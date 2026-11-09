module
public import FormalProof4FHE.HasteBoots.NativeRecordValues
public import FormalProof4FHE.HasteBoots.NativeZstReference
public import FormalProof4FHE.HasteBoots.NativeRawVecReference
public import FormalProof4FHE.HasteBoots.NativeByteDropCalls
@[expose] public section

/-! Finite typed aggregate bodies over the shared reference/byte heap.
Native layout, ABI, compiler and lifetime correspondence remain unproved. -/
namespace FormalProof4FHE.HasteBoots.NativeRecordLLBC
open NativeRecordValues (Ty Value Path)
open NativeReferenceMachine (State)
open NativeSliceLLBC (Element)
open NativeWord64Memory (Word)
open NativeByteDropCalls (Classification)

inductive Slot where
  | dead
  | live (value : Option Value)
  deriving DecidableEq

structure Frame where
  types : List Ty
  slots : List Slot
  world : State
  deriving DecidableEq

inductive Operand where
  | copy (index : Nat) (path : Path := [])
  | move (index : Nat) (path : Path := [])
  | usize (value : Word)
  | unit
  deriving DecidableEq

inductive Input where
  | vectorSharedReference (index : Nat)
  | rawVecSharedReference (index : Nat)
  | zstSharedReference (index : Nat)
  | unit
  | scalar (value : NativeSliceLLBC.Input)
  | choice (right : Bool) (fields : Input)
  | pair (left right : Input)
  | record (tag : Nat) (fields : Input)
  | enumeration (tag : Nat) (value : Word)
  deriving DecidableEq

def decode (world : State) : Input → Option Value
  | .vectorSharedReference index => (NativeRawVecReference.decode world index .vector).map Value.scalar
  | .rawVecSharedReference index => (NativeRawVecReference.decode world index).map Value.scalar
  | .zstSharedReference index => (NativeZstReference.decode world index).map Value.scalar
  | .unit => some (.scalar .unit)
  | .scalar value => (NativeSliceLLBC.decodeInput world value).map Value.scalar
  | .pair left right => do return .pair (← decode world left) (← decode world right)
  | .record tag fields => (decode world fields).map (.record tag)
  | .choice side fields => (decode world fields).map (.choice side)
  | .enumeration tag value => some (.enumeration tag value)

def read (frame : Frame) (index : Nat) (path : Path) : Option Value := do
  let type ← frame.types[index]?
  let selectedType ← NativeRecordValues.typeAt type path
  let .live (some value) ← frame.slots[index]? | none
  let selected ← NativeRecordValues.get value path
  if NativeRecordValues.fits selectedType selected then some selected else none

def selectChoice (frame : Frame) (index : Nat) (path : Path) (tag : Nat) : Option Bool := do
  let type ← frame.types[index]?
  let .record actual (.choice _ _) ← NativeRecordValues.typeAt type path | none
  if actual ≠ tag then none else do
    let .live (some value) ← frame.slots[index]? | none
    NativeRecordValues.sideAt value path tag

def write (frame : Frame) (index : Nat) (value : Value) : Option Frame :=
  frame.types[index]?.bind (fun type =>
    if NativeRecordValues.fits type value then
      frame.slots[index]?.bind (fun slot => match slot with
        | .live _ => some {frame with slots := frame.slots.set index (.live (some value))}
        | .dead => none)
    else none)

def storageLive (frame : Frame) (index : Nat) : Option Frame :=
  frame.slots[index]?.map (fun _ => {frame with slots := frame.slots.set index (.live none)})

def storageDead (frame : Frame) (index : Nat) : Option Frame :=
  frame.slots[index]?.map (fun _ => {frame with slots := frame.slots.set index .dead})

def evalOperand (frame : Frame) : Operand → Option (Value × Frame)
  | .unit => some (.scalar .unit, frame)
  | .usize value => some (.scalar (.usize value), frame)
  | .copy index path => do
    let type ← frame.types[index]?
    let selectedType ← NativeRecordValues.typeAt type path
    if NativeRecordValues.copyable selectedType then return (← read frame index path, frame) else none
  | .move index path => do
    let selected ← read frame index path
    let .live (some value) ← frame.slots[index]? | none
    let changed ← NativeRecordValues.replace value path .uninit
    pure (selected, {frame with slots := frame.slots.set index (.live (some changed))})

def evalArgs (frame : Frame) : List Operand → Option (List Value × Frame)
  | [] => some ([],frame)
  | arg :: tail => do
    let (value,changed) ← evalOperand frame arg
    let (values,final) ← evalArgs changed tail
    pure (value :: values,final)

def initial (types : List Ty) (argCount : Nat) (args : List Value) (world : State) : Option Frame :=
  if args.length = argCount ∧ argCount + 1 ≤ types.length ∧
      ((types.drop 1 |>.take argCount).zip args).all (fun (type,value) => NativeRecordValues.fits type value) then
    some ⟨types, .dead :: (args.map (fun value => .live (some value))) ++
      List.replicate (types.length - argCount - 1) .dead, world⟩
  else none

inductive Tagged where
  | value (value : Value) (world : State)
  | invalid (world : State)
  deriving DecidableEq

def Tagged.world : Tagged → State
  | .value _ world | .invalid world => world

/-- Aggregate retags execute in field order and retain a failed prefix. -/
def retag (world : State) : Value → Bool → Element → Tagged
  | value, false, _ => .value value world
  | .scalar value, true, element =>
    match NativeSliceLLBC.retagValue ⟨[],[],world⟩ value true element with
    | none => .invalid world
    | some (value,frame) => .value (.scalar value) frame.world
  | .pair left right, true, element => match retag world left true element with
    | .invalid world => .invalid world
    | .value first middle => match retag middle right true element with
      | .invalid world => .invalid world
      | .value second final => .value (.pair first second) final
  | .choice side fields, true, element => match retag world fields true element with
    | .invalid world => .invalid world
    | .value changed final => .value (.choice side changed) final
  | .record tag fields, true, element => match retag world fields true element with
    | .invalid world => .invalid world
    | .value changed final => .value (.record tag changed) final
  | .enumeration tag value, true, _ => .value (.enumeration tag value) world
  | .uninit, true, _ => .invalid world

inductive Rvalue where
  | unit
  | recordResult (tag : Nat) (singleton : Bool) (inner : Rvalue)
  | mulUsizeUB (left right : Operand)
  | enumWord (value : Operand) (tag : Nat)
  | rawVecField (action : NativeRawVecReference.Action) (reference : Operand) (enabled : Bool := false)
  | aggregate (tag : Option Nat) (side : Option Bool) (fields : List Operand)
  | use (value : Operand) (enabled : Bool) (element : Element := .byte)
  | rawCast (value : Operand)
  | choice (right : Bool) (value : Operand)
  | wrapOne (tag : Nat) (value : Operand)
  | pair (left right : Operand)
  deriving DecidableEq

inductive Evaluated where
  | value (value : Value) (frame : Frame)
  | invalid (world : State)
  deriving DecidableEq

def Evaluated.world : Evaluated → State
  | .value _ frame => frame.world
  | .invalid world => world

def evalRawVecField (frame : Frame) (operand : Operand) (action : NativeRawVecReference.Action) (enabled : Bool := false) : Evaluated :=
  match evalOperand frame operand with
  | none => .invalid frame.world
  | some (value,caller) => match value with
    | .scalar value => match NativeRawVecReference.eval caller.world value action with
      | .invalid next => .invalid next
      | .value output next => match retag next (.scalar output) enabled .word with
        | .invalid final => .invalid final
        | .value tagged final => .value tagged {caller with world := final}
    | _ => .invalid caller.world

def multiplyWords : List Value → Option Value
  | [.scalar (.usize left), .scalar (.usize right)] =>
    if bounded : left.val * right.val < 2^64 then some (.scalar (.usize ⟨left.val * right.val, bounded⟩)) else none
  | _ => none

def evalMultiply (frame : Frame) (left right : Operand) : Evaluated :=
  match evalArgs frame [left,right] with
  | none => .invalid frame.world
  | some (values,caller) => match multiplyWords values with
    | none => .invalid caller.world
    | some value => .value value caller

def enumWordValue (tag : Nat) : Value → Option Value
  | .enumeration actual value => if tag = actual then some (.scalar (.usize value)) else none
  | _ => none

def evalEnumWord (frame : Frame) (operand : Operand) (tag : Nat) : Evaluated :=
  match evalOperand frame operand with
  | none => .invalid frame.world
  | some (value,caller) => match enumWordValue tag value with
    | none => .invalid caller.world
    | some value => .value value caller

def recordResultValue (tag : Nat) (singleton : Bool) (value : Value) : Option Value :=
  if singleton then some (.record tag (.pair value (.scalar .unit))) else
    match value with | .scalar .unit => some (.record tag (.scalar .unit)) | _ => none

def evalRvalue (frame : Frame) : Rvalue → Evaluated
  | .unit => .value (.scalar .unit) frame
  | .recordResult tag singleton inner => match evalRvalue frame inner with
    | .invalid world => .invalid world
    | .value value caller => match recordResultValue tag singleton value with
      | none => .invalid caller.world
      | some output => .value output caller
  | .mulUsizeUB left right => evalMultiply frame left right
  | .enumWord operand tag => evalEnumWord frame operand tag
  | .rawVecField action operand enabled => evalRawVecField frame operand action enabled
  | .aggregate tag side fields => match evalArgs frame fields with
    | none => .invalid frame.world
    | some (values,caller) =>
      let tree := values.foldr Value.pair (.scalar .unit)
      let payload := match side with | none => tree | some side => .choice side tree
      .value (match tag with | none => payload | some tag => .record tag payload) caller
  | .use operand enabled element => match evalOperand frame operand with
    | none => .invalid frame.world
    | some (value,caller) => match retag caller.world value enabled element with
      | .invalid world => .invalid world
      | .value changed world => .value changed {caller with world}
  | .rawCast operand => match evalOperand frame operand with
    | none => .invalid frame.world
    | some (value,caller) => match value with
      | .scalar (.raw pointer) =>
        if pointer.length = none then .value (.scalar (.raw pointer)) caller else .invalid caller.world
      | _ => .invalid caller.world
  | .choice side operand => match evalOperand frame operand with
    | none => .invalid frame.world
    | some (value,caller) => .value (.choice side value) caller
  | .wrapOne tag operand => match evalOperand frame operand with
    | none => .invalid frame.world
    | some (value,caller) => .value (.record tag (.pair value (.scalar .unit))) caller
  | .pair left right => match evalArgs frame [left,right] with
    | none => .invalid frame.world
    | some (values,caller) => match values with
      | [first,second] => .value (.pair first second) caller
      | _ => .invalid caller.world

inductive Flow where
  | normal (frame : Frame)
  | returned (value : Value) (world : State)
  | unwind (world : State)
  | invalid (world : State)
  | unsupported (source : String) (world : State)
  deriving DecidableEq

def Flow.world : Flow → State
  | .normal frame => frame.world
  | .returned _ world | .unwind world | .invalid world | .unsupported _ world => world

/-- As in the earlier caller model, normal unit cleanup is explicit ghost
composition, not a statement about Rust region erasure or lifetime endings. -/
def settle (entered : State) : Flow → Flow
  | .returned (.scalar .unit) world =>
    match NativeReferenceCleanup.settleUnit entered (.returned .unit world) with
    | .returned .unit changed => .returned (.scalar .unit) changed
    | flow => .invalid flow.world
  | flow => flow

/-- Logical marshalled external deallocation with an explicit enum identity. -/
def deallocate (frame : Frame) (pointer size alignment : Operand) (enumTag : Nat) : Flow :=
  match evalArgs frame [pointer,size,alignment] with
  | none => .invalid frame.world
  | some (values,caller) => match values with
    | [.scalar (.raw pointer),.scalar (.usize size),.enumeration tag alignment] =>
      if tag = enumTag then match NativeByteDeallocation.execute caller.world pointer size alignment with
        | none => .invalid caller.world
        | some world => .returned (.scalar .unit) world
      else .invalid caller.world
    | _ => .invalid caller.world

inductive Body where
  | done
  | ret
  | resume
  | abort
  | unsupported (source : String)
  | live (index : Nat) (next : Body)
  | dead (index : Nat) (next : Body)
  | assign (index : Nat) (value : Rvalue) (next : Body)
  | constIf (condition : Bool) (yes no next : Body)
  | matchChoice (index : Nat) (path : Path) (tag : Nat) (left right next : Body)
  | switchUsize (test : Operand) (value : Word) (yes no next : Body)
  | deallocate (pointer size alignment : Operand) (enumTag : Nat)
  | call (name : String) (classification : Classification) (types : List Ty) (argCount target : Nat)
      (args : List Operand) (callee unwind next : Body)
  deriving DecidableEq

structure Function where
  name : String
  classification : Classification
  types : List Ty
  argCount : Nat
  body : Body
  deriving DecidableEq

def eval : Body → Frame → Flow
  | .done, frame => .normal frame
  | .ret, frame => match read frame 0 [] with | none => .invalid frame.world | some value => .returned value frame.world
  | .resume, frame => .unwind frame.world
  | .abort, frame => .invalid frame.world
  | .unsupported source, frame => .unsupported source frame.world
  | .live index next, frame => match storageLive frame index with
    | none => .invalid frame.world | some changed => eval next changed
  | .dead index next, frame => match storageDead frame index with
    | none => .invalid frame.world | some changed => eval next changed
  | .assign index value next, frame => match evalRvalue frame value with
    | .invalid world => .invalid world
    | .value output changed => match write changed index output with
      | none => .invalid changed.world | some written => eval next written
  | .constIf condition yes no next, frame =>
    let branch := if condition then eval yes frame else eval no frame
    match branch with | .normal changed => eval next changed | flow => flow
  | .matchChoice index path tag left right next, frame => match selectChoice frame index path tag with
    | none => .invalid frame.world
    | some side =>
      let branch := if side then eval right frame else eval left frame
      match branch with | .normal changed => eval next changed | flow => flow
  | .switchUsize operand value yes no next, frame => match evalOperand frame operand with
    | some (.scalar (.usize word),caller) =>
      let branch := if word = value then eval yes caller else eval no caller
      match branch with | .normal changed => eval next changed | flow => flow
    | _ => .invalid frame.world
  | .deallocate pointer size alignment tag, frame => deallocate frame pointer size alignment tag
  | .call _ _ types argCount target args callee unwind next, frame => match evalArgs frame args with
    | none => .invalid frame.world
    | some (values,caller) => match initial types argCount values caller.world with
      | none => .invalid caller.world
      | some entered => match settle entered.world (eval callee entered) with
        | .returned value world => match write {caller with world} target value with
          | none => .invalid world | some changed => eval next changed
        | .unwind world => eval unwind {caller with world}
        | .invalid world => .invalid world
        | .unsupported source world => .unsupported source world
        | .normal changed => .invalid changed.world

def decodeArgs (world : State) : List Input → Option (List Value)
  | [] => some []
  | arg :: tail => do return (← decode world arg) :: (← decodeArgs world tail)

def invoke (function : Function) (world : State) (args : List Input) : Flow :=
  match decodeArgs world args with
  | none => .invalid world
  | some values => match initial function.types function.argCount values world with
    | none => .invalid world
    | some frame => settle world (eval function.body frame)


theorem write_world (frame changed : Frame) (index : Nat) (value : Value)
    (written : write frame index value = some changed) : changed.world = frame.world := by
  simp only [write, Option.bind_eq_some_iff] at written
  obtain ⟨type, _, actual⟩ := written
  split at actual
  · simp only [Option.bind_eq_some_iff] at actual
    obtain ⟨slot, _, actual⟩ := actual
    cases slot with
    | dead => cases actual
    | live previous => cases actual; rfl
  · cases actual

theorem storageLive_world (frame changed : Frame) (index : Nat)
    (written : storageLive frame index = some changed) : changed.world = frame.world := by
  obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp written
  cases same
  rfl

theorem storageDead_world (frame changed : Frame) (index : Nat)
    (written : storageDead frame index = some changed) : changed.world = frame.world := by
  obtain ⟨_, _, same⟩ := Option.map_eq_some_iff.mp written
  cases same
  rfl

theorem evalOperand_world (frame changed : Frame) (operand : Operand) (value : Value)
    (evaluated : evalOperand frame operand = some (value,changed)) : changed.world = frame.world := by
  cases operand with
  | unit => cases evaluated; rfl
  | usize word => cases evaluated; rfl
  | copy index path =>
    simp only [evalOperand, Option.bind_eq_bind', Option.bind_eq_some_iff] at evaluated
    obtain ⟨type, _, selectedType, _, actual⟩ := evaluated
    split at actual
    · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at actual
      obtain ⟨_, _, same⟩ := actual
      cases same
      rfl
    · cases actual
  | move index path =>
    simp only [evalOperand, Option.bind_eq_bind', Option.bind_eq_some_iff] at evaluated
    obtain ⟨_, _, slot, _, actual⟩ := evaluated
    cases slot with
    | dead => cases actual
    | live previous =>
      cases previous with
      | none => cases actual
      | some stored =>
        simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at actual
        obtain ⟨_, _, same⟩ := actual
        cases same
        rfl

theorem evalArgs_world (frame changed : Frame) (args : List Operand) (values : List Value)
    (evaluated : evalArgs frame args = some (values,changed)) : changed.world = frame.world := by
  induction args generalizing frame values with
  | nil => cases evaluated; rfl
  | cons arg tail ih =>
    simp only [evalArgs, Option.bind_eq_bind', Option.bind_eq_some_iff, pure, Option.some.injEq] at evaluated
    obtain ⟨⟨value,middle⟩, first, ⟨later,final⟩, rest, same⟩ := evaluated
    cases same
    exact (ih middle later rest).trans (evalOperand_world frame middle arg value first)

theorem initial_world (types : List Ty) (argCount : Nat) (args : List Value) (world : State) (frame : Frame)
    (initialized : initial types argCount args world = some frame) : frame.world = world := by
  simp only [initial] at initialized
  split at initialized
  · cases initialized; rfl
  · cases initialized

theorem retag_projects (world : State) (value : Value) (enabled : Bool) (element : Element) :
    NativeReferenceMachine.Runs world (retag world value enabled element).world := by
  induction value generalizing world with
  | scalar value =>
    cases enabled with
    | false => exact .refl _
    | true =>
      cases actual : NativeSliceLLBC.retagValue ⟨[],[],world⟩ value true element with
      | none => simp only [retag, actual, Tagged.world]; exact .refl _
      | some result =>
        rcases result with ⟨output,frame⟩
        simpa only [retag, actual, Tagged.world] using
          NativeSliceLLBC.retagValue_projects ⟨[],[],world⟩ frame value output true element actual
  | pair left right leftIH rightIH =>
    cases enabled with
    | false => exact .refl _
    | true =>
      have first := leftIH world
      cases firstEq : retag world left true element with
      | invalid rejected => simpa only [retag, firstEq, Tagged.world] using first
      | value value middle =>
        have second := rightIH middle
        rw [firstEq] at first
        cases secondEq : retag middle right true element with
        | invalid rejected =>
          rw [secondEq] at second
          simp only [retag, firstEq, secondEq, Tagged.world]
          exact NativeReferenceMachine.runs_trans _ _ _ first second
        | value output final =>
          rw [secondEq] at second
          simp only [retag, firstEq, secondEq, Tagged.world]
          exact NativeReferenceMachine.runs_trans _ _ _ first second
  | choice side fields ih =>
    cases enabled with
    | false => exact .refl _
    | true =>
      have first := ih world
      cases actual : retag world fields true element with
      | invalid rejected => simpa only [retag, actual, Tagged.world] using first
      | value output final => simpa only [retag, actual, Tagged.world] using first
  | record tag fields ih =>
    cases enabled with
    | false => exact .refl _
    | true =>
      have first := ih world
      cases actual : retag world fields true element with
      | invalid rejected => simpa only [retag, actual, Tagged.world] using first
      | value output final => simpa only [retag, actual, Tagged.world] using first
  | enumeration tag value => cases enabled <;> exact .refl _
  | uninit => cases enabled <;> exact .refl _

theorem evalRawVecField_projects (frame : Frame) (operand : Operand) (action : NativeRawVecReference.Action) (enabled : Bool) :
    NativeReferenceMachine.Runs frame.world (evalRawVecField frame operand action enabled).world := by
  cases selected : evalOperand frame operand with
  | none => simp only [evalRawVecField, selected, Evaluated.world]; exact .refl _
  | some result =>
    rcases result with ⟨value,caller⟩
    have same := evalOperand_world frame caller operand value selected
    cases value with
    | scalar value =>
      have first := NativeRawVecReference.eval_projects caller.world value action
      cases actual : NativeRawVecReference.eval caller.world value action with
      | invalid rejected =>
        rw [actual] at first
        simp only [evalRawVecField, selected, actual, Evaluated.world]
        simpa only [NativeRawVecFields.Result.world, same] using first
      | value output next =>
        rw [actual] at first
        have readPrefix : NativeReferenceMachine.Runs frame.world next := by
          simpa only [NativeRawVecFields.Result.world, same] using first
        have second := retag_projects next (.scalar output) enabled .word
        cases tagged : retag next (.scalar output) enabled .word with
        | invalid final =>
          rw [tagged] at second
          simp only [evalRawVecField, selected, actual, tagged, Evaluated.world]
          exact NativeReferenceMachine.runs_trans _ _ _ readPrefix second
        | value result final =>
          rw [tagged] at second
          simp only [evalRawVecField, selected, actual, tagged, Evaluated.world]
          exact NativeReferenceMachine.runs_trans _ _ _ readPrefix second
    | choice side fields => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | pair left right => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | record tag fields => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | enumeration tag value => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _
    | uninit => simp only [evalRawVecField, selected, Evaluated.world]; rw [same]; exact .refl _

theorem multiplyWords_no_wrap (left right result : Word)
    (computed : multiplyWords [.scalar (.usize left), .scalar (.usize right)] = some (.scalar (.usize result))) :
    result.val = left.val * right.val := by
  simp only [multiplyWords] at computed
  split at computed
  next bounded => cases computed; rfl
  next => cases computed

theorem multiplyWords_overflow (left right : Word) (overflow : ¬ left.val * right.val < 2^64) :
    multiplyWords [.scalar (.usize left), .scalar (.usize right)] = none := by
  simp only [multiplyWords, overflow, dite_false]

theorem enumWordValue_exact (tag : Nat) (value : Word) :
    enumWordValue tag (.enumeration tag value) = some (.scalar (.usize value)) := by
  simp only [enumWordValue, ite_true]

theorem evalMultiply_world (frame : Frame) (left right : Operand) :
    (evalMultiply frame left right).world = frame.world := by
  cases selected : evalArgs frame [left,right] with
  | none => simp only [evalMultiply, selected, Evaluated.world]
  | some result =>
    rcases result with ⟨values,caller⟩
    have same := evalArgs_world frame caller [left,right] values selected
    cases actual : multiplyWords values <;> simpa only [evalMultiply, selected, actual, Evaluated.world] using same

theorem evalEnumWord_world (frame : Frame) (operand : Operand) (tag : Nat) :
    (evalEnumWord frame operand tag).world = frame.world := by
  cases selected : evalOperand frame operand with
  | none => simp only [evalEnumWord, selected, Evaluated.world]
  | some result =>
    rcases result with ⟨value,caller⟩
    have same := evalOperand_world frame caller operand value selected
    cases actual : enumWordValue tag value <;> simpa only [evalEnumWord, selected, actual, Evaluated.world] using same

theorem evalRvalue_projects (frame : Frame) (rvalue : Rvalue) :
    NativeReferenceMachine.Runs frame.world (evalRvalue frame rvalue).world := by
  induction rvalue with
  | unit => exact .refl _
  | mulUsizeUB left right =>
    change NativeReferenceMachine.Runs frame.world (evalMultiply frame left right).world
    rw [evalMultiply_world]; exact .refl _
  | enumWord operand tag =>
    change NativeReferenceMachine.Runs frame.world (evalEnumWord frame operand tag).world
    rw [evalEnumWord_world]; exact .refl _
  | recordResult tag singleton inner ih =>
    cases selected : evalRvalue frame inner with
    | invalid world => simpa only [evalRvalue, selected, Evaluated.world] using ih
    | value value caller =>
      cases actual : recordResultValue tag singleton value <;>
        simpa only [evalRvalue, selected, actual, Evaluated.world] using ih
  | rawVecField action operand enabled => exact evalRawVecField_projects frame operand action enabled
  | aggregate tag side fields =>
    cases selected : evalArgs frame fields with
    | none => simp only [evalRvalue, selected, Evaluated.world]; exact .refl _
    | some result =>
      rcases result with ⟨values,caller⟩
      simp only [evalRvalue, selected, Evaluated.world]
      rw [evalArgs_world frame caller fields values selected]
      exact .refl _
  | use operand enabled element =>
    cases selected : evalOperand frame operand with
    | none => simp only [evalRvalue, selected, Evaluated.world]; exact .refl _
    | some result =>
      rcases result with ⟨value,caller⟩
      have same := evalOperand_world frame caller operand value selected
      have first := retag_projects caller.world value enabled element
      cases actual : retag caller.world value enabled element with
      | invalid rejected =>
        rw [actual] at first
        simp only [evalRvalue, selected, actual, Evaluated.world]
        simpa only [same, Tagged.world] using first
      | value output world =>
        rw [actual] at first
        simp only [evalRvalue, selected, actual, Evaluated.world]
        simpa only [same, Tagged.world] using first
  | choice side operand =>
    cases selected : evalOperand frame operand with
    | none => simp only [evalRvalue, selected, Evaluated.world]; exact .refl _
    | some result =>
      rcases result with ⟨value,caller⟩
      simp only [evalRvalue, selected, Evaluated.world]
      rw [evalOperand_world frame caller operand value selected]
      exact .refl _
  | wrapOne tag operand =>
    cases selected : evalOperand frame operand with
    | none => simp only [evalRvalue, selected, Evaluated.world]; exact .refl _
    | some result =>
      rcases result with ⟨value,caller⟩
      simp only [evalRvalue, selected, Evaluated.world]
      rw [evalOperand_world frame caller operand value selected]
      exact .refl _
  | rawCast operand =>
    cases selected : evalOperand frame operand with
    | none => simp only [evalRvalue, selected, Evaluated.world]; exact .refl _
    | some result =>
      rcases result with ⟨value,caller⟩
      have same := evalOperand_world frame caller operand value selected
      cases value with
      | scalar value =>
        cases value with
        | raw pointer =>
          by_cases thin : pointer.length = none
          · simp only [evalRvalue, selected, thin, ite_true, Evaluated.world]
            rw [same]; exact .refl _
          · simp only [evalRvalue, selected, thin, ite_false, Evaluated.world]
            rw [same]; exact .refl _
        | unit => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
        | usize word => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
        | reference mutable reference length => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
      | pair left right => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
      | choice side fields => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
      | record tag fields => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
      | enumeration tag value => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
      | uninit => simp only [evalRvalue, selected, Evaluated.world]; rw [same]; exact .refl _
  | pair left right =>
    cases selected : evalArgs frame [left,right] with
    | none => simp only [evalRvalue, selected, Evaluated.world]; exact .refl _
    | some result =>
      rcases result with ⟨values,caller⟩
      have same := evalArgs_world frame caller [left,right] values selected
      simp only [evalRvalue, selected]
      split
      · change NativeReferenceMachine.Runs frame.world caller.world
        rw [same]; exact .refl _
      · change NativeReferenceMachine.Runs frame.world caller.world
        rw [same]; exact .refl _


theorem settle_projects (entered : State) (flow : Flow) :
    NativeReferenceMachine.Runs flow.world (settle entered flow).world := by
  cases flow with
  | normal frame => exact .refl _
  | unwind world => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _
  | returned value world =>
    cases value with
    | pair left right => exact .refl _
    | choice side fields => exact .refl _
    | record tag fields => exact .refl _
    | enumeration tag value => exact .refl _
    | uninit => exact .refl _
    | scalar value =>
      cases value with
      | usize value => exact .refl _
      | raw pointer => exact .refl _
      | reference mutable reference length => exact .refl _
      | unit =>
        have first := NativeReferenceCleanup.settleUnit_projects entered (.returned .unit world)
        cases actual : NativeReferenceCleanup.settleUnit entered (.returned .unit world) with
        | returned value final =>
          cases value <;> simpa only [settle, actual, NativeSliceLLBC.Flow.world, Flow.world] using first
        | continued frame => simpa only [settle, actual, NativeSliceLLBC.Flow.world, Flow.world] using first
        | unwind final => simpa only [settle, actual, NativeSliceLLBC.Flow.world, Flow.world] using first
        | invalid final => simpa only [settle, actual, NativeSliceLLBC.Flow.world, Flow.world] using first
        | unsupported source final => simpa only [settle, actual, NativeSliceLLBC.Flow.world, Flow.world] using first

theorem deallocate_projects (frame : Frame) (pointer size alignment : Operand) (tag : Nat) :
    NativeReferenceMachine.Runs frame.world (deallocate frame pointer size alignment tag).world := by
  cases selected : evalArgs frame [pointer,size,alignment] with
  | none => simp only [deallocate, selected, Flow.world]; exact .refl _
  | some result =>
    rcases result with ⟨values,caller⟩
    have same := evalArgs_world frame caller [pointer,size,alignment] values selected
    simp only [deallocate, selected]
    split
    next raw bytes actual align =>
      by_cases matched : actual = tag
      · simp only [matched, ite_true]
        cases freed : NativeByteDeallocation.execute caller.world raw bytes align with
        | none => simp only [Flow.world]; rw [same]; exact .refl _
        | some world =>
          have first := NativeByteDeallocation.execute_projects caller.world world raw bytes align freed
          simpa only [Flow.world, same] using first
      · simp only [matched, ite_false, Flow.world]; rw [same]; exact .refl _
    next => change NativeReferenceMachine.Runs frame.world caller.world; rw [same]; exact .refl _

theorem eval_projects (body : Body) (frame : Frame) :
    NativeReferenceMachine.Runs frame.world (eval body frame).world := by
  induction body generalizing frame with
  | done => exact .refl _
  | ret =>
    cases selected : read frame 0 [] <;> simp only [eval, selected, Flow.world] <;> exact .refl _
  | resume => exact .refl _
  | abort => exact .refl _
  | unsupported source => exact .refl _
  | live index next ih =>
    cases changed : storageLive frame index with
    | none => simp only [eval, changed, Flow.world]; exact .refl _
    | some caller =>
      simp only [eval, changed]
      have first := ih caller
      simpa only [storageLive_world frame caller index changed] using first
  | dead index next ih =>
    cases changed : storageDead frame index with
    | none => simp only [eval, changed, Flow.world]; exact .refl _
    | some caller =>
      simp only [eval, changed]
      have first := ih caller
      simpa only [storageDead_world frame caller index changed] using first
  | assign index rvalue next ih =>
    have first := evalRvalue_projects frame rvalue
    cases actual : evalRvalue frame rvalue with
    | invalid world => simpa only [eval, actual, Evaluated.world, Flow.world] using first
    | value value caller =>
      rw [actual] at first
      cases written : write caller index value with
      | none => simpa only [eval, actual, written, Evaluated.world, Flow.world] using first
      | some changed =>
        simp only [eval, actual, written]
        have second := ih changed
        rw [write_world caller changed index value written] at second
        exact NativeReferenceMachine.runs_trans _ _ _ first second
  | constIf condition yes no next yesIH noIH nextIH =>
    have first : NativeReferenceMachine.Runs frame.world
        (if condition then eval yes frame else eval no frame).world := by
      cases condition
      · exact noIH frame
      · exact yesIH frame
    simp only [eval]
    generalize chosen : (if condition then eval yes frame else eval no frame) = branch at first ⊢
    cases branch with
    | normal changed => exact NativeReferenceMachine.runs_trans _ _ _ first (nextIH changed)
    | returned value world => exact first
    | unwind world => exact first
    | invalid world => exact first
    | unsupported source world => exact first
  | matchChoice index path tag left right next leftIH rightIH nextIH =>
    cases selected : selectChoice frame index path tag with
    | none => simp only [eval, selected, Flow.world]; exact .refl _
    | some side =>
      have first : NativeReferenceMachine.Runs frame.world
          (if side then eval right frame else eval left frame).world := by
        cases side
        · exact leftIH frame
        · exact rightIH frame
      simp only [eval, selected]
      generalize chosen : (if side then eval right frame else eval left frame) = branch at first ⊢
      cases branch with
      | normal changed => exact NativeReferenceMachine.runs_trans _ _ _ first (nextIH changed)
      | returned value world => exact first
      | unwind world => exact first
      | invalid world => exact first
      | unsupported source world => exact first
  | switchUsize operand expected yes no next yesIH noIH nextIH =>
    cases selected : evalOperand frame operand with
    | none => simp only [eval, selected, Flow.world]; exact .refl _
    | some result =>
      rcases result with ⟨value,caller⟩
      have same := evalOperand_world frame caller operand value selected
      cases value with
      | pair left right => simp only [eval, selected, Flow.world]; exact .refl _
      | choice side fields => simp only [eval, selected, Flow.world]; exact .refl _
      | record tag fields => simp only [eval, selected, Flow.world]; exact .refl _
      | enumeration tag value => simp only [eval, selected, Flow.world]; exact .refl _
      | uninit => simp only [eval, selected, Flow.world]; exact .refl _
      | scalar value =>
        cases value with
        | unit => simp only [eval, selected, Flow.world]; exact .refl _
        | raw pointer => simp only [eval, selected, Flow.world]; exact .refl _
        | reference mutable reference length => simp only [eval, selected, Flow.world]; exact .refl _
        | usize word =>
          have first : NativeReferenceMachine.Runs frame.world
              (if word = expected then eval yes caller else eval no caller).world := by
            rw [← same]
            split
            · exact yesIH caller
            · exact noIH caller
          simp only [eval, selected]
          generalize chosen : (if word = expected then eval yes caller else eval no caller) = branch at first ⊢
          cases branch with
          | normal changed => exact NativeReferenceMachine.runs_trans _ _ _ first (nextIH changed)
          | returned value world => exact first
          | unwind world => exact first
          | invalid world => exact first
          | unsupported source world => exact first
  | deallocate pointer size alignment tag => exact deallocate_projects frame pointer size alignment tag
  | call name classification types argCount target args callee unwind next calleeIH unwindIH nextIH =>
    cases selected : evalArgs frame args with
    | none => simp only [eval, selected, Flow.world]; exact .refl _
    | some result =>
      rcases result with ⟨values,caller⟩
      have same := evalArgs_world frame caller args values selected
      cases initialized : initial types argCount values caller.world with
      | none => simp only [eval, selected, initialized, Flow.world]; rw [same]; exact .refl _
      | some entered =>
        have entryWorld := initial_world types argCount values caller.world entered initialized
        have callPrefix : NativeReferenceMachine.Runs frame.world entered.world := by
          rw [entryWorld, same]
          exact .refl _
        have first := NativeReferenceMachine.runs_trans _ _ _ callPrefix
          (NativeReferenceMachine.runs_trans _ _ _ (calleeIH entered)
            (settle_projects entered.world (eval callee entered)))
        cases returned : settle entered.world (eval callee entered) with
        | normal changed => simpa only [eval, selected, initialized, returned, Flow.world] using first
        | invalid world => simpa only [eval, selected, initialized, returned, Flow.world] using first
        | unsupported source world => simpa only [eval, selected, initialized, returned, Flow.world] using first
        | unwind world =>
          rw [returned] at first
          simp only [eval, selected, initialized, returned]
          exact NativeReferenceMachine.runs_trans _ _ _ first (unwindIH {caller with world})
        | returned output world =>
          rw [returned] at first
          cases written : write {caller with world} target output with
          | none => simpa only [eval, selected, initialized, returned, written, Flow.world] using first
          | some changed =>
            have second := nextIH changed
            rw [write_world {caller with world} changed target output written] at second
            simp only [eval, selected, initialized, returned, written]
            exact NativeReferenceMachine.runs_trans _ _ _ first second

theorem invoke_projects (function : Function) (world : State) (args : List Input) :
    NativeReferenceMachine.Runs world (invoke function world args).world := by
  cases decoded : decodeArgs world args with
  | none => simp only [invoke, decoded, Flow.world]; exact .refl _
  | some values =>
    cases initialized : initial function.types function.argCount values world with
    | none => simp only [invoke, decoded, initialized, Flow.world]; exact .refl _
    | some frame =>
      have same := initial_world function.types function.argCount values world frame initialized
      have first := NativeReferenceMachine.runs_trans _ _ _ (eval_projects function.body frame)
        (settle_projects world (eval function.body frame))
      simpa only [invoke, decoded, initialized, same] using first

theorem invoke_reachable (function : Function) (world : State) (args : List Input)
    (reachable : NativeReferenceMachine.Reachable world) :
    NativeReferenceMachine.Reachable (invoke function world args).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (invoke_projects function world args)

end FormalProof4FHE.HasteBoots.NativeRecordLLBC
