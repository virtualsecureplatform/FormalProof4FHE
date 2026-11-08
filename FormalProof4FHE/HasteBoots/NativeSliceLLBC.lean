module
public import FormalProof4FHE.HasteBoots.NativeReferenceMachine
@[expose] public section

/-! Slice-constructor body semantics over the closed reference machine.
Unsupported source fragments halt explicitly. Lifetimes and Rust alias semantics
are not refined by this model. Local storage death does not end ledger leases. -/
namespace FormalProof4FHE.HasteBoots.NativeSliceLLBC
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeReferenceMachine (State Reference)

inductive Element where
  | byte
  | word
  deriving DecidableEq

def Element.width : Element → Nat
  | .byte => 1
  | .word => 8

inductive Ty where
  | unit
  | usize
  | raw (slice : Bool)
  | reference (mutable : Bool)
  deriving DecidableEq

structure Raw where
  storage : Pointer
  length : Option Word
  deriving DecidableEq

inductive Value where
  | unit
  | usize (word : Word)
  | raw (pointer : Raw)
  | reference (mutable : Bool) (value : Reference) (length : Word)
  deriving DecidableEq

inductive Input where
  | usize (word : Word)
  | rawRegister (index : Nat)
  deriving DecidableEq

def decodeInput (world : State) : Input → Option Value
  | .usize word => some (.usize word)
  | .rawRegister index => world.pointers.registers[index]?.map (fun pointer => .raw ⟨pointer, none⟩)

def fits : Ty → Value → Bool
  | .unit, .unit | .usize, .usize _ => true
  | .raw slice, .raw pointer => slice == pointer.length.isSome
  | .reference mutable, .reference actual _ _ => mutable == actual
  | _, _ => false

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
  | copy (index : Nat)
  | move (index : Nat)
  deriving DecidableEq

inductive Rvalue where
  | use (value : Operand) (retag : Bool := true) (element : Element := .word)
  | rawCast (value : Operand)
  | borrow (mutable : Bool) (base : Nat) (element : Element := .word)
  | unit
  deriving DecidableEq

inductive Body where
  | done
  | ret
  | resume
  | abort
  | unsupported (source : String) (next : Body)
  | storageLive (index : Nat) (next : Body)
  | storageDead (index : Nat) (next : Body)
  | assign (target : Nat) (value : Rvalue) (next : Body)
  | parts (target : Nat) (data length : Operand) (unwind next : Body)
  | constIf (condition : Bool) (yes no next : Body)
  | call (name : String) (types : List Ty) (argCount target : Nat)
      (args : List Operand) (callee unwind next : Body)
  deriving DecidableEq

structure Function where
  name : String
  types : List Ty
  argCount : Nat
  body : Body
  deriving DecidableEq

inductive Flow where
  | continued (frame : Frame)
  | returned (value : Value) (world : State)
  | unwind (world : State)
  | invalid (world : State)
  | unsupported (source : String) (world : State)
  deriving DecidableEq

def Flow.world : Flow → State
  | .continued frame => frame.world
  | .returned _ world | .unwind world | .invalid world | .unsupported _ world => world

def readLocal (frame : Frame) (index : Nat) : Option Value :=
  match frame.slots[index]? with
  | some (.live (some value)) => some value
  | _ => none

def writeLocal (frame : Frame) (index : Nat) (value : Value) : Option Frame :=
  frame.types[index]?.bind (fun ty =>
    if fits ty value then match frame.slots[index]? with
      | some (.live _) => some {frame with slots := frame.slots.set index (.live (some value))}
      | _ => none
    else none)

def storageLive (frame : Frame) (index : Nat) : Option Frame :=
  match frame.slots[index]? with
  | some .dead => some {frame with slots := frame.slots.set index (.live none)}
  | _ => none

def storageDead (frame : Frame) (index : Nat) : Option Frame :=
  match frame.slots[index]? with
  | some (.live _) => some {frame with slots := frame.slots.set index .dead}
  | _ => none

def mode (mutable : Bool) : NativeByteBorrow.Mode := if mutable then .exclusive else .shared

def layout (length : Word) (element : Element := .word) : NativeByteMemory.Layout := ⟨element.width * length.val, element.width⟩

/-- Data pointers are recovered by complete identity. Tags are minted only by
successful checked machine operations, using their pre-operation counter. -/
def issue (world : State) (mutable : Bool) (input : Value) (element : Element := .word) : Option (Value × State) :=
  match input with
  | .raw ⟨pointer, some length⟩ =>
    let index := world.pointers.registers.idxOf pointer
    if world.pointers.registers[index]? = some pointer then
      (NativeReferenceMachine.execute world (.borrow index (mode mutable) (layout length element))).map
        (fun next => (.reference mutable ⟨world.nextTag⟩ length, next))
    else none
  | .reference _ reference length =>
    (NativeByteBorrow.lookup world.leases reference.tag).bind (fun lease =>
      let parent := world.references.idxOf reference
      let index := world.pointers.registers.idxOf lease.pointer
      if lease.layout = layout length element ∧ world.references[parent]? = some reference ∧
          world.pointers.registers[index]? = some lease.pointer then
        (NativeReferenceMachine.execute world (.reborrow parent index (mode mutable) (layout length element))).map
          (fun next => (.reference mutable ⟨world.nextTag⟩ length, next))
      else none)
  | _ => none

/-- `Use` carries Charon's retag flag. Reference retags execute a checked
reborrow; a no-retag transfer keeps the stable reference identity. Primitive
and raw values contain no modeled references to retag. -/
def retagValue (frame : Frame) (value : Value) (enabled : Bool) (element : Element) : Option (Value × Frame) :=
  if enabled then match value with
    | .reference mutable _ _ => (issue frame.world mutable value element).map
        (fun (tagged, world) => (tagged, {frame with world}))
    | _ => some (value, frame)
  else some (value, frame)

def evalOperand (frame : Frame) : Operand → Option (Value × Frame)
  | .copy index => (readLocal frame index).map (fun value => (value, frame))
  | .move index => (readLocal frame index).map (fun value =>
    (value, {frame with slots := frame.slots.set index (.live none)}))

def evalRvalue (frame : Frame) : Rvalue → Option (Value × Frame)
  | .unit => some (.unit, frame)
  | .use value retag element => (evalOperand frame value).bind (fun (value, next) => retagValue next value retag element)
  | .rawCast value => (evalOperand frame value).bind (fun (value, next) =>
    match value with
    | .raw ⟨_, none⟩ => some (value, next)
    | _ => none)
  | .borrow mutable base element => (readLocal frame base).bind (fun value =>
    (issue frame.world mutable value element).map (fun (reference, world) => (reference, {frame with world})))

def evalArgs (frame : Frame) : List Operand → Option (List Value × Frame)
  | [] => some ([], frame)
  | value :: tail => (evalOperand frame value).bind (fun (value, next) =>
    (evalArgs next tail).map (fun (values, final) => (value :: values, final)))

def initial (types : List Ty) (argCount : Nat) (args : List Value) (world : State) : Option Frame :=
  if args.length = argCount ∧ argCount + 1 ≤ types.length ∧
      (((types.drop 1).take argCount).zip args).all (fun (ty, value) => fits ty value) = true then
    some ⟨types, .dead :: (args.map (fun value => Slot.live (some value)) ++
      List.replicate (types.length - argCount - 1) Slot.dead), world⟩
  else none

def partsValue : Value → Value → Option Value
  | .raw ⟨pointer, none⟩, .usize length => some (.raw ⟨pointer, some length⟩)
  | _, _ => none

def evalParts (frame : Frame) (target : Nat) (data length : Operand) : Option Frame :=
  (evalOperand frame data).bind (fun (pointer, first) =>
    (evalOperand first length).bind (fun (count, evaluated) =>
      (partsValue pointer count).bind (writeLocal evaluated target)))

def eval : Body → Frame → Flow
  | .done, frame => .continued frame
  | .ret, frame => match readLocal frame 0 with
    | some value => .returned value frame.world
    | none => .invalid frame.world
  | .resume, frame => .unwind frame.world
  | .abort, frame => .invalid frame.world
  | .unsupported source _, frame => .unsupported source frame.world
  | .storageLive index next, frame => match storageLive frame index with
    | some changed => eval next changed
    | none => .invalid frame.world
  | .storageDead index next, frame => match storageDead frame index with
    | some changed => eval next changed
    | none => .invalid frame.world
  | .assign target value next, frame => match evalRvalue frame value with
    | none => .invalid frame.world
    | some (value, evaluated) => match writeLocal evaluated target value with
      | none => .invalid evaluated.world
      | some changed => eval next changed
  | .parts target data length _ next, frame => match evalParts frame target data length with
    | some changed => eval next changed
    | none => .invalid frame.world
  | .constIf condition yes no next, frame =>
    match (if condition then eval yes frame else eval no frame) with
    | .continued changed => eval next changed
    | .returned value world => .returned value world
    | .unwind world => .unwind world
    | .invalid world => .invalid world
    | .unsupported source world => .unsupported source world
  | .call _ types argCount target args callee unwind next, frame => match evalArgs frame args with
    | none => .invalid frame.world
    | some (values, evaluated) => match initial types argCount values evaluated.world with
      | none => .invalid evaluated.world
      | some called => match eval callee called with
        | .returned value world => match writeLocal {evaluated with world} target value with
          | some changed => eval next changed
          | none => .invalid world
        | .unwind world => eval unwind {evaluated with world}
        | .invalid world => .invalid world
        | .unsupported source world => .unsupported source world
        | .continued changed => .invalid changed.world

def decodeArgs (world : State) : List Input → Option (List Value)
  | [] => some []
  | arg :: tail => (decodeInput world arg).bind (fun value => (decodeArgs world tail).map (value :: ·))

def invoke (function : Function) (world : State) (args : List Input) : Flow :=
  match decodeArgs world args with
  | none => .invalid world
  | some values => match initial function.types function.argCount values world with
    | some frame => eval function.body frame
    | none => .invalid world

theorem issue_executes (world next : State) (mutable : Bool) (input output : Value) {element : Element}
    (issued : issue world mutable input element = some (output, next)) :
    ∃ op, NativeReferenceMachine.execute world op = some next := by
  cases input with
  | unit => cases issued
  | usize word => cases issued
  | raw raw =>
    rcases raw with ⟨pointer, length⟩
    cases length with
    | none => cases issued
    | some length =>
      simp only [issue] at issued
      split at issued
      next =>
        obtain ⟨final, actual, same⟩ := Option.map_eq_some_iff.mp issued
        cases same
        exact ⟨_, actual⟩
      next => cases issued
  | reference parent reference length =>
    simp only [issue, Option.bind_eq_some_iff] at issued
    obtain ⟨lease, _, issued⟩ := issued
    split at issued
    next =>
      obtain ⟨final, actual, same⟩ := Option.map_eq_some_iff.mp issued
      cases same
      exact ⟨_, actual⟩
    next => cases issued

theorem issue_projects (world next : State) (mutable : Bool) (input output : Value) {element : Element}
    (issued : issue world mutable input element = some (output, next)) : NativeReferenceMachine.Runs world next := by
  obtain ⟨op, actual⟩ := issue_executes world next mutable input output issued
  exact NativeReferenceMachine.Runs.step (.refl world) op actual

theorem issue_returned_tag (world next : State) (mutable : Bool) (input output : Value) {element : Element}
    (issued : issue world mutable input element = some (output, next)) :
    ∃ length, output = .reference mutable ⟨world.nextTag⟩ length := by
  cases input with
  | unit => cases issued
  | usize word => cases issued
  | raw raw =>
    rcases raw with ⟨pointer, length⟩
    cases length with
    | none => cases issued
    | some length =>
      simp only [issue] at issued
      split at issued
      next =>
        obtain ⟨final, _, same⟩ := Option.map_eq_some_iff.mp issued
        exact ⟨length, (congrArg Prod.fst same).symm⟩
      next => cases issued
  | reference parent reference length =>
    simp only [issue, Option.bind_eq_some_iff] at issued
    obtain ⟨lease, _, issued⟩ := issued
    split at issued
    next =>
      obtain ⟨final, _, same⟩ := Option.map_eq_some_iff.mp issued
      exact ⟨length, (congrArg Prod.fst same).symm⟩
    next => cases issued

theorem writeLocal_world (frame next : Frame) (index : Nat) (value : Value) (written : writeLocal frame index value = some next) :
    next.world = frame.world := by
  unfold writeLocal at written
  cases found : frame.types[index]? with
  | none => simp only [found, Option.bind_none] at written; cases written
  | some ty =>
    simp only [found, Option.bind_some] at written
    split at written
    next =>
      cases slot : frame.slots[index]? with
      | none => simp only [slot] at written; cases written
      | some old =>
        cases old with
        | dead => simp only [slot] at written; cases written
        | live previous => simp only [slot] at written; cases written; rfl
    next => cases written

theorem storageLive_world (frame next : Frame) (index : Nat) (changed : storageLive frame index = some next) : next.world = frame.world := by
  unfold storageLive at changed
  cases slot : frame.slots[index]? with
  | none => simp only [slot] at changed; cases changed
  | some old =>
    cases old with
    | dead => simp only [slot] at changed; cases changed; rfl
    | live previous => simp only [slot] at changed; cases changed

theorem storageDead_world (frame next : Frame) (index : Nat) (changed : storageDead frame index = some next) : next.world = frame.world := by
  unfold storageDead at changed
  cases slot : frame.slots[index]? with
  | none => simp only [slot] at changed; cases changed
  | some old =>
    cases old with
    | dead => simp only [slot] at changed; cases changed
    | live previous => simp only [slot] at changed; cases changed; rfl

theorem evalOperand_world (frame next : Frame) (operand : Operand) (value : Value)
    (evaluated : evalOperand frame operand = some (value, next)) : next.world = frame.world := by
  cases operand <;> simp only [evalOperand, Option.map_eq_some_iff] at evaluated
  · obtain ⟨_, _, same⟩ := evaluated; cases same; rfl
  · obtain ⟨_, _, same⟩ := evaluated; cases same; rfl

theorem retagValue_projects (frame next : Frame) (input output : Value) (enabled : Bool) (element : Element)
    (tagged : retagValue frame input enabled element = some (output, next)) :
    NativeReferenceMachine.Runs frame.world next.world := by
  cases enabled with
  | false => cases tagged; exact .refl _
  | true =>
    cases input with
    | unit => cases tagged; exact .refl _
    | usize word => cases tagged; exact .refl _
    | raw pointer => cases tagged; exact .refl _
    | reference mutable reference length =>
      simp only [retagValue, ite_true, Option.map_eq_some_iff] at tagged
      obtain ⟨⟨value, world⟩, actual, same⟩ := tagged
      cases same
      exact issue_projects _ _ _ _ _ actual

theorem retagValue_disabled (frame : Frame) (value : Value) (element : Element) :
    retagValue frame value false element = some (value, frame) := rfl

theorem retagValue_reference (frame : Frame) (mutable : Bool) (reference : Reference) (length : Word) (element : Element) :
    retagValue frame (.reference mutable reference length) true element =
      (issue frame.world mutable (.reference mutable reference length) element).map
        (fun (value, world) => (value, {frame with world})) := rfl

theorem retagValue_fresh (frame next : Frame) (mutable : Bool) (reference : Reference) (length : Word)
    (element : Element) (output : Value)
    (tagged : retagValue frame (.reference mutable reference length) true element = some (output, next)) :
    ∃ count, output = .reference mutable ⟨frame.world.nextTag⟩ count := by
  rw [retagValue_reference] at tagged
  obtain ⟨⟨value, world⟩, actual, same⟩ := Option.map_eq_some_iff.mp tagged
  cases same
  exact issue_returned_tag _ _ _ _ _ actual

theorem evalRvalue_projects (frame next : Frame) (rvalue : Rvalue) (value : Value)
    (evaluated : evalRvalue frame rvalue = some (value, next)) : NativeReferenceMachine.Runs frame.world next.world := by
  cases rvalue with
  | unit => cases evaluated; exact .refl _
  | use operand retag element =>
    simp only [evalRvalue, Option.bind_eq_some_iff] at evaluated
    obtain ⟨⟨input, middle⟩, selected, tagged⟩ := evaluated
    have same := evalOperand_world frame middle operand input selected
    rw [← same]
    exact retagValue_projects middle next input value retag element tagged
  | rawCast operand =>
    simp only [evalRvalue, Option.bind_eq_some_iff] at evaluated
    obtain ⟨⟨input, changed⟩, first, actual⟩ := evaluated
    cases input with
    | unit => cases actual
    | usize word => cases actual
    | reference mutable reference length => cases actual
    | raw pointer =>
      rcases pointer with ⟨pointer, length⟩
      cases length with
      | some length => cases actual
      | none =>
        cases actual
        rw [evalOperand_world frame _ operand _ first]
        exact .refl _
  | borrow mutable base element =>
    simp only [evalRvalue, Option.bind_eq_some_iff, Option.map_eq_some_iff] at evaluated
    obtain ⟨input, _, ⟨output, world⟩, issued, same⟩ := evaluated
    cases same
    exact issue_projects frame.world world mutable input output issued

theorem evalArgs_world (frame next : Frame) (args : List Operand) (values : List Value)
    (evaluated : evalArgs frame args = some (values, next)) : next.world = frame.world := by
  induction args generalizing frame values with
  | nil => cases evaluated; rfl
  | cons operand tail ih =>
    simp only [evalArgs, Option.bind_eq_some_iff, Option.map_eq_some_iff] at evaluated
    obtain ⟨⟨value, middle⟩, first, ⟨later, final⟩, rest, same⟩ := evaluated
    cases same
    exact (ih middle later rest).trans (evalOperand_world frame middle operand value first)

theorem evalParts_world (frame next : Frame) (target : Nat) (data length : Operand)
    (evaluated : evalParts frame target data length = some next) : next.world = frame.world := by
  simp only [evalParts, Option.bind_eq_some_iff] at evaluated
  obtain ⟨⟨pointer, first⟩, dataEq, ⟨count, middle⟩, lengthEq, value, _, written⟩ := evaluated
  exact (writeLocal_world middle next target value written).trans
    ((evalOperand_world first middle length count lengthEq).trans (evalOperand_world frame first data pointer dataEq))

theorem initial_world (types : List Ty) (argCount : Nat) (args : List Value) (world : State) (frame : Frame)
    (initialized : initial types argCount args world = some frame) : frame.world = world := by
  unfold initial at initialized
  split at initialized
  · cases initialized; rfl
  · cases initialized

theorem eval_projects (body : Body) (frame : Frame) : NativeReferenceMachine.Runs frame.world (eval body frame).world := by
  induction body generalizing frame with
  | done => exact .refl _
  | ret => simp only [eval]; split <;> exact .refl _
  | resume => exact .refl _
  | abort => exact .refl _
  | unsupported source next ih => exact .refl _
  | storageLive index next ih =>
    simp only [eval]
    split
    next changed =>
      have same := storageLive_world frame _ index changed
      rw [← same]
      exact ih _
    next => exact .refl _
  | storageDead index next ih =>
    simp only [eval]
    split
    next changed =>
      have same := storageDead_world frame _ index changed
      rw [← same]
      exact ih _
    next => exact .refl _
  | assign target value next ih =>
    simp only [eval]
    split
    next => exact .refl _
    next evaluated =>
      have first := evalRvalue_projects frame _ value _ evaluated
      split
      next => exact first
      next written =>
        have same := writeLocal_world _ _ target _ written
        exact NativeReferenceMachine.runs_trans _ _ _ first (by rw [← same]; exact ih _)
  | parts target data length unwind next unwindIH nextIH =>
    simp only [eval]
    split
    next evaluated =>
      rw [← evalParts_world frame _ target data length evaluated]
      exact nextIH _
    next => exact .refl _
  | constIf condition yes no next yesIH noIH nextIH =>
    have branch : NativeReferenceMachine.Runs frame.world (if condition then eval yes frame else eval no frame).world := by
      cases condition
      · exact noIH frame
      · exact yesIH frame
    simp only [eval]
    split
    next same =>
      rw [same] at branch
      exact NativeReferenceMachine.runs_trans _ _ _ branch (nextIH _)
    next same => rw [same] at branch; exact branch
    next same => rw [same] at branch; exact branch
    next same => rw [same] at branch; exact branch
    next same => rw [same] at branch; exact branch
  | call name types argCount target args callee unwind next calleeIH unwindIH nextIH =>
    simp only [eval]
    split
    next => exact .refl _
    next evaluated =>
      rename_i values evaluatedFrame
      have same := evalArgs_world frame _ args _ evaluated
      split
      next => rw [same]; exact .refl _
      next initialized =>
        rename_i calledFrame
        have calledWorld := (initial_world types argCount _ _ _ initialized).trans same
        have called := calleeIH calledFrame
        rw [calledWorld] at called
        split
        next result =>
          rw [result] at called
          simp only [Flow.world] at called
          split
          next written =>
            have changed := writeLocal_world _ _ target _ written
            dsimp only at changed
            exact NativeReferenceMachine.runs_trans _ _ _ called (by rw [← changed]; exact nextIH _)
          next => exact called
        next result =>
          rename_i resultWorld
          rw [result] at called
          simp only [Flow.world] at called
          exact NativeReferenceMachine.runs_trans _ _ _ called (unwindIH {evaluatedFrame with world := resultWorld})
        next result => rw [result] at called; exact called
        next result => rw [result] at called; exact called
        next result => rw [result] at called; exact called

theorem invoke_projects (function : Function) (world : State) (args : List Input) :
    NativeReferenceMachine.Runs world (invoke function world args).world := by
  simp only [invoke]
  split
  next => exact .refl _
  next =>
    split
    next initialized =>
      have result := eval_projects function.body ‹Frame›
      rw [initial_world function.types function.argCount _ world _ initialized] at result
      exact result
    next => exact .refl _

theorem reference_runs_wellFormed (world next : State) (valid : NativeReferenceMachine.WellFormed world)
    (runs : NativeReferenceMachine.Runs world next) : NativeReferenceMachine.WellFormed next := by
  induction runs with
  | refl => exact valid
  | step prior op actual ih => exact NativeReferenceMachine.execute_wellFormed _ _ ih op actual

theorem invoke_wellFormed (function : Function) (world : State) (valid : NativeReferenceMachine.WellFormed world) (args : List Input) :
    NativeReferenceMachine.WellFormed (invoke function world args).world :=
  reference_runs_wellFormed world _ valid (invoke_projects function world args)

theorem issue_raw_selected (world : State) (index : Nat) (pointer : Pointer)
    (selected : world.pointers.registers[index]? = some pointer) (mutable : Bool) (length : Word) (element : Element := .word) :
    issue world mutable (.raw ⟨pointer, some length⟩) element =
      (NativeReferenceMachine.grant world none (mode mutable) pointer (layout length element)).map
        (fun next => (.reference mutable ⟨world.nextTag⟩ length, next)) := by
  have recovered := List.getElem?_idxOf (List.mem_of_getElem? selected)
  simp only [issue, recovered, ite_true, NativeReferenceMachine.execute, Option.bind_some]

theorem reference_runs_reachable (world next : State) (reachable : NativeReferenceMachine.Reachable world)
    (runs : NativeReferenceMachine.Runs world next) : NativeReferenceMachine.Reachable next := by
  induction runs with
  | refl => exact reachable
  | step prior op actual ih => exact NativeReferenceMachine.Reachable.step ih op actual

theorem invoke_reachable (function : Function) (world : State) (reachable : NativeReferenceMachine.Reachable world) (args : List Input) :
    NativeReferenceMachine.Reachable (invoke function world args).world :=
  reference_runs_reachable world _ reachable (invoke_projects function world args)

end FormalProof4FHE.HasteBoots.NativeSliceLLBC
