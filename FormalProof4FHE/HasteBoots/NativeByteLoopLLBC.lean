module
public import FormalProof4FHE.HasteBoots.NativeByteDropTraversal
@[expose] public section

/-! Typed finite blocks and an unbounded single-outer-loop LLBC relation.
Loop-backedge cleanup is explicit ghost composition, not a proved Rust lifetime
translation. Storage liveness changes slots only. No compiler or work law is
asserted here. -/
namespace FormalProof4FHE.HasteBoots.NativeByteLoopLLBC
open NativeReferenceMachine (State Reference)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeByteSliceIndex (Slice)

inductive Ty where
  | unit | usize | boolean | rawByte | sliceRef | byteRef
  deriving DecidableEq

inductive Value where
  | unit
  | usize (value : Word)
  | boolean (value : Bool)
  | rawByte (pointer : Pointer)
  | sliceRef (slice : Slice)
  | byteRef (reference : Reference)
  deriving DecidableEq

def fits : Ty → Value → Bool
  | .unit, .unit | .usize, .usize _ | .boolean, .boolean _ | .rawByte, .rawByte _
    | .sliceRef, .sliceRef _ | .byteRef, .byteRef _ => true
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

/-- MIR storage markers may be repeated along different control paths. -/
def storageLive (frame : Frame) (index : Nat) : Option Frame :=
  frame.slots[index]?.map (fun _ => {frame with slots := frame.slots.set index (.live none)})

def storageDead (frame : Frame) (index : Nat) : Option Frame :=
  frame.slots[index]?.map (fun _ => {frame with slots := frame.slots.set index .dead})

inductive Operand where
  | copy (index : Nat)
  | move (index : Nat)
  | literal (value : Word)
  | metadata (index : Nat)
  deriving DecidableEq

def copyAllowed : Value → Bool
  | .sliceRef _ | .byteRef _ => false
  | _ => true

def evalOperand (frame : Frame) : Operand → Option (Value × Frame)
  | .copy index => (readLocal frame index).bind (fun value => if copyAllowed value then some (value, frame) else none)
  | .move index => (readLocal frame index).map (fun value =>
    (value, {frame with slots := frame.slots.set index (.live none)}))
  | .literal value => some (.usize value, frame)
  | .metadata index => (readLocal frame index).bind (fun value => match value with
    | .sliceRef slice => some (.usize slice.length, frame)
    | _ => none)

inductive EvalResult where
  | value (value : Value) (frame : Frame)
  | invalid (frame : Frame)
  deriving DecidableEq

def EvalResult.frame : EvalResult → Frame
  | .value _ frame | .invalid frame => frame

/-- Shared with the established checked byte-reference reborrow operation. -/
def borrowSlice (frame : Frame) (slice : Slice) : EvalResult :=
  match NativeSliceLLBC.issue frame.world true (.reference true slice.reference slice.length) .byte with
  | none => .invalid frame
  | some (value, world) => match value with
    | .reference true reference length => .value (.sliceRef ⟨reference, length⟩) {frame with world}
    | _ => .invalid {frame with world}

def retagValue (frame : Frame) (value : Value) (enabled : Bool) : EvalResult :=
  if enabled then match value with
    | .sliceRef slice => borrowSlice frame slice
    | .byteRef reference => match borrowSlice frame ⟨reference, ⟨1, by decide⟩⟩ with
      | .value (.sliceRef slice) next => .value (.byteRef slice.reference) next
      | .value _ next | .invalid next => .invalid next
    | _ => .value value frame
  else .value value frame

inductive Rvalue where
  | unit
  | use (operand : Operand) (retag : Bool)
  | eq (left right : Operand)
  | addWrap (left right : Operand)
  | borrowSlice (index : Nat)
  | rawByte (index : Nat)
  deriving DecidableEq

inductive Binary where
  | eq | addWrap
  deriving DecidableEq

def binaryValue : Binary → Value → Value → Option Value
  | .eq, .usize left, .usize right => some (.boolean (left == right))
  | .addWrap, .usize left, .usize right => some (.usize ⟨(left.val + right.val) % (2^64), Nat.mod_lt _ (by decide)⟩)
  | _, _, _ => none

def evalBinary (frame : Frame) (op : Binary) (left right : Operand) : EvalResult :=
  match evalOperand frame left with
  | none => .invalid frame
  | some (a, first) => match evalOperand first right with
    | none => .invalid first
    | some (b, next) => match binaryValue op a b with
      | none => .invalid next
      | some value => .value value next

def evalRvalue (frame : Frame) : Rvalue → EvalResult
  | .unit => .value .unit frame
  | .use operand retag => match evalOperand frame operand with
    | none => .invalid frame
    | some (value, next) => retagValue next value retag
  | .eq left right => evalBinary frame .eq left right
  | .addWrap left right => evalBinary frame .addWrap left right
  | .borrowSlice index => match readLocal frame index with
    | some (.sliceRef slice) => borrowSlice frame slice
    | _ => .invalid frame
  | .rawByte index => match readLocal frame index with
    | some (.byteRef reference) => match NativeByteSliceIndex.rawByte frame.world reference with
      | some pointer => .value (.rawByte pointer) frame
      | none => .invalid frame
    | _ => .invalid frame

inductive IndexResult where
  | next (frame : Frame)
  | unwind (frame : Frame)
  | invalid (frame : Frame)
  deriving DecidableEq

def IndexResult.frame : IndexResult → Frame
  | .next frame | .unwind frame | .invalid frame => frame

def evalIndex (frame : Frame) (target : Nat) (source offset : Operand) : IndexResult :=
  match evalOperand frame source with
  | none => .invalid frame
  | some (value, first) => match evalOperand first offset with
    | none => .invalid first
    | some (position, evaluated) => match value, position with
      | .sliceRef slice, .usize index =>
        if index.val < slice.length.val then match NativeByteSliceIndex.index evaluated.world slice index with
          | .invalid world => .invalid {evaluated with world}
          | .value reference world => match writeLocal {evaluated with world} target (.byteRef reference) with
            | none => .invalid {evaluated with world}
            | some next => .next next
        else .unwind evaluated
      | _, _ => .invalid evaluated

inductive Code where
  | done | ret | resume | abort | breaking | continuing
  | storageLive (index : Nat) (next : Code)
  | storageDead (index : Nat) (next : Code)
  | assign (target : Nat) (value : Rvalue) (next : Code)
  | index (target : Nat) (source offset : Operand) (unwind next : Code)
  | branch (condition : Operand) (yes no next : Code)
  deriving DecidableEq

inductive Flow where
  | normal (frame : Frame)
  | returned (value : Value) (frame : Frame)
  | unwind (frame : Frame)
  | invalid (frame : Frame)
  | breaking (frame : Frame)
  | continuing (frame : Frame)
  deriving DecidableEq

def Flow.frame : Flow → Frame
  | .normal frame | .returned _ frame | .unwind frame | .invalid frame | .breaking frame | .continuing frame => frame

def Flow.world (flow : Flow) : State := flow.frame.world

def Flow.terminal : Flow → Bool
  | .returned _ _ | .unwind _ | .invalid _ => true
  | _ => false

def eval : Code → Frame → Flow
  | .done, frame => .normal frame
  | .ret, frame => match readLocal frame 0 with
    | none => .invalid frame
    | some value => .returned value frame
  | .resume, frame => .unwind frame
  | .abort, frame => .invalid frame
  | .breaking, frame => .breaking frame
  | .continuing, frame => .continuing frame
  | .storageLive index next, frame => match storageLive frame index with
    | none => .invalid frame
    | some changed => eval next changed
  | .storageDead index next, frame => match storageDead frame index with
    | none => .invalid frame
    | some changed => eval next changed
  | .assign target value next, frame => match evalRvalue frame value with
    | .invalid changed => .invalid changed
    | .value value evaluated => match writeLocal evaluated target value with
      | none => .invalid evaluated
      | some changed => eval next changed
  | .index target source offset unwind next, frame => match evalIndex frame target source offset with
    | .next changed => eval next changed
    | .unwind changed => eval unwind changed
    | .invalid changed => .invalid changed
  | .branch condition yes no next, frame => match evalOperand frame condition with
    | none => .invalid frame
    | some (value, evaluated) => match value with
      | .boolean condition => match (match condition with | true => eval yes evaluated | false => eval no evaluated) with
        | .normal changed => eval next changed
        | flow => flow
      | _ => .invalid evaluated

/-- Explicitly compose checked cleanup at a loop backedge. It does not change
source local values or imply that Rust ends those lifetimes at this point. -/
def settleFrame (entered : State) (frame : Frame) : Option Frame × Frame :=
  let result := NativeReferenceCleanup.closeScope entered frame.world
  let changed := {frame with world := result.world}
  (if result.pending.isEmpty then some changed else none, changed)

def settle (entered : State) : Flow → Flow
  | .normal frame => match (settleFrame entered frame).1 with
    | some changed => .normal changed
    | none => .invalid (settleFrame entered frame).2
  | .continuing frame => match (settleFrame entered frame).1 with
    | some changed => .continuing changed
    | none => .invalid (settleFrame entered frame).2
  | flow => flow

inductive LoopRuns (body after : Code) : Frame → Flow → Prop where
  | stop (frame next : Frame) (flow : Flow) (evaluated : eval body frame = .breaking next)
      (returned : eval after next = flow) : LoopRuns body after frame flow
  | next (frame changed : Frame) (flow : Flow)
      (evaluated : settle frame.world (eval body frame) = .continuing changed)
      (later : LoopRuns body after changed flow) : LoopRuns body after frame flow
  | normal (frame changed : Frame) (flow : Flow)
      (evaluated : settle frame.world (eval body frame) = .normal changed)
      (later : LoopRuns body after changed flow) : LoopRuns body after frame flow
  | terminal (frame : Frame) (flow : Flow)
      (evaluated : settle frame.world (eval body frame) = flow) (stopped : flow.terminal = true) : LoopRuns body after frame flow

structure Function where
  name : String
  types : List Ty
  before : Code
  body : Code
  after : Code
  deriving DecidableEq

/-- The only external operand selects an existing live exclusive byte-slice
reference; its extent is recovered from that lease, not supplied separately. -/
def decodeSlice (world : State) (register : Nat) : Option Slice := do
  let reference ← world.references[register]?
  let lease ← NativeByteBorrow.lookup world.leases reference.tag
  if bounded : lease.layout.size < 2^64 then
    if lease.layout.alignment = 1 ∧ lease.mode = .exclusive then
      some ⟨reference, ⟨lease.layout.size, bounded⟩⟩
    else none
  else none

def initial (function : Function) (world : State) (slice : Slice) : Option Frame :=
  if function.types[0]? = some .unit ∧ function.types[1]? = some .sliceRef then
    some ⟨function.types, .dead :: .live (some (.sliceRef slice)) :: List.replicate (function.types.length - 2) .dead, world⟩
  else none

inductive Executes (function : Function) : Frame → Flow → Prop where
  | start (frame next : Frame) (flow : Flow) (evaluated : eval function.before frame = .normal next)
      (loop : LoopRuns function.body function.after next flow) : Executes function frame flow
  | early (frame : Frame) (flow : Flow) (evaluated : eval function.before frame = flow)
      (stopped : flow.terminal = true) : Executes function frame flow

def invalidEntry (function : Function) (world : State) : Frame :=
  ⟨function.types, List.replicate function.types.length .dead, world⟩

inductive Invokes (function : Function) (world : State) (register : Nat) : Flow → Prop where
  | invalid (decoded : decodeSlice world register = none) : Invokes function world register (.invalid (invalidEntry function world))
  | malformed (slice : Slice) (decoded : decodeSlice world register = some slice)
      (rejected : initial function world slice = none) : Invokes function world register (.invalid (invalidEntry function world))
  | valid (slice : Slice) (frame : Frame) (flow : Flow) (decoded : decodeSlice world register = some slice)
      (initialized : initial function world slice = some frame) (executed : Executes function frame flow) : Invokes function world register flow

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

theorem storageLive_world (frame next : Frame) (index : Nat) (changed : storageLive frame index = some next) :
    next.world = frame.world := by
  simp only [storageLive, Option.map_eq_some_iff] at changed
  obtain ⟨_, _, same⟩ := changed
  cases same
  rfl

theorem storageDead_world (frame next : Frame) (index : Nat) (changed : storageDead frame index = some next) :
    next.world = frame.world := by
  simp only [storageDead, Option.map_eq_some_iff] at changed
  obtain ⟨_, _, same⟩ := changed
  cases same
  rfl

theorem storageLive_reset (frame : Frame) (index : Nat) (old : Slot) (selected : frame.slots[index]? = some old) :
    storageLive frame index = some {frame with slots := frame.slots.set index (.live none)} := by
  simp only [storageLive, selected, Option.map_some]

theorem storageDead_reset (frame : Frame) (index : Nat) (old : Slot) (selected : frame.slots[index]? = some old) :
    storageDead frame index = some {frame with slots := frame.slots.set index .dead} := by
  simp only [storageDead, selected, Option.map_some]

theorem evalOperand_world (frame next : Frame) (operand : Operand) (value : Value)
    (evaluated : evalOperand frame operand = some (value, next)) : next.world = frame.world := by
  cases operand with
  | copy index =>
    simp only [evalOperand, Option.bind_eq_some_iff] at evaluated
    obtain ⟨_, _, evaluated⟩ := evaluated
    split at evaluated
    · cases evaluated; rfl
    · cases evaluated
  | move index =>
    simp only [evalOperand, Option.map_eq_some_iff] at evaluated
    obtain ⟨_, _, same⟩ := evaluated
    cases same
    rfl
  | literal literal => cases evaluated; rfl
  | metadata index =>
    simp only [evalOperand, Option.bind_eq_some_iff] at evaluated
    obtain ⟨input, _, evaluated⟩ := evaluated
    cases input <;> cases evaluated
    rfl

theorem issue_slice_shape (world next : State) (slice : Slice) (value : NativeSliceLLBC.Value)
    (issued : NativeSliceLLBC.issue world true (.reference true slice.reference slice.length) .byte = some (value, next)) :
    value = .reference true ⟨world.nextTag⟩ slice.length := by
  simp only [NativeSliceLLBC.issue, Option.bind_eq_some_iff] at issued
  obtain ⟨lease, _, issued⟩ := issued
  split at issued
  · obtain ⟨world, _, same⟩ := Option.map_eq_some_iff.mp issued
    cases same
    rfl
  · cases issued

theorem borrowSlice_projects (frame : Frame) (slice : Slice) :
    NativeReferenceMachine.Runs frame.world (borrowSlice frame slice).frame.world := by
  cases actual : NativeSliceLLBC.issue frame.world true (.reference true slice.reference slice.length) .byte with
  | none => simp only [borrowSlice, actual, EvalResult.frame]; exact .refl _
  | some output =>
    rcases output with ⟨value, world⟩
    have first := NativeSliceLLBC.issue_projects frame.world world true _ value actual
    obtain ⟨length, same⟩ := NativeSliceLLBC.issue_returned_tag frame.world world true _ value actual
    subst value
    simpa only [borrowSlice, actual, EvalResult.frame] using first

theorem retagValue_projects (frame : Frame) (value : Value) (enabled : Bool) :
    NativeReferenceMachine.Runs frame.world (retagValue frame value enabled).frame.world := by
  cases enabled with
  | false => exact .refl _
  | true =>
    cases value with
    | unit => exact .refl _
    | usize word => exact .refl _
    | boolean condition => exact .refl _
    | rawByte pointer => exact .refl _
    | sliceRef slice => exact borrowSlice_projects frame slice
    | byteRef reference =>
      have first := borrowSlice_projects frame ⟨reference, ⟨1, by decide⟩⟩
      cases actual : borrowSlice frame ⟨reference, ⟨1, by decide⟩⟩ with
      | invalid next => simpa only [retagValue, ite_true, actual, EvalResult.frame] using first
      | value value next =>
        cases value <;> simpa only [retagValue, ite_true, actual, EvalResult.frame] using first

theorem evalBinary_world (frame : Frame) (op : Binary) (left right : Operand) :
    (evalBinary frame op left right).frame.world = frame.world := by
  cases firstEq : evalOperand frame left with
  | none => simp only [evalBinary, firstEq, EvalResult.frame]
  | some first =>
    rcases first with ⟨a, middle⟩
    have same := evalOperand_world frame middle left a firstEq
    simp only [evalBinary, firstEq]
    cases secondEq : evalOperand middle right with
    | none => exact same
    | some second =>
      rcases second with ⟨b, next⟩
      have secondSame := evalOperand_world middle next right b secondEq
      simp only []
      cases actual : binaryValue op a b <;> exact secondSame.trans same

theorem evalRvalue_projects (frame : Frame) (value : Rvalue) :
    NativeReferenceMachine.Runs frame.world (evalRvalue frame value).frame.world := by
  cases value with
  | unit => exact .refl _
  | use operand retag =>
    cases actual : evalOperand frame operand with
    | none => simp only [evalRvalue, actual, EvalResult.frame]; exact .refl _
    | some output =>
      rcases output with ⟨value, next⟩
      have same := evalOperand_world frame next operand value actual
      simp only [evalRvalue, actual]
      rw [← same]
      exact retagValue_projects next value retag
  | eq left right => rw [show (evalRvalue frame (.eq left right)).frame.world = frame.world from evalBinary_world frame .eq left right]; exact .refl _
  | addWrap left right => rw [show (evalRvalue frame (.addWrap left right)).frame.world = frame.world from evalBinary_world frame .addWrap left right]; exact .refl _
  | borrowSlice index =>
    cases actual : readLocal frame index with
    | none => simp only [evalRvalue, actual, EvalResult.frame]; exact .refl _
    | some value =>
      simp only [evalRvalue, actual]
      cases value <;> first | exact borrowSlice_projects _ _ | exact .refl _
  | rawByte index =>
    cases actual : readLocal frame index with
    | none => simp only [evalRvalue, actual, EvalResult.frame]; exact .refl _
    | some value =>
      simp only [evalRvalue, actual]
      cases value <;> try exact .refl _
      rename_i reference
      simp only []
      split <;> exact .refl _

theorem evalIndex_projects (frame : Frame) (target : Nat) (source offset : Operand) :
    NativeReferenceMachine.Runs frame.world (evalIndex frame target source offset).frame.world := by
  cases firstEq : evalOperand frame source with
  | none => simp only [evalIndex, firstEq, IndexResult.frame]; exact .refl _
  | some first =>
    rcases first with ⟨value, middle⟩
    have same := evalOperand_world frame middle source value firstEq
    simp only [evalIndex, firstEq]
    cases secondEq : evalOperand middle offset with
    | none => change NativeReferenceMachine.Runs frame.world middle.world; rw [same]; exact .refl _
    | some second =>
      rcases second with ⟨position, evaluated⟩
      have baseWorld := (evalOperand_world middle evaluated offset position secondEq).trans same
      cases value <;> cases position <;> try (change NativeReferenceMachine.Runs frame.world evaluated.world; rw [baseWorld]; exact .refl _)
      rename_i slice index
      simp only []
      split
      · cases actual : NativeByteSliceIndex.index evaluated.world slice index with
        | invalid world =>
          have first := NativeByteSliceIndex.index_projects evaluated.world slice index
          rw [actual] at first
          rw [← baseWorld]
          exact first
        | value reference world =>
          have first := NativeByteSliceIndex.index_projects evaluated.world slice index
          rw [actual] at first
          rw [← baseWorld]
          simp only []
          cases written : writeLocal {evaluated with world} target (.byteRef reference) with
          | none => exact first
          | some next =>
            have nextWorld := writeLocal_world {evaluated with world} next target (.byteRef reference) written
            change NativeReferenceMachine.Runs evaluated.world next.world
            rw [nextWorld]
            exact first
      · change NativeReferenceMachine.Runs frame.world evaluated.world; rw [baseWorld]; exact .refl _

theorem follow_projects (next : Code) (world : State) (flow : Flow)
    (before : NativeReferenceMachine.Runs world flow.world)
    (later : ∀ frame, NativeReferenceMachine.Runs frame.world (eval next frame).world) :
    NativeReferenceMachine.Runs world (match flow with | .normal frame => eval next frame | flow => flow).world := by
  cases flow with
  | normal frame => exact NativeReferenceMachine.runs_trans _ _ _ before (later frame)
  | returned value frame => exact before
  | unwind frame => exact before
  | invalid frame => exact before
  | breaking frame => exact before
  | continuing frame => exact before

theorem eval_projects (code : Code) (frame : Frame) :
    NativeReferenceMachine.Runs frame.world (eval code frame).world := by
  induction code generalizing frame with
  | done => exact .refl _
  | ret => unfold eval; split <;> exact .refl _
  | resume => exact .refl _
  | abort => exact .refl _
  | breaking => exact .refl _
  | continuing => exact .refl _
  | storageLive index next ih =>
    simp only [eval]
    split
    · exact .refl _
    · rename_i changed actual
      rw [← storageLive_world frame changed index actual]
      exact ih changed
  | storageDead index next ih =>
    simp only [eval]
    split
    · exact .refl _
    · rename_i changed actual
      rw [← storageDead_world frame changed index actual]
      exact ih changed
  | assign target value next ih =>
    have first := evalRvalue_projects frame value
    cases actual : evalRvalue frame value with
    | invalid changed => simpa only [eval, actual, EvalResult.frame, Flow.world, Flow.frame] using first
    | value output evaluated =>
      rw [actual] at first
      simp only [eval, actual]
      cases written : writeLocal evaluated target output with
      | none => exact first
      | some changed =>
        have afterWrite := writeLocal_world evaluated changed target output written
        simp only []
        have afterRun : NativeReferenceMachine.Runs evaluated.world (eval next changed).world := by
          rw [← afterWrite]
          exact ih changed
        exact NativeReferenceMachine.runs_trans _ _ _ first afterRun
  | index target source offset unwind next unwindIH nextIH =>
    have first := evalIndex_projects frame target source offset
    cases actual : evalIndex frame target source offset with
    | invalid changed => simpa only [eval, actual, IndexResult.frame, Flow.world, Flow.frame] using first
    | next changed =>
      rw [actual] at first
      simp only [eval, actual]
      exact NativeReferenceMachine.runs_trans _ _ _ first (nextIH changed)
    | unwind changed =>
      rw [actual] at first
      simp only [eval, actual]
      exact NativeReferenceMachine.runs_trans _ _ _ first (unwindIH changed)
  | branch condition yes no next yesIH noIH nextIH =>
    simp only [eval]
    cases actual : evalOperand frame condition with
    | none => exact .refl _
    | some output =>
      rcases output with ⟨value, evaluated⟩
      have same := evalOperand_world frame evaluated condition value actual
      cases value <;> try (change NativeReferenceMachine.Runs frame.world evaluated.world; rw [same]; exact .refl _)
      rename_i condition
      cases condition with
      | false =>
        simp only []
        apply follow_projects next frame.world (eval no evaluated)
        · rw [← same]; exact noIH evaluated
        · exact nextIH
      | true =>
        simp only []
        apply follow_projects next frame.world (eval yes evaluated)
        · rw [← same]; exact yesIH evaluated
        · exact nextIH

theorem settleFrame_projects (entered : State) (frame : Frame) :
    NativeReferenceMachine.Runs frame.world (settleFrame entered frame).2.world ∧
      ∀ changed, (settleFrame entered frame).1 = some changed → NativeReferenceMachine.Runs frame.world changed.world := by
  have cleaned := NativeReferenceCleanup.closeScope_projects entered frame.world
  constructor
  · exact cleaned
  · intro changed selected
    dsimp only [settleFrame] at selected
    split at selected
    · cases selected; exact cleaned
    · cases selected

theorem settle_projects (entered : State) (flow : Flow) :
    NativeReferenceMachine.Runs flow.world (settle entered flow).world := by
  cases flow with
  | normal frame =>
    simp only [settle]
    cases actual : (settleFrame entered frame).1 with
    | none => exact (settleFrame_projects entered frame).1
    | some changed => exact (settleFrame_projects entered frame).2 changed actual
  | continuing frame =>
    simp only [settle]
    cases actual : (settleFrame entered frame).1 with
    | none => exact (settleFrame_projects entered frame).1
    | some changed => exact (settleFrame_projects entered frame).2 changed actual
  | returned value frame => exact .refl _
  | unwind frame => exact .refl _
  | invalid frame => exact .refl _
  | breaking frame => exact .refl _

theorem loopRuns_projects (body after : Code) (frame : Frame) (flow : Flow) (ran : LoopRuns body after frame flow) :
    NativeReferenceMachine.Runs frame.world flow.world := by
  induction ran with
  | stop frame next flow evaluated returned =>
    have first := eval_projects body frame
    rw [evaluated] at first
    have later := eval_projects after next
    rw [returned] at later
    exact NativeReferenceMachine.runs_trans _ _ _ first later
  | next frame changed flow evaluated later ih =>
    have first := NativeReferenceMachine.runs_trans _ _ _ (eval_projects body frame) (settle_projects frame.world (eval body frame))
    rw [evaluated] at first
    exact NativeReferenceMachine.runs_trans _ _ _ first ih
  | normal frame changed flow evaluated later ih =>
    have first := NativeReferenceMachine.runs_trans _ _ _ (eval_projects body frame) (settle_projects frame.world (eval body frame))
    rw [evaluated] at first
    exact NativeReferenceMachine.runs_trans _ _ _ first ih
  | terminal frame flow evaluated stopped =>
    have first := NativeReferenceMachine.runs_trans _ _ _ (eval_projects body frame) (settle_projects frame.world (eval body frame))
    rw [evaluated] at first
    exact first

theorem executes_projects (function : Function) (frame : Frame) (flow : Flow) (ran : Executes function frame flow) :
    NativeReferenceMachine.Runs frame.world flow.world := by
  cases ran with
  | start next flow evaluated loop =>
    have first := eval_projects function.before frame
    rw [evaluated] at first
    exact NativeReferenceMachine.runs_trans _ _ _ first (loopRuns_projects _ _ _ _ loop)
  | early flow evaluated stopped =>
    have first := eval_projects function.before frame
    rw [evaluated] at first
    exact first

theorem executes_reachable (function : Function) (frame : Frame) (flow : Flow)
    (reachable : NativeReferenceMachine.Reachable frame.world) (ran : Executes function frame flow) :
    NativeReferenceMachine.Reachable flow.world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (executes_projects function frame flow ran)

theorem decodeSlice_success (world : State) (register : Nat) (slice : Slice)
    (decoded : decodeSlice world register = some slice) :
    ∃ lease, world.references[register]? = some slice.reference ∧
      NativeByteBorrow.lookup world.leases slice.reference.tag = some lease ∧
      lease.layout = ⟨slice.length.val, 1⟩ ∧ lease.mode = .exclusive := by
  simp only [decodeSlice, Option.bind_eq_bind', Option.bind_eq_some_iff] at decoded
  obtain ⟨reference, registered, lease, found, decoded⟩ := decoded
  split at decoded
  · split at decoded
    · rename_i checked
      cases decoded
      refine ⟨lease, registered, found, ?_, checked.2⟩
      have alignment := checked.1
      change lease.layout = ⟨lease.layout.size, 1⟩
      rw [← alignment]
    · cases decoded
  · cases decoded

theorem loopRuns_deterministic (body after : Code) (frame : Frame) (left right : Flow)
    (first : LoopRuns body after frame left) (second : LoopRuns body after frame right) : left = right := by
  induction first generalizing right with
  | stop frame next flow evaluated returned =>
    cases second <;> simp_all [settle, Flow.terminal]
    all_goals cases right <;> simp_all
  | next frame changed flow evaluated later ih =>
    cases second <;> simp_all [settle, Flow.terminal]
    all_goals first | exact ih _ (by assumption) | (cases right <;> simp_all)
  | normal frame changed flow evaluated later ih =>
    cases second <;> simp_all [settle, Flow.terminal]
    all_goals first | exact ih _ (by assumption) | (cases right <;> simp_all)
  | terminal frame flow evaluated stopped =>
    cases second <;> simp_all [settle, Flow.terminal]
    all_goals cases flow <;> simp_all

theorem initial_world (function : Function) (world : State) (slice : Slice) (frame : Frame)
    (initialized : initial function world slice = some frame) : frame.world = world := by
  unfold initial at initialized
  split at initialized
  · cases initialized; rfl
  · cases initialized

theorem invokes_projects (function : Function) (world : State) (register : Nat) (flow : Flow)
    (invoked : Invokes function world register flow) : NativeReferenceMachine.Runs world flow.world := by
  cases invoked with
  | invalid decoded => exact .refl _
  | malformed slice decoded rejected => exact .refl _
  | valid slice frame flow decoded initialized executed =>
    rw [← initial_world function world slice frame initialized]
    exact executes_projects function frame flow executed

theorem executes_deterministic (function : Function) (frame : Frame) (left right : Flow)
    (first : Executes function frame left) (second : Executes function frame right) : left = right := by
  cases first with
  | start next left evaluated loop =>
    cases second with
    | start other right secondEval secondLoop =>
      have same := Flow.normal.inj (evaluated.symm.trans secondEval)
      subst other
      exact loopRuns_deterministic _ _ _ _ _ loop secondLoop
    | early right secondEval stopped =>
      have same := evaluated.symm.trans secondEval
      cases same
      cases stopped
  | early left evaluated stopped =>
    cases second with
    | start next right secondEval loop =>
      have same := secondEval.symm.trans evaluated
      cases same
      cases stopped
    | early right secondEval stopped => exact evaluated.symm.trans secondEval

end FormalProof4FHE.HasteBoots.NativeByteLoopLLBC
