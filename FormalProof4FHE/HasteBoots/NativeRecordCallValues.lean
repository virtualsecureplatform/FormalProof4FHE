module
public import FormalProof4FHE.HasteBoots.NativeRecordHeapBounds
@[expose] public section

/-! Typed callee execution and caller resumption, factored from the existing
finite-body evaluator. Initial argument checks and cleanup retain their original
semantics. This is not a native calling-convention or lifetime correspondence. -/
namespace FormalProof4FHE.HasteBoots.NativeRecordCallValues
open NativeRecordLLBC (Frame Flow Function Body Operand Input)
open NativeRecordValues (Value)
open NativeReferenceMachine (State)

/-- Internal callers already hold checked aggregate values. -/
def invokeValues (function : Function) (world : State) (args : List Value) : Flow :=
  match NativeRecordLLBC.initial function.types function.argCount args world with
  | none => .invalid world
  | some entered => NativeRecordLLBC.settle world (NativeRecordLLBC.eval function.body entered)

/-- Resume exactly the caller's normal or unwind successor. -/
def resume (caller : Frame) (target : Nat) (unwind next : Body) : Flow → Flow
  | .returned value world => match NativeRecordLLBC.write {caller with world} target value with
    | none => .invalid world
    | some changed => NativeRecordLLBC.eval next changed
  | .unwind world => NativeRecordLLBC.eval unwind {caller with world}
  | .invalid world => .invalid world
  | .unsupported source world => .unsupported source world
  | .normal changed => .invalid changed.world

theorem invoke_eq (function : Function) (world : State) (args : List Input) :
    NativeRecordLLBC.invoke function world args =
      match NativeRecordLLBC.decodeArgs world args with
      | none => .invalid world
      | some values => invokeValues function world values := by
  rfl

theorem invokeValues_initialized (function : Function) (world : State) (args : List Value) (entered : Frame)
    (initialized : NativeRecordLLBC.initial function.types function.argCount args world = some entered) :
    invokeValues function world args = NativeRecordLLBC.settle entered.world (NativeRecordLLBC.eval function.body entered) := by
  have same := NativeRecordLLBC.initial_world function.types function.argCount args world entered initialized
  simp only [invokeValues, initialized]
  rw [same]

theorem eval_call (function : Function) (caller : Frame) (target : Nat) (args : List Operand) (unwind next : Body) :
    NativeRecordLLBC.eval (.call function.name function.classification function.types function.argCount target args
      function.body unwind next) caller =
      match NativeRecordLLBC.evalArgs caller args with
      | none => .invalid caller.world
      | some (values,consumed) => resume consumed target unwind next (invokeValues function consumed.world values) := by
  cases prepared : NativeRecordLLBC.evalArgs caller args with
  | none => simp only [NativeRecordLLBC.eval, prepared]
  | some pair =>
    rcases pair with ⟨values,consumed⟩
    cases initialized : NativeRecordLLBC.initial function.types function.argCount values consumed.world with
    | none => simp only [NativeRecordLLBC.eval,prepared,initialized,invokeValues,resume]
    | some entered =>
      have same := NativeRecordLLBC.initial_world function.types function.argCount values consumed.world entered initialized
      simp only [NativeRecordLLBC.eval,prepared,initialized,invokeValues,same]
      rfl

theorem invokeValues_projects (function : Function) (world : State) (args : List Value) :
    NativeReferenceMachine.Runs world (invokeValues function world args).world := by
  cases initialized : NativeRecordLLBC.initial function.types function.argCount args world with
  | none => simp only [invokeValues,initialized,Flow.world]; exact .refl _
  | some entered =>
    have same := NativeRecordLLBC.initial_world function.types function.argCount args world entered initialized
    have body := NativeRecordLLBC.eval_projects function.body entered
    rw [same] at body
    simpa only [invokeValues,initialized] using NativeReferenceMachine.runs_trans _ _ _ body
      (NativeRecordLLBC.settle_projects world (NativeRecordLLBC.eval function.body entered))

theorem invokeValues_loss (function : Function) (world : State) (args : List Value) :
    NativeHeapLoss.Loss world (invokeValues function world args).world (NativeRecordLLBC.deallocationBudget function.body) := by
  cases initialized : NativeRecordLLBC.initial function.types function.argCount args world with
  | none => simp only [invokeValues,initialized,Flow.world]; exact .refl _ _
  | some entered =>
    have same := NativeRecordLLBC.initial_world function.types function.argCount args world entered initialized
    have body := NativeRecordLLBC.eval_loss function.body entered
    rw [same] at body
    simpa only [invokeValues,initialized] using body.suffix (NativeRecordLLBC.settle_heap_projects world _)

/-- The reserved receiver is activated after the remaining arguments, then
moved into the callee. Every failure retains its actual execution prefix. -/
theorem eval_twoPhase_call (function : Function) (caller : Frame) (parent reserved target : Nat)
    (path : NativeRecordValues.Path) (rest : List Operand) (unwind next : Body) :
    NativeRecordLLBC.eval (.twoPhaseRawVecCall parent path reserved function.name function.classification
      function.types function.argCount target rest function.body unwind next) caller =
      if NativeRecordLLBC.pendingMutableSlot caller reserved then
        match NativeRecordLLBC.reserveRawVec caller parent path with
        | .invalid world => .invalid world
        | .value reservation prepared => match NativeRecordLLBC.evalArgs {caller with world := prepared} rest with
          | none => .invalid prepared
          | some (values,arguments) => match NativeRawVecMutBorrow.activate arguments.world reservation with
            | .invalid world => .invalid world
            | .value reference world => match NativeRecordLLBC.write {arguments with world} reserved (.scalar reference) with
              | none => .invalid world
              | some written => match NativeRecordLLBC.evalOperand written (.move reserved []) with
                | none => .invalid world
                | some (argument,consumed) => resume consumed target unwind next
                    (invokeValues function consumed.world (argument :: values))
      else .invalid caller.world := by
  by_cases pending : NativeRecordLLBC.pendingMutableSlot caller reserved = true
  · cases reservation : NativeRecordLLBC.reserveRawVec caller parent path with
    | invalid world => simp only [NativeRecordLLBC.eval,pending,ite_true,reservation]
    | value value prepared =>
      cases arguments : NativeRecordLLBC.evalArgs {caller with world := prepared} rest with
      | none => simp only [NativeRecordLLBC.eval,pending,ite_true,reservation,arguments]
      | some pair =>
        rcases pair with ⟨values,argumentFrame⟩
        cases activated : NativeRawVecMutBorrow.activate argumentFrame.world value with
        | invalid world => simp only [NativeRecordLLBC.eval,pending,ite_true,reservation,arguments,activated]
        | value reference world =>
          cases written : NativeRecordLLBC.write {argumentFrame with world} reserved (.scalar reference) with
          | none => simp only [NativeRecordLLBC.eval,pending,ite_true,reservation,arguments,activated,written]
          | some writtenFrame =>
            cases moved : NativeRecordLLBC.evalOperand writtenFrame (.move reserved []) with
            | none => simp only [NativeRecordLLBC.eval,pending,ite_true,reservation,arguments,activated,written,moved]
            | some pair =>
              rcases pair with ⟨argument,consumed⟩
              cases initialized : NativeRecordLLBC.initial function.types function.argCount (argument :: values) consumed.world with
              | none => simp only [NativeRecordLLBC.eval,pending,ite_true,reservation,arguments,activated,written,moved,initialized,invokeValues,resume]
              | some entered =>
                have same := NativeRecordLLBC.initial_world function.types function.argCount (argument :: values) consumed.world entered initialized
                simp only [NativeRecordLLBC.eval,pending,ite_true,reservation,arguments,activated,written,moved,initialized,invokeValues,same]
                rfl
  · simp only [NativeRecordLLBC.eval,pending,Bool.false_eq_true,ite_false]

theorem body_zero_heap (body : Body) (frame : Frame) (budget : NativeRecordLLBC.deallocationBudget body = 0) :
    NativeHeapFrame.Runs frame.world (NativeRecordLLBC.eval body frame).world := by
  have bound := NativeRecordLLBC.eval_loss body frame
  rw [budget] at bound
  have bounded := bound.bounded
  have growth := bound.no_growth
  exact ⟨bound.unchanged (by omega)⟩

theorem resume_heap (caller : Frame) (target : Nat) (unwind next : Body) (flow : Flow)
    (unwindBudget : NativeRecordLLBC.deallocationBudget unwind = 0)
    (nextBudget : NativeRecordLLBC.deallocationBudget next = 0) :
    NativeHeapFrame.Runs flow.world (resume caller target unwind next flow).world := by
  cases flow with
  | returned value world =>
    cases written : NativeRecordLLBC.write {caller with world} target value with
    | none => simp only [resume,written,Flow.world]; exact .refl _
    | some changed =>
      have frame := body_zero_heap next changed nextBudget
      have same := NativeRecordLLBC.write_world {caller with world} changed target value written
      refine ⟨?_⟩
      simpa only [resume,written,Flow.world,same] using frame.heap_eq
  | unwind world => exact body_zero_heap unwind {caller with world} unwindBudget
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _
  | normal changed => exact .refl _

theorem eval_mut_borrow (frame : Frame) (index : Nat) (path : NativeRecordValues.Path) (value : NativeSliceLLBC.Value)
    (selected : NativeRecordLLBC.read frame index path = some (.scalar value)) :
    NativeRecordLLBC.evalRawVecMutBorrow frame index path =
      match NativeRawVecMutBorrow.immediate frame.world value with
      | .invalid world => .invalid world
      | .value output world => .value (.scalar output) {frame with world} := by
  simp only [NativeRecordLLBC.evalRawVecMutBorrow,NativeRecordLLBC.reserveRawVec,selected,NativeRawVecMutBorrow.immediate]
  cases actual : NativeRawVecMutBorrow.reserve frame.world value with
  | invalid world => rfl
  | value reservation world => cases NativeRawVecMutBorrow.activate world reservation <;> rfl

/-- Unit callees either return unit or retain a rejected execution prefix. -/
def UnitResult : Flow → Prop
  | .returned value _ => value = .scalar .unit
  | .invalid _ => True
  | _ => False

theorem UnitResult.settle (entered : State) (flow : Flow) (checked : UnitResult flow) :
    UnitResult (NativeRecordLLBC.settle entered flow) := by
  cases flow with
  | returned value world =>
    change value = .scalar .unit at checked
    subst value
    simp only [NativeRecordLLBC.settle,NativeReferenceCleanup.settleUnit]
    split <;> simp only [UnitResult]
  | invalid world => trivial
  | normal changed => cases checked
  | unwind world => cases checked
  | unsupported source world => cases checked

end FormalProof4FHE.HasteBoots.NativeRecordCallValues
