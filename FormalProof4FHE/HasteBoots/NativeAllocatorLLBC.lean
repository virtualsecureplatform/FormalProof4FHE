module
public import FormalProof4FHE.HasteBoots.NativeRecordCallValues
public import FormalProof4FHE.HasteBoots.NativeAllocatorExecution
@[expose] public section

/-! Allocation-capable finite bodies embed the existing record evaluator.
Native allocator/shim ABI and compiler correspondence remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeAllocatorLLBC
open NativeRecordLLBC (Frame Flow Operand)
open NativeRecordValues (Ty Value)
open NativePointerStorage (Address)
open NativeByteDropCalls (Classification)

inductive Body where
  | done
  | legacy (body : NativeRecordLLBC.Body) (next : Body)
  | call (name : String) (classification : Classification) (types : List Ty) (argCount target : Nat)
      (args : List Operand) (callee unwind next : Body)
  | switchBoolean (test : Operand) (yes no next : Body)
  | switchUsize (test : Operand) (value : NativeWord64Memory.Word) (yes no next : Body)
  | matchChoice (index : Nat) (path : NativeRecordValues.Path) (tag : Nat) (left right next : Body)
  | allocate (symbol : NativeAllocatorExecution.Symbol) (outcome : Option Address)
      (alignmentTag enumTag target : Nat) (args : List Operand) (next : Body)
  deriving DecidableEq

structure Function where
  name : String
  classification : Classification
  types : List Ty
  argCount : Nat
  body : Body
  deriving DecidableEq

def decodeRequest (alignmentTag enumTag : Nat) : List Value → Option (NativeWord64Memory.Word × NativeWord64Memory.Word)
  | [.scalar (.usize size),.record actual (.pair (.enumeration actualEnum alignment) (.scalar .unit))] =>
    if actual = alignmentTag ∧ actualEnum = enumTag then some (size,alignment) else none
  | _ => none

def eval : Body → Frame → Flow
  | .done, frame => .normal frame
  | .legacy body next, frame => match NativeRecordLLBC.eval body frame with
    | .normal changed => eval next changed
    | flow => flow
  | .call _ _ types argCount target args callee unwind next, frame => match NativeRecordLLBC.evalArgs frame args with
    | none => .invalid frame.world
    | some (values,caller) => match NativeRecordLLBC.initial types argCount values caller.world with
      | none => .invalid caller.world
      | some entered => match NativeRecordLLBC.settle entered.world (eval callee entered) with
        | .returned value world => match NativeRecordLLBC.write {caller with world} target value with
          | none => .invalid world
          | some changed => eval next changed
        | .unwind world => eval unwind {caller with world}
        | .invalid world => .invalid world
        | .unsupported source world => .unsupported source world
        | .normal changed => .invalid changed.world
  | .switchBoolean test yes no next, frame => match NativeRecordLLBC.evalBooleanOperand frame test with
    | none => .invalid frame.world
    | some (condition,caller) =>
      let branch := if condition then eval yes caller else eval no caller
      match branch with | .normal changed => eval next changed | flow => flow
  | .switchUsize test expected yes no next, frame => match NativeRecordLLBC.evalOperand frame test with
    | some (.scalar (.usize actual),caller) =>
      let branch := if actual = expected then eval yes caller else eval no caller
      match branch with | .normal changed => eval next changed | flow => flow
    | _ => .invalid frame.world
  | .matchChoice index path tag left right next, frame => match NativeRecordLLBC.selectChoice frame index path tag with
    | none => .invalid frame.world
    | some side =>
      let branch := if side then eval right frame else eval left frame
      match branch with | .normal changed => eval next changed | flow => flow
  | .allocate symbol outcome alignmentTag enumTag target args next, frame => match NativeRecordLLBC.evalArgs frame args with
    | none => .invalid frame.world
    | some (values,caller) => match decodeRequest alignmentTag enumTag values with
      | none => .invalid caller.world
      | some (size,alignment) => match NativeAllocatorExecution.run caller.world symbol outcome size alignment with
        | .invalid world => .invalid world
        | .value value world => match NativeRecordLLBC.write {caller with world} target (.scalar value) with
          | none => .invalid world
          | some changed => eval next changed

def invokeValues (function : Function) (world : NativeReferenceMachine.State) (args : List Value) : Flow :=
  match NativeRecordLLBC.initial function.types function.argCount args world with
  | none => .invalid world
  | some entered => NativeRecordLLBC.settle world (eval function.body entered)

def invoke (function : Function) (world : NativeReferenceMachine.State) (args : List NativeRecordLLBC.Input) : Flow :=
  match NativeRecordLLBC.decodeArgs world args with
  | none => .invalid world
  | some values => invokeValues function world values

def resume (caller : Frame) (target : Nat) (unwind next : Body) : Flow → Flow
  | .returned value world => match NativeRecordLLBC.write {caller with world} target value with
    | none => .invalid world
    | some changed => eval next changed
  | .unwind world => eval unwind {caller with world}
  | .invalid world => .invalid world
  | .unsupported source world => .unsupported source world
  | .normal changed => .invalid changed.world

def continueWith (next : Body) : Flow → Flow
  | .normal changed => eval next changed
  | flow => flow

theorem eval_call (function : Function) (caller : Frame) (target : Nat) (args : List Operand) (unwind next : Body) :
    eval (.call function.name function.classification function.types function.argCount target args function.body unwind next) caller =
      match NativeRecordLLBC.evalArgs caller args with
      | none => .invalid caller.world
      | some (values,consumed) => resume consumed target unwind next (invokeValues function consumed.world values) := by
  cases prepared : NativeRecordLLBC.evalArgs caller args with
  | none => simp only [eval,prepared]
  | some pair =>
    rcases pair with ⟨values,consumed⟩
    cases initialized : NativeRecordLLBC.initial function.types function.argCount values consumed.world with
    | none => simp only [eval,prepared,initialized,invokeValues,resume]
    | some entered =>
      have same := NativeRecordLLBC.initial_world function.types function.argCount values consumed.world entered initialized
      simp only [eval,prepared,initialized,invokeValues,same]
      rfl

theorem switch_usize_false {frame caller : Frame} {operand : Operand} {word : NativeWord64Memory.Word}
    (expected : NativeWord64Memory.Word) (yes no next : Body)
    (selected : NativeRecordLLBC.evalOperand frame operand = some (.scalar (.usize word),caller))
    (different : word ≠ expected) :
    eval (.switchUsize operand expected yes no next) frame = continueWith next (eval no caller) := by
  simp only [eval,selected,ite_eq_right different,continueWith]

theorem continue_done (flow : Flow) : continueWith .done flow = flow := by
  cases flow <;> rfl

theorem legacy_normal {frame changed : Frame} {body : NativeRecordLLBC.Body} (next : Body)
    (executed : NativeRecordLLBC.eval body frame = .normal changed) :
    eval (.legacy body next) frame = eval next changed := by
  simp only [eval,executed]

theorem legacy_done (frame : Frame) (body : NativeRecordLLBC.Body) :
    eval (.legacy body .done) frame = NativeRecordLLBC.eval body frame := by
  cases actual : NativeRecordLLBC.eval body frame <;> simp only [eval,actual]

theorem decode_request_exact (alignmentTag enumTag : Nat) (size alignment : NativeWord64Memory.Word) :
    decodeRequest alignmentTag enumTag [.scalar (.usize size),
      .record alignmentTag (.pair (.enumeration enumTag alignment) (.scalar .unit))] = some (size,alignment) := by
  simp only [decodeRequest,and_self,ite_true]

theorem invokeValues_initialized (function : Function) (world : NativeReferenceMachine.State)
    (args : List Value) (entered : Frame)
    (initialized : NativeRecordLLBC.initial function.types function.argCount args world = some entered) :
    invokeValues function world args = NativeRecordLLBC.settle entered.world (eval function.body entered) := by
  have same := NativeRecordLLBC.initial_world function.types function.argCount args world entered initialized
  simp only [invokeValues,initialized]
  rw [same]

/-- Every outcome, including failed allocation or failed result storage, retains
its actual checked reference-machine execution prefix. -/
theorem eval_projects (body : Body) (frame : Frame) :
    NativeReferenceMachine.Runs frame.world (eval body frame).world := by
  induction body generalizing frame with
  | done => exact .refl _
  | legacy body next nextIH =>
    have first := NativeRecordLLBC.eval_projects body frame
    cases actual : NativeRecordLLBC.eval body frame with
    | normal changed =>
      rw [actual] at first
      simp only [eval,actual]
      exact NativeReferenceMachine.runs_trans _ _ _ first (nextIH changed)
    | returned value world => simpa only [eval,actual,Flow.world] using first
    | unwind world => simpa only [eval,actual,Flow.world] using first
    | invalid world => simpa only [eval,actual,Flow.world] using first
    | unsupported source world => simpa only [eval,actual,Flow.world] using first
  | switchBoolean operand yes no next yesIH noIH nextIH =>
    cases selected : NativeRecordLLBC.evalBooleanOperand frame operand with
    | none => simp only [eval,selected,Flow.world]; exact .refl _
    | some result =>
      rcases result with ⟨condition,caller⟩
      have same := NativeRecordLLBC.evalBooleanOperand_world frame caller operand condition selected
      have first : NativeReferenceMachine.Runs frame.world
          (if condition then eval yes caller else eval no caller).world := by
        rw [← same]
        cases condition
        · exact noIH caller
        · exact yesIH caller
      simp only [eval,selected]
      generalize chosen : (if condition then eval yes caller else eval no caller) = branch at first ⊢
      cases branch with
      | normal changed => exact NativeReferenceMachine.runs_trans _ _ _ first (nextIH changed)
      | returned value world => exact first
      | unwind world => exact first
      | invalid world => exact first
      | unsupported source world => exact first
  | matchChoice index path tag left right next leftIH rightIH nextIH =>
    cases selected : NativeRecordLLBC.selectChoice frame index path tag with
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
    cases selected : NativeRecordLLBC.evalOperand frame operand with
    | none => simp only [eval, selected, Flow.world]; exact .refl _
    | some result =>
      rcases result with ⟨value,caller⟩
      have same := NativeRecordLLBC.evalOperand_world frame caller operand value selected
      cases value with
      | pair left right => simp only [eval, selected, Flow.world]; exact .refl _
      | choice side fields => simp only [eval, selected, Flow.world]; exact .refl _
      | record tag fields => simp only [eval, selected, Flow.world]; exact .refl _
      | enumeration tag value => simp only [eval, selected, Flow.world]; exact .refl _
      | boolean value => simp only [eval, selected, Flow.world]; exact .refl _
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
  | call name classification types argCount target args callee unwind next calleeIH unwindIH nextIH =>
    cases selected : NativeRecordLLBC.evalArgs frame args with
    | none => simp only [eval, selected, Flow.world]; exact .refl _
    | some result =>
      rcases result with ⟨values,caller⟩
      have same := NativeRecordLLBC.evalArgs_world frame caller args values selected
      cases initialized : NativeRecordLLBC.initial types argCount values caller.world with
      | none => simp only [eval, selected, initialized, Flow.world]; rw [same]; exact .refl _
      | some entered =>
        have entryWorld := NativeRecordLLBC.initial_world types argCount values caller.world entered initialized
        have callPrefix : NativeReferenceMachine.Runs frame.world entered.world := by
          rw [entryWorld, same]
          exact .refl _
        have first := NativeReferenceMachine.runs_trans _ _ _ callPrefix
          (NativeReferenceMachine.runs_trans _ _ _ (calleeIH entered)
            (NativeRecordLLBC.settle_projects entered.world (eval callee entered)))
        cases returned : NativeRecordLLBC.settle entered.world (eval callee entered) with
        | normal changed => simpa only [eval, selected, initialized, returned, Flow.world] using first
        | invalid world => simpa only [eval, selected, initialized, returned, Flow.world] using first
        | unsupported source world => simpa only [eval, selected, initialized, returned, Flow.world] using first
        | unwind world =>
          rw [returned] at first
          simp only [eval, selected, initialized, returned]
          exact NativeReferenceMachine.runs_trans _ _ _ first (unwindIH {caller with world})
        | returned output world =>
          rw [returned] at first
          cases written : NativeRecordLLBC.write {caller with world} target output with
          | none => simpa only [eval, selected, initialized, returned, written, Flow.world] using first
          | some changed =>
            have second := nextIH changed
            rw [NativeRecordLLBC.write_world {caller with world} changed target output written] at second
            simp only [eval, selected, initialized, returned, written]
            exact NativeReferenceMachine.runs_trans _ _ _ first second

  | allocate symbol outcome alignmentTag enumTag target args next nextIH =>
    cases selected : NativeRecordLLBC.evalArgs frame args with
    | none => simp only [eval,selected,Flow.world]; exact .refl _
    | some result =>
      rcases result with ⟨values,caller⟩
      have same := NativeRecordLLBC.evalArgs_world frame caller args values selected
      cases decoded : decodeRequest alignmentTag enumTag values with
      | none => simp only [eval,selected,decoded,Flow.world]; rw [same]; exact .refl _
      | some request =>
        rcases request with ⟨size,alignment⟩
        have first : NativeReferenceMachine.Runs frame.world (NativeAllocatorExecution.run caller.world symbol outcome size alignment).world := by
          rw [← same]
          exact NativeAllocatorExecution.run_projects caller.world symbol outcome size alignment
        cases actual : NativeAllocatorExecution.run caller.world symbol outcome size alignment with
        | invalid world => simpa only [eval,selected,decoded,actual,NativeRawVecFields.Result.world,Flow.world] using first
        | value value world =>
          rw [actual] at first
          cases written : NativeRecordLLBC.write {caller with world} target (.scalar value) with
          | none => simpa only [eval,selected,decoded,actual,written,NativeRawVecFields.Result.world,Flow.world] using first
          | some changed =>
            have later := nextIH changed
            rw [NativeRecordLLBC.write_world {caller with world} changed target (.scalar value) written] at later
            simp only [eval,selected,decoded,actual,written]
            exact NativeReferenceMachine.runs_trans _ _ _ first later

theorem invokeValues_projects (function : Function) (world : NativeReferenceMachine.State) (args : List Value) :
    NativeReferenceMachine.Runs world (invokeValues function world args).world := by
  cases initialized : NativeRecordLLBC.initial function.types function.argCount args world with
  | none => simp only [invokeValues,initialized,Flow.world]; exact .refl _
  | some entered =>
    have same := NativeRecordLLBC.initial_world function.types function.argCount args world entered initialized
    have first := NativeReferenceMachine.runs_trans _ _ _ (eval_projects function.body entered)
      (NativeRecordLLBC.settle_projects world (eval function.body entered))
    simpa only [invokeValues,initialized,same] using first

theorem invoke_projects (function : Function) (world : NativeReferenceMachine.State) (args : List NativeRecordLLBC.Input) :
    NativeReferenceMachine.Runs world (invoke function world args).world := by
  cases decoded : NativeRecordLLBC.decodeArgs world args with
  | none => simp only [invoke,decoded,Flow.world]; exact .refl _
  | some values => simpa only [invoke,decoded] using invokeValues_projects function world values

theorem invoke_reachable (function : Function) (world : NativeReferenceMachine.State) (args : List NativeRecordLLBC.Input)
    (reachable : NativeReferenceMachine.Reachable world) : NativeReferenceMachine.Reachable (invoke function world args).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (invoke_projects function world args)

end FormalProof4FHE.HasteBoots.NativeAllocatorLLBC
