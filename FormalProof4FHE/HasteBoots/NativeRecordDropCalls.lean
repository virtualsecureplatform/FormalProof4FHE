module
public import FormalProof4FHE.HasteBoots.NativeRecordLLBC
@[expose] public section

/-! Composition of retained finite bodies and typed slice-loop bodies.
Classification is retained as data; interpreting a retained foreign-classified
body does not establish native foreign-call or compiler correctness. Normal unit
return cleanup is an explicit ghost composition, not a Rust lifetime theorem. -/
namespace FormalProof4FHE.HasteBoots.NativeRecordDropCalls
open NativeReferenceMachine (State)
open NativeRecordLLBC (Frame Flow Operand Input)
open NativeRecordValues (Value Ty)
open NativeByteDropCalls (Classification)
open NativeByteSliceIndex (Slice)

inductive Code where
  | scope (body next : Code)
  | done
  | native (body : NativeRecordLLBC.Body) (next : Code)
  | call (name : String) (classification : Classification) (types : List Ty) (argCount target : Nat)
      (args : List Operand) (callee unwind next : Code)
  | loop (classification : Classification) (function : NativeByteLoopLLBC.Function)
  deriving DecidableEq

structure Definition where
  name : String
  classification : Classification
  types : List Ty
  argCount : Nat
  code : Code
  deriving DecidableEq

def Flow.terminal : Flow → Bool
  | .normal _ => false
  | _ => true

/-- Callee arguments and local slots are initialized from actual evaluated
operands. The source caller frame keeps its moves across the call. -/
def prepareCall (frame : Frame) (types : List Ty) (argCount : Nat) (args : List Operand) : Option (Frame × Frame) :=
  (NativeRecordLLBC.evalArgs frame args).bind (fun (values, caller) =>
    (NativeRecordLLBC.initial types argCount values caller.world).map (fun callee => (caller, callee)))

inductive Resume where
  | next (frame : Frame)
  | unwind (frame : Frame)
  | invalid (world : State)
  | unsupported (source : String) (world : State)
  deriving DecidableEq

def Resume.world : Resume → State
  | .next frame | .unwind frame => frame.world
  | .invalid world | .unsupported _ world => world

/-- Settle only a normal unit return, using the actual call-entry world. -/
def resumeCall (entered : State) (caller : Frame) (target : Nat) : Flow → Resume
  | .returned value current =>
    let settled := NativeRecordLLBC.settle entered (.returned value current)
    match settled with
    | .returned value world => match NativeRecordLLBC.write {caller with world} target value with
      | some frame => .next frame
      | none => .invalid world
    | .invalid world => .invalid world
    | _ => .invalid settled.world
  | .unwind world => .unwind {caller with world}
  | .invalid world => .invalid world
  | .unsupported source world => .unsupported source world
  | .normal frame => .invalid frame.world

def loopArgument (frame : Frame) : Option Slice :=
  (NativeRecordLLBC.read frame 1 []).bind (fun value => match value with
    | .scalar (.reference true reference length) => some ⟨reference,length⟩
    | _ => none)

def fromLoop : NativeByteLoopLLBC.Flow → Flow
  | .returned .unit frame => .returned (.scalar .unit) frame.world
  | .unwind frame => .unwind frame.world
  | .invalid frame => .invalid frame.world
  | flow => .invalid flow.world

/-- Explicit ghost cleanup of loans created while preparing and executing a
call. Source local slots are preserved; incoming loans are never selected. -/
def resumeScope (entered : State) : Flow → Flow
  | .normal frame =>
    let cleaned := NativeReferenceCleanup.closeScope entered frame.world
    if cleaned.pending.isEmpty then .normal {frame with world := cleaned.world} else .invalid cleaned.world
  | flow => flow

inductive Runs : Code → Frame → Flow → Prop where
  | scopeNext (body next : Code) (frame changed : Frame) (returned flow : Flow)
      (executed : Runs body frame returned) (settled : resumeScope frame.world returned = .normal changed)
      (later : Runs next changed flow) : Runs (.scope body next) frame flow
  | scopeStop (body next : Code) (frame : Frame) (returned flow : Flow)
      (executed : Runs body frame returned) (settled : resumeScope frame.world returned = flow)
      (stopped : Flow.terminal flow = true) : Runs (.scope body next) frame flow
  | done (frame : Frame) : Runs .done frame (.normal frame)
  | nativeNext (body : NativeRecordLLBC.Body) (next : Code) (frame changed : Frame) (flow : Flow)
      (evaluated : NativeRecordLLBC.eval body frame = .normal changed) (later : Runs next changed flow) :
      Runs (.native body next) frame flow
  | nativeStop (body : NativeRecordLLBC.Body) (next : Code) (frame : Frame) (flow : Flow)
      (evaluated : NativeRecordLLBC.eval body frame = flow) (stopped : Flow.terminal flow = true) :
      Runs (.native body next) frame flow
  | callInvalid (name : String) (classification : Classification) (types : List Ty) (argCount target : Nat)
      (args : List Operand) (callee unwind next : Code) (frame : Frame)
      (rejected : prepareCall frame types argCount args = none) :
      Runs (.call name classification types argCount target args callee unwind next) frame (.invalid frame.world)
  | callNext (name : String) (classification : Classification) (types : List Ty) (argCount target : Nat)
      (args : List Operand) (callee unwind next : Code) (frame caller entered changed : Frame) (returned flow : Flow)
      (prepared : prepareCall frame types argCount args = some (caller, entered))
      (called : Runs callee entered returned) (resumed : resumeCall entered.world caller target returned = .next changed)
      (later : Runs next changed flow) : Runs (.call name classification types argCount target args callee unwind next) frame flow
  | callUnwind (name : String) (classification : Classification) (types : List Ty) (argCount target : Nat)
      (args : List Operand) (callee unwind next : Code) (frame caller entered changed : Frame) (returned flow : Flow)
      (prepared : prepareCall frame types argCount args = some (caller, entered))
      (called : Runs callee entered returned) (resumed : resumeCall entered.world caller target returned = .unwind changed)
      (later : Runs unwind changed flow) : Runs (.call name classification types argCount target args callee unwind next) frame flow
  | callStopped (name : String) (classification : Classification) (types : List Ty) (argCount target : Nat)
      (args : List Operand) (callee unwind next : Code) (frame caller entered : Frame) (returned : Flow) (world : State)
      (prepared : prepareCall frame types argCount args = some (caller, entered))
      (called : Runs callee entered returned) (resumed : resumeCall entered.world caller target returned = .invalid world) :
      Runs (.call name classification types argCount target args callee unwind next) frame (.invalid world)
  | callUnsupported (name : String) (classification : Classification) (types : List Ty) (argCount target : Nat)
      (args : List Operand) (callee unwind next : Code) (frame caller entered : Frame) (returned : Flow) (source : String) (world : State)
      (prepared : prepareCall frame types argCount args = some (caller, entered))
      (called : Runs callee entered returned) (resumed : resumeCall entered.world caller target returned = .unsupported source world) :
      Runs (.call name classification types argCount target args callee unwind next) frame (.unsupported source world)
  | loopArgumentInvalid (classification : Classification) (function : NativeByteLoopLLBC.Function) (frame : Frame)
      (rejected : loopArgument frame = none) : Runs (.loop classification function) frame (.invalid frame.world)
  | loopInitialInvalid (classification : Classification) (function : NativeByteLoopLLBC.Function) (frame : Frame) (slice : Slice)
      (argument : loopArgument frame = some slice) (rejected : NativeByteLoopLLBC.initial function frame.world slice = none) :
      Runs (.loop classification function) frame (.invalid frame.world)
  | loopRun (classification : Classification) (function : NativeByteLoopLLBC.Function) (frame : Frame) (slice : Slice)
      (native : NativeByteLoopLLBC.Frame) (flow : NativeByteLoopLLBC.Flow)
      (argument : loopArgument frame = some slice) (initialized : NativeByteLoopLLBC.initial function frame.world slice = some native)
      (executed : NativeByteLoopLLBC.Executes function native flow) :
      Runs (.loop classification function) frame (fromLoop flow)

inductive Invokes (function : Definition) (world : State) (args : List Input) : Flow → Prop where
  | argumentsInvalid (rejected : NativeRecordLLBC.decodeArgs world args = none) : Invokes function world args (.invalid world)
  | initialInvalid (values : List Value) (decoded : NativeRecordLLBC.decodeArgs world args = some values)
      (rejected : NativeRecordLLBC.initial function.types function.argCount values world = none) : Invokes function world args (.invalid world)
  | run (values : List Value) (frame : Frame) (flow : Flow)
      (decoded : NativeRecordLLBC.decodeArgs world args = some values)
      (initialized : NativeRecordLLBC.initial function.types function.argCount values world = some frame)
      (executed : Runs function.code frame flow) :
      Invokes function world args (NativeRecordLLBC.settle world flow)

theorem prepareCall_worlds (frame caller callee : Frame) (types : List Ty) (argCount : Nat) (args : List Operand)
    (prepared : prepareCall frame types argCount args = some (caller, callee)) :
    caller.world = frame.world ∧ callee.world = frame.world := by
  simp only [prepareCall, Option.bind_eq_some_iff, Option.map_eq_some_iff] at prepared
  obtain ⟨⟨values, evaluated⟩, evaluatedEq, initialized, initialEq, same⟩ := prepared
  cases same
  have callerWorld := NativeRecordLLBC.evalArgs_world frame evaluated args values evaluatedEq
  exact ⟨callerWorld, (NativeRecordLLBC.initial_world types argCount values evaluated.world _ initialEq).trans callerWorld⟩

theorem fromLoop_world (flow : NativeByteLoopLLBC.Flow) : (fromLoop flow).world = flow.world := by
  cases flow with
  | returned value frame => cases value <;> rfl
  | normal frame => rfl
  | unwind frame => rfl
  | invalid frame => rfl
  | breaking frame => rfl
  | continuing frame => rfl

theorem resumeCall_projects (entered : State) (caller : Frame) (target : Nat) (flow : Flow) :
    NativeReferenceMachine.Runs flow.world (resumeCall entered caller target flow).world := by
  cases flow with
  | returned value current =>
    have first := NativeRecordLLBC.settle_projects entered (.returned value current)
    simp only [resumeCall]
    cases actual : NativeRecordLLBC.settle entered (.returned value current) with
    | returned output world =>
      rw [actual] at first
      simp only []
      cases written : NativeRecordLLBC.write {caller with world} target output with
      | none => exact first
      | some frame =>
        have same := NativeRecordLLBC.write_world {caller with world} frame target output written
        change NativeReferenceMachine.Runs current frame.world
        rw [same]
        exact first
    | invalid world => simpa only [actual, NativeRecordLLBC.Flow.world, Resume.world] using first
    | normal frame => simpa only [actual, NativeRecordLLBC.Flow.world, Resume.world] using first
    | unwind world => simpa only [actual, NativeRecordLLBC.Flow.world, Resume.world] using first
    | unsupported source world => simpa only [actual, NativeRecordLLBC.Flow.world, Resume.world] using first
  | unwind world => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _
  | normal frame => exact .refl _

theorem resumeScope_projects (entered : State) (flow : Flow) :
    NativeReferenceMachine.Runs flow.world (resumeScope entered flow).world := by
  cases flow with
  | normal frame =>
    have first := NativeReferenceCleanup.closeScope_projects entered frame.world
    simp only [resumeScope]
    split <;> exact first
  | returned value world => exact .refl _
  | unwind world => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _

theorem runs_projects (code : Code) (frame : Frame) (flow : Flow) (ran : Runs code frame flow) :
    NativeReferenceMachine.Runs frame.world flow.world := by
  induction ran with
  | scopeNext body next frame changed returned flow executed settled later firstIH laterIH =>
    have cleanupRun := resumeScope_projects frame.world returned
    rw [settled] at cleanupRun
    exact NativeReferenceMachine.runs_trans _ _ _ firstIH (NativeReferenceMachine.runs_trans _ _ _ cleanupRun laterIH)
  | scopeStop body next frame returned flow executed settled stopped firstIH =>
    have cleanupRun := resumeScope_projects frame.world returned
    rw [settled] at cleanupRun
    exact NativeReferenceMachine.runs_trans _ _ _ firstIH cleanupRun
  | done frame => exact .refl _
  | nativeNext body next frame changed flow evaluated later ih =>
    have first := NativeRecordLLBC.eval_projects body frame
    rw [evaluated] at first
    exact NativeReferenceMachine.runs_trans _ _ _ first ih
  | nativeStop body next frame flow evaluated stopped =>
    have first := NativeRecordLLBC.eval_projects body frame
    rw [evaluated] at first
    exact first
  | callInvalid => exact .refl _
  | callNext name classification types argCount target args callee unwind next frame caller entered changed returned flow prepared called resumed later calledIH laterIH =>
    have same := (prepareCall_worlds frame caller entered types argCount args prepared).2
    have first : NativeReferenceMachine.Runs frame.world returned.world := by rw [← same]; exact calledIH
    have resumedRun := resumeCall_projects entered.world caller target returned
    rw [resumed] at resumedRun
    exact NativeReferenceMachine.runs_trans _ _ _ first (NativeReferenceMachine.runs_trans _ _ _ resumedRun laterIH)
  | callUnwind name classification types argCount target args callee unwind next frame caller entered changed returned flow prepared called resumed later calledIH laterIH =>
    have same := (prepareCall_worlds frame caller entered types argCount args prepared).2
    have first : NativeReferenceMachine.Runs frame.world returned.world := by rw [← same]; exact calledIH
    have resumedRun := resumeCall_projects entered.world caller target returned
    rw [resumed] at resumedRun
    exact NativeReferenceMachine.runs_trans _ _ _ first (NativeReferenceMachine.runs_trans _ _ _ resumedRun laterIH)
  | callStopped name classification types argCount target args callee unwind next frame caller entered returned world prepared called resumed ih =>
    have same := (prepareCall_worlds frame caller entered types argCount args prepared).2
    have first : NativeReferenceMachine.Runs frame.world returned.world := by rw [← same]; exact ih
    have resumedRun := resumeCall_projects entered.world caller target returned
    rw [resumed] at resumedRun
    exact NativeReferenceMachine.runs_trans _ _ _ first resumedRun
  | callUnsupported name classification types argCount target args callee unwind next frame caller entered returned source world prepared called resumed ih =>
    have same := (prepareCall_worlds frame caller entered types argCount args prepared).2
    have first : NativeReferenceMachine.Runs frame.world returned.world := by rw [← same]; exact ih
    have resumedRun := resumeCall_projects entered.world caller target returned
    rw [resumed] at resumedRun
    exact NativeReferenceMachine.runs_trans _ _ _ first resumedRun
  | loopArgumentInvalid => exact .refl _
  | loopInitialInvalid => exact .refl _
  | loopRun classification function frame slice native flow argument initialized executed =>
    have same := NativeByteLoopLLBC.initial_world function frame.world slice native initialized
    rw [fromLoop_world, ← same]
    exact NativeByteLoopLLBC.executes_projects function native flow executed

theorem invokes_projects (function : Definition) (world : State) (args : List Input) (flow : Flow)
    (invoked : Invokes function world args flow) : NativeReferenceMachine.Runs world flow.world := by
  cases invoked with
  | argumentsInvalid => exact .refl _
  | initialInvalid => exact .refl _
  | run values frame flow decoded initialized executed =>
    have same := NativeRecordLLBC.initial_world function.types function.argCount values world frame initialized
    have first := runs_projects function.code frame flow executed
    rw [same] at first
    exact NativeReferenceMachine.runs_trans _ _ _ first (NativeRecordLLBC.settle_projects world flow)

theorem invokes_reachable (function : Definition) (world : State) (args : List Input) (flow : Flow)
    (reachable : NativeReferenceMachine.Reachable world) (invoked : Invokes function world args flow) :
    NativeReferenceMachine.Reachable flow.world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (invokes_projects function world args flow invoked)

end FormalProof4FHE.HasteBoots.NativeRecordDropCalls
