namespace HasteBootsVecByteLoop
open FormalProof4FHE.HasteBoots
open NativeByteLoopLLBC
open NativeReferenceMachine (State)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeByteSliceIndex (Slice)

/-- The exact projected outcome distinguishes a rejected iteration from a
completed traversal; neither case discards its actual final machine world. -/
theorem loop_witness_exact (slice : Slice) (cursor : Nat) (world : State) (last : Option Pointer)
    (result : NativeByteDropTraversal.Result)
    (ran : NativeByteDropTraversal.Executes slice cursor world last result) (bounded : cursor ≤ slice.length.val)
    (six seven : Slot) :
    ∃ flow, LoopRuns f6.body f6.after
      (head world slice ⟨cursor, Nat.lt_of_le_of_lt bounded slice.length.isLt⟩ last six seven) flow ∧
      NativeRecordDropCalls.fromLoop flow =
        if result.complete then .returned (.scalar .unit) result.world else .invalid result.world := by
  induction ran generalizing six seven with
  | stop cursor world last done =>
    subst cursor
    refine ⟨.returned .unit (exit world), ?_, rfl⟩
    exact .stop _ _ _ (body_stop world slice last six seven) (after_exact world slice slice.length last six seven)
  | fail cursor world next last before failed =>
    obtain ⟨frame, actual, same⟩ := episode_failure world next slice
      ⟨cursor, Nat.lt_trans before slice.length.isLt⟩ last six seven before failed
    refine ⟨.invalid frame, .terminal _ _ actual rfl, ?_⟩
    change NativeRecordLLBC.Flow.invalid frame.world = .invalid next
    rw [same]
  | next cursor world next last pointer result before actual later ih =>
    obtain ⟨newSix, newSeven, stepped⟩ := episode_success world next slice
      ⟨cursor, Nat.lt_trans before slice.length.isLt⟩ last six seven before pointer actual
    have nextWord : successor ⟨cursor, Nat.lt_trans before slice.length.isLt⟩ =
        (⟨cursor+1, Nat.lt_of_le_of_lt (Nat.succ_le_of_lt before) slice.length.isLt⟩ : Word) := by
      apply Fin.ext
      exact NativeByteDropTraversal.cursor_increment slice.length ⟨cursor, Nat.lt_trans before slice.length.isLt⟩ before
    rw [nextWord] at stepped
    obtain ⟨flow, tail, observed⟩ := ih (Nat.succ_le_of_lt before) newSix newSeven
    exact ⟨flow, .next _ _ _ stepped tail, observed⟩

theorem run_exact (world : State) (slice : Slice) :
    ∃ flow, Executes f6 (entry world slice) flow ∧
      NativeRecordDropCalls.fromLoop flow =
        if (NativeByteDropTraversal.run world slice).complete then
          .returned (.scalar .unit) (NativeByteDropTraversal.run world slice).world
        else .invalid (NativeByteDropTraversal.run world slice).world := by
  obtain ⟨flow, loop, observed⟩ := loop_witness_exact slice 0 world none _
    (NativeByteDropTraversal.run_executes world slice) (Nat.zero_le _) .dead .dead
  exact ⟨flow, .start _ _ _ (before_exact world slice) loop, observed⟩
end HasteBootsVecByteLoop

namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeRecordDropCalls
open NativeRecordLLBC (Frame Flow Input)
open NativeReferenceMachine (State)
open NativeByteSliceIndex (Slice)
open NativeByteDropCalls (Classification)

/-- Every loop leaf is the actual retained source byte loop. This is a syntax
check, independent of any execution outcome, heap validity or caller witness. -/
def sourceLoops : Code → Bool
  | .done => true
  | .native _ next => sourceLoops next
  | .scope body next => sourceLoops body && sourceLoops next
  | .call _ _ _ _ _ _ callee unwind next => sourceLoops callee && sourceLoops unwind && sourceLoops next
  | .loop _ function => function == HasteBootsVecByteLoop.f6

def loopOutcome (world : State) (slice : Slice) : Flow :=
  let result := NativeByteDropTraversal.run world slice
  if result.complete then .returned (.scalar .unit) result.world else .invalid result.world

/-- Structural evaluation of the actual retained call tree, using the complete
source-loop traversal. A different loop declaration is rejected by the syntax
check; the concrete destructor tree is proved to contain only the source loop. -/
def evalCode : Code → Frame → Option Flow
  | .done, frame => some (.normal frame)
  | .native body next, frame => match NativeRecordLLBC.eval body frame with
    | .normal changed => evalCode next changed
    | flow => some flow
  | .scope body next, frame => match evalCode body frame with
    | none => none
    | some returned => match resumeScope frame.world returned with
      | .normal changed => evalCode next changed
      | flow => some flow
  | .call _ _ types count target args callee unwind next, frame =>
    match prepareCall frame types count args with
    | none => some (.invalid frame.world)
    | some (caller,entered) => match evalCode callee entered with
      | none => none
      | some returned => match resumeCall entered.world caller target returned with
        | .next changed => evalCode next changed
        | .unwind changed => evalCode unwind changed
        | .invalid world => some (.invalid world)
        | .unsupported source world => some (.unsupported source world)
  | .loop _ function, frame =>
    if function = HasteBootsVecByteLoop.f6 then
      some (match loopArgument frame with
        | none => .invalid frame.world
        | some slice => loopOutcome frame.world slice)
    else none

theorem loopOutcome_runs (classification : Classification) (frame : Frame) (slice : Slice)
    (argument : loopArgument frame = some slice) :
    Runs (.loop classification HasteBootsVecByteLoop.f6) frame (loopOutcome frame.world slice) := by
  obtain ⟨flow, executed, output⟩ := HasteBootsVecByteLoop.run_exact frame.world slice
  change fromLoop flow = loopOutcome frame.world slice at output
  rw [← output]
  exact .loopRun classification _ frame slice _ flow argument (HasteBootsVecByteLoop.initial_exact _ _) executed

theorem evalCode_total (code : Code) (frame : Frame) (checked : sourceLoops code = true) :
    (evalCode code frame).isSome = true := by
  induction code generalizing frame with
  | done => rfl
  | native body next ih =>
    simp only [sourceLoops] at checked
    cases actual : NativeRecordLLBC.eval body frame <;> simp only [evalCode, actual, Option.isSome_some]
    exact ih _ checked
  | scope body next bodyIH nextIH =>
    simp only [sourceLoops, Bool.and_eq_true] at checked
    have first := bodyIH frame checked.1
    cases actual : evalCode body frame with
    | none => rw [actual] at first; cases first
    | some flow =>
      cases settled : resumeScope frame.world flow <;> simp only [evalCode, actual, settled, Option.isSome_some]
      exact nextIH _ checked.2
  | call name classification types count target args callee unwind next calleeIH unwindIH nextIH =>
    simp only [sourceLoops, Bool.and_eq_true] at checked
    cases prepared : prepareCall frame types count args with
    | none => simp only [evalCode, prepared, Option.isSome_some]
    | some pair =>
      rcases pair with ⟨caller,entered⟩
      have first := calleeIH entered checked.1.1
      cases actual : evalCode callee entered with
      | none => rw [actual] at first; cases first
      | some flow =>
        cases resumed : resumeCall entered.world caller target flow <;>
          simp only [evalCode, prepared, actual, resumed, Option.isSome_some]
        · exact nextIH _ checked.2
        · exact unwindIH _ checked.1.2
  | loop classification function =>
    simp only [sourceLoops, beq_iff_eq] at checked
    subst function
    simp only [evalCode, ite_true, Option.isSome_some]

theorem evalCode_sound (code : Code) (frame : Frame) (flow : Flow)
    (computed : evalCode code frame = some flow) : Runs code frame flow := by
  induction code generalizing frame flow with
  | done => simp only [evalCode, Option.some.injEq] at computed; subst flow; exact .done frame
  | native body next nextIH =>
    cases actual : NativeRecordLLBC.eval body frame with
    | normal changed => exact .nativeNext body next frame changed flow actual (nextIH changed flow (by simpa only [evalCode, actual] using computed))
    | returned value world =>
      simp only [evalCode, actual, Option.some.injEq] at computed
      subst flow; exact .nativeStop body next frame _ actual rfl
    | unwind world =>
      simp only [evalCode, actual, Option.some.injEq] at computed
      subst flow; exact .nativeStop body next frame _ actual rfl
    | invalid world =>
      simp only [evalCode, actual, Option.some.injEq] at computed
      subst flow; exact .nativeStop body next frame _ actual rfl
    | unsupported source world =>
      simp only [evalCode, actual, Option.some.injEq] at computed
      subst flow; exact .nativeStop body next frame _ actual rfl
  | scope body next bodyIH nextIH =>
    cases actual : evalCode body frame with
    | none => simp only [evalCode, actual] at computed; cases computed
    | some returned =>
      have first := bodyIH frame returned actual
      cases settled : resumeScope frame.world returned with
      | normal changed =>
        apply Runs.scopeNext body next frame changed returned flow first settled
        exact nextIH changed flow (by simpa only [evalCode, actual, settled] using computed)
      | returned value world =>
        simp only [evalCode, actual, settled, Option.some.injEq] at computed
        subst flow; exact .scopeStop body next frame returned _ first settled rfl
      | unwind world =>
        simp only [evalCode, actual, settled, Option.some.injEq] at computed
        subst flow; exact .scopeStop body next frame returned _ first settled rfl
      | invalid world =>
        simp only [evalCode, actual, settled, Option.some.injEq] at computed
        subst flow; exact .scopeStop body next frame returned _ first settled rfl
      | unsupported source world =>
        simp only [evalCode, actual, settled, Option.some.injEq] at computed
        subst flow; exact .scopeStop body next frame returned _ first settled rfl
  | call name classification types count target args callee unwind next calleeIH unwindIH nextIH =>
    cases prepared : prepareCall frame types count args with
    | none =>
      simp only [evalCode, prepared, Option.some.injEq] at computed
      subst flow; exact .callInvalid name classification types count target args callee unwind next frame prepared
    | some pair =>
      rcases pair with ⟨caller,entered⟩
      cases actual : evalCode callee entered with
      | none => simp only [evalCode, prepared, actual] at computed; cases computed
      | some returned =>
        have first := calleeIH entered returned actual
        cases resumed : resumeCall entered.world caller target returned with
        | next changed =>
          apply Runs.callNext name classification types count target args callee unwind next frame caller entered changed returned flow prepared first resumed
          exact nextIH changed flow (by simpa only [evalCode, prepared, actual, resumed] using computed)
        | unwind changed =>
          apply Runs.callUnwind name classification types count target args callee unwind next frame caller entered changed returned flow prepared first resumed
          exact unwindIH changed flow (by simpa only [evalCode, prepared, actual, resumed] using computed)
        | invalid world =>
          simp only [evalCode, prepared, actual, resumed, Option.some.injEq] at computed
          subst flow; exact .callStopped name classification types count target args callee unwind next frame caller entered returned world prepared first resumed
        | unsupported source world =>
          simp only [evalCode, prepared, actual, resumed, Option.some.injEq] at computed
          subst flow; exact .callUnsupported name classification types count target args callee unwind next frame caller entered returned source world prepared first resumed
  | loop classification function =>
    by_cases same : function = HasteBootsVecByteLoop.f6
    · subst function
      cases argument : loopArgument frame with
      | none =>
        simp only [evalCode, ite_true, argument, Option.some.injEq] at computed
        subst flow; exact .loopArgumentInvalid classification _ frame argument
      | some slice =>
        simp only [evalCode, ite_true, argument, Option.some.injEq] at computed
        subst flow; exact loopOutcome_runs classification frame slice argument
    · simp only [evalCode, same, ite_false] at computed; cases computed

/-- On checked syntax the complete source model has exactly this computed
outcome, including rejected, unsupported and unwinding prefixes. -/
theorem evalCode_iff (code : Code) (frame : Frame) (flow : Flow) (checked : sourceLoops code = true) :
    Runs code frame flow ↔ evalCode code frame = some flow := by
  constructor
  · intro ran
    have total := evalCode_total code frame checked
    cases actual : evalCode code frame with
    | none => rw [actual] at total; cases total
    | some other =>
      have same := runs_deterministic code frame flow other ran (evalCode_sound code frame other actual)
      exact congrArg some same.symm
  · exact evalCode_sound code frame flow

def invokeCode (function : Definition) (world : State) (args : List Input) : Option Flow :=
  match NativeRecordLLBC.decodeArgs world args with
  | none => some (.invalid world)
  | some values => match NativeRecordLLBC.initial function.types function.argCount values world with
    | none => some (.invalid world)
    | some entered => (evalCode function.code entered).map (NativeRecordLLBC.settle world)

theorem invokeCode_total (function : Definition) (world : State) (args : List Input)
    (checked : sourceLoops function.code = true) : (invokeCode function world args).isSome = true := by
  cases decoded : NativeRecordLLBC.decodeArgs world args with
  | none => simp only [invokeCode, decoded, Option.isSome_some]
  | some values =>
    cases initialized : NativeRecordLLBC.initial function.types function.argCount values world with
    | none => simp only [invokeCode, decoded, initialized, Option.isSome_some]
    | some entered =>
      simpa only [invokeCode, decoded, initialized, Option.isSome_map] using evalCode_total function.code entered checked

theorem invokeCode_sound (function : Definition) (world : State) (args : List Input) (flow : Flow)
    (computed : invokeCode function world args = some flow) : Invokes function world args flow := by
  cases decoded : NativeRecordLLBC.decodeArgs world args with
  | none =>
    simp only [invokeCode, decoded, Option.some.injEq] at computed
    subst flow; exact .argumentsInvalid decoded
  | some values =>
    cases initialized : NativeRecordLLBC.initial function.types function.argCount values world with
    | none =>
      simp only [invokeCode, decoded, initialized, Option.some.injEq] at computed
      subst flow; exact .initialInvalid values decoded initialized
    | some entered =>
      simp only [invokeCode, decoded, initialized, Option.map_eq_some_iff] at computed
      obtain ⟨returned, actual, same⟩ := computed
      subst flow
      exact .run values entered returned decoded initialized (evalCode_sound function.code entered returned actual)

theorem source_loops_checked : sourceLoops f1.code = true := by decide

/-- A total executor for the concrete retained destructor. The proof of a value
is established for all inputs; no fallback outcome or execution witness is supplied. -/
def execute (world : State) (args : List Input) : Flow :=
  (invokeCode f1 world args).get (invokeCode_total f1 world args source_loops_checked)

theorem execute_invokes (world : State) (args : List Input) : Invokes f1 world args (execute world args) := by
  apply invokeCode_sound
  exact Option.get_mem (invokeCode_total f1 world args source_loops_checked)

theorem invocation_iff_execute (world : State) (args : List Input) (flow : Flow) :
    Invokes f1 world args flow ↔ flow = execute world args := by
  constructor
  · intro invoked
    exact invokes_deterministic f1 world args flow _ invoked (execute_invokes world args)
  · intro same; subst flow; exact execute_invokes world args


theorem loopOutcome_heap_frame (world : State) (slice : Slice) :
    (loopOutcome world slice).world.pointers.heap = world.pointers.heap := by
  unfold loopOutcome
  dsimp only
  split <;> exact NativeByteDropTraversal.run_heap_frame world slice

theorem execute_projects (world : State) (args : List Input) :
    NativeReferenceMachine.Runs world (execute world args).world :=
  invokes_projects f1 world args (execute world args) (execute_invokes world args)

theorem execute_reachable (world : State) (args : List Input) (reachable : NativeReferenceMachine.Reachable world) :
    NativeReferenceMachine.Reachable (execute world args).world :=
  invokes_reachable f1 world args _ reachable (execute_invokes world args)

end HasteBootsVecDrop
