module
public import FormalProof4FHE.HasteBoots.NativeRootFamilyHashStep
public import FormalProof4FHE.HasteBoots.PrivateCoinByteRootBudget
@[expose] public section

/-! First global source/collision failures occur at actual hash instructions
of the closed interpreter. Every earlier mixed observation remains part of the
selecting packet; local steps never manufacture oracle events. -/
namespace FormalProof4FHE.HasteBoots.PrivateCoinByteRootFailure
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open NativeTranscript (Observation Execution)
open PrivateCoinByteMachine (Instruction State take initialise)
open PrivateCoinReplay (Tape)
open PrivateCoinByteFixed (Packet packet history history_run history_replay)
open PrivateCoinByteRequest (command)
open InstructionClock (single)
open NativeRootFamilyLifetime (Bad)
open MeasureTheory ProbabilityTheory
noncomputable section

def select (code : List Instruction) (publicData : Input) (tape : Tape) (old : Packet) : Option Input :=
  match CausalSeedExposure.request (command code publicData tape) old.1 with
  | some (.hash input) => some input
  | _ => none

def event (code : List Instruction) (publicData : Input) (tape : Tape) (dummy : Digest) (old : Packet) (world : World) : Prop :=
  match select code publicData tape old with
  | none => False
  | some input => NativeRootFamilyHashStep.event dummy input old.2 world

def risk (code : List Instruction) (publicData : Input) (tape : Tape) (dummy : Digest) (old : Packet) : ENNReal :=
  match select code publicData tape old with
  | none => 0
  | some input => NativeRootFamilyHashStep.risk dummy input old.2

theorem conditional_bound {past : World → Execution (State ⊕ State)} (replay : ObservationReplay.Replayable past)
    (code : List Instruction) (publicData : Input) (tape : Tape) (dummy : Digest) (world : World) :
    (law[|{other | (past other).run = (past world).run}])
      {other | event code publicData tape dummy (past other).run other} ≤ risk code publicData tape dummy (past world).run := by
  have fixed : (law[|{other | (past other).run = (past world).run}])
      {other | event code publicData tape dummy (past other).run other} =
      (law[|{other | (past other).run = (past world).run}])
      {other | event code publicData tape dummy (past world).run other} := by
    apply NativeShakeProjection.conditional_event_congr replay world
    intro other same
    rw [same]
  rw [fixed]
  cases chosen : select code publicData tape (past world).run with
  | none => simp only [event,risk,chosen,Set.ofPred_false,measure_empty,le_refl]
  | some input =>
    simp only [event,risk,chosen]
    exact NativeRootFamilyHashStep.conditional_bound replay dummy world input

theorem event_measurable {past : World → Execution (State ⊕ State)} (replay : ObservationReplay.Replayable past)
    (code : List Instruction) (publicData : Input) (tape : Tape) (dummy : Digest) :
    MeasurableSet {world | event code publicData tape dummy (past world).run world} := by
  apply OracleProgramHistory.event_measurable replay
  intro old
  cases chosen : select code publicData tape old with
  | none => simp only [event,chosen,Set.ofPred_false,MeasurableSet.empty]
  | some input => simpa only [event,chosen] using NativeRootFamilyHashStep.event_measurable dummy input old.2

theorem averaged_bound {past : World → Execution (State ⊕ State)} (replay : ObservationReplay.Replayable past)
    (code : List Instruction) (publicData : Input) (tape : Tape) (dummy : Digest) :
    law {world | event code publicData tape dummy (past world).run world} ≤
      ∫⁻ world, risk code publicData tape dummy (past world).run ∂law := by
  rw [OracleHistoryComposition.average_event replay law _ (event_measurable replay code publicData tape dummy)]
  exact lintegral_mono (conditional_bound replay code publicData tape dummy)

theorem tick_coverage (code : List Instruction) (publicData : Input) (tape : Tape) (dummy : Digest) (state : State)
    (before : List Observation) (world : World) (safe : ¬Bad dummy before)
    (failed : Bad dummy (before++(OracleProgram.run (PrivateCoinByteMachine.tick code publicData tape state) world).run.2)) :
    event code publicData tape dummy (packet state before) world := by
  rw [PrivateCoinByteRequest.command_exact] at failed
  cases chosen : command code publicData tape state with
  | done next =>
    rw [chosen] at failed
    change Bad dummy (before++[]) at failed
    rw [List.append_nil] at failed
    exact False.elim (safe failed)
  | start input next =>
    rw [chosen] at failed
    change Bad dummy (before++[.start input]) at failed
    exact False.elim (safe ((NativeRootFamilyHashStep.bad_start dummy before input).mp failed))
  | read input offset count next =>
    rw [chosen] at failed
    change Bad dummy (before++[.output input offset (InputIndexedOracle.bytes world input offset count)]) at failed
    exact False.elim (safe ((NativeRootFamilyHashStep.bad_read dummy before input offset _).mp failed))
  | hash input next =>
    simp only [event,select,CausalSeedExposure.request,packet,chosen]
    rw [chosen] at failed
    exact ⟨safe,failed⟩

theorem next_log (code : List Instruction) (publicData : Input) (tape : Tape) (privateData : ClosedByteMachine.Tape → Input) (fuel : ℕ) (world : World) :
    (history code publicData tape privateData (fuel+1) world).run.2 =
      (history code publicData tape privateData fuel world).run.2 ++
        (OracleProgram.run (PrivateCoinByteMachine.tick code publicData tape
          (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.1) world).run.2 := by
  simp only [history_run]
  rw [PrivateCoinByteMachine.take_resume code publicData tape fuel 1,OracleProgram.run_bind,ObservationReplay.run_bind,
    PrivateCoinByteLogWork.take_one_log]
  rfl

theorem coverage (code : List Instruction) (publicData : Input) (tape : Tape) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (fuel : ℕ) (world : World) (failed : Bad dummy (history code publicData tape privateData fuel world).run.2) :
    ∃ index < fuel, event code publicData tape dummy (history code publicData tape privateData index world).run world := by
  induction fuel with
  | zero =>
    change CheckpointCollision.Bad NativeMerkleShapeFamily.shape (CheckpointExecution.empty NativeMerkleShapeFamily.shape) at failed
    rcases failed with flag | collision
    · cases flag
    · exact False.elim (CachedHashCollision.no_collision_empty collision)
  | succ fuel ih =>
    by_cases old : Bad dummy (history code publicData tape privateData fuel world).run.2
    · obtain ⟨index,bound,yes⟩ := ih old
      exact ⟨index,by omega,yes⟩
    · refine ⟨fuel,by omega,?_⟩
      rw [next_log] at failed
      have yes := tick_coverage code publicData tape dummy
        (OracleProgram.run (take code publicData tape fuel (initialise code privateData)) world).run.1
        (history code publicData tape privateData fuel world).run.2 world old failed
      simpa only [history_run,packet] using yes
end
end FormalProof4FHE.HasteBoots.PrivateCoinByteRootFailure
