module

public import FormalProof4FHE.HasteBoots.NativeGoldLookupAvailability
@[expose] public section

/-! Raw-source failures from the actual whole registered lookup producer reduce to the shared any-batch availability event, over finite histories and unbounded causal lifetimes. Acceptance and receipt witnesses are derived from execution. Framing, lineage, application soundness and physical work remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldLookupLifetimeAvailability
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (Program run)
open OracleSpec OracleComp MeasureTheory
open NativeMerkleShapeFamily (shape)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- A failed source receipt emitted by the actual whole registered lookup,
whose complete native observation trace is present in the containing history. -/
def Failure (Memory : Type) (dummy : Digest) (history : List Observation) (world : World) : Prop :=
  ∃ (ctx : NativeGoldHelperVerification.Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory),
    (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history ∧
    NativeGoldLookupAvailability.Failure dummy ctx chooseHelper chooseBatch memory history world

theorem failure_implies_any (Memory : Type) (dummy : Digest) (history : List Observation) (world : World)
    (failed : Failure Memory dummy history world) : NativeGoldBatchAnySourceRisk.Failure Memory dummy history world := by
  obtain ⟨ctx,chooseHelper,chooseBatch,memory,observed,failed⟩ := failed
  exact NativeGoldLookupAvailability.failure_implies_any dummy ctx chooseHelper chooseBatch memory history world observed failed

theorem failure_replay (Memory : Type) (dummy : Digest) (history : List Observation) (world other : World)
    (agrees : ObservationReplay.Agrees other history) (failed : Failure Memory dummy history world) : Failure Memory dummy history other := by
  obtain ⟨ctx,chooseHelper,chooseBatch,memory,observed,failed⟩ := failed
  have same := (OracleProgram.run_replay (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory)).replay world other
    (fun entry member => agrees entry (observed.subset member))
  exact ⟨ctx,chooseHelper,chooseBatch,memory,by rw [same]; exact observed,
    NativeGoldLookupAvailability.failure_replay dummy ctx chooseHelper chooseBatch memory history world other observed agrees failed⟩

def HistoryFailure (Memory : Type) (dummy : Digest) (history : List Observation) : Prop := ∃ world, Failure Memory dummy history world

theorem failure_measurable {A : Type} (Memory : Type) (dummy : Digest) (program : Program A) :
    MeasurableSet {world | Failure Memory dummy (run program world).run.2 world} := by
  have same : {world | Failure Memory dummy (run program world).run.2 world} =
      {world | HistoryFailure Memory dummy (run program world).run.2} := by
    ext world
    constructor
    · intro failed; exact ⟨world,failed⟩
    · rintro ⟨other,failed⟩
      exact failure_replay Memory dummy _ other world ((OracleProgram.run_replay program).truthful world) failed
  rw [same]
  exact OracleExecutionLaw.event_measurable (OracleProgram.run_replay program) (fun packet => HistoryFailure Memory dummy packet.2)

theorem failure_le_charge {A : Type} (Memory : Type) (dummy : Digest) (program : Program A) :
    InputIndexedOracle.law {world | Failure Memory dummy (run program world).run.2 world} ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (CheckpointCollision.loss unifSpec shape)
        ((NativeRootFamilyFreeze.compile NativeParentLedger.empty program).run NativeShakeCache.empty)
        (CheckpointExecution.empty shape) := by
  have included : {world | Failure Memory dummy (run program world).run.2 world} ⊆
      {world | NativeGoldBatchAnySourceRisk.Failure Memory dummy (run program world).run.2 world} :=
    fun world failed => failure_implies_any Memory dummy _ world failed
  exact (measure_mono included).trans (NativeGoldBatchAnySourceRisk.failure_le_charge Memory dummy program)

def LifetimeFailure {S A : Type} (Memory : Type) (dummy : Digest) (prelude : Program S)
    (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  ∃ fuel, Failure Memory dummy (run (NativeRootFamilyLifetime.program prelude step fuel) world).run.2 world

theorem lifetime_failure_measurable {S A : Type} (Memory : Type) (dummy : Digest) (prelude : Program S)
    (step : S → OracleMachine.Command S A) : MeasurableSet {world | LifetimeFailure Memory dummy prelude step world} := by
  have union : {world | LifetimeFailure Memory dummy prelude step world} =
      ⋃ fuel : ℕ, {world | Failure Memory dummy (run (NativeRootFamilyLifetime.program prelude step fuel) world).run.2 world} := by
    ext world
    simp only [LifetimeFailure,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [union]
  exact MeasurableSet.iUnion (fun fuel => failure_measurable Memory dummy (NativeRootFamilyLifetime.program prelude step fuel))

/-- The actual whole-lookup producer is covered over the unbounded lifetime,
including earlier accepted receipts before a later native rejection. -/
theorem lifetime_failure_le_charge {S A : Type} (Memory : Type) (dummy : Digest) (prelude : Program S)
    (step : S → OracleMachine.Command S A) :
    InputIndexedOracle.law {world | LifetimeFailure Memory dummy prelude step world} ≤
      ⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy prelude step fuel := by
  have included : {world | LifetimeFailure Memory dummy prelude step world} ⊆
      {world | NativeGoldBatchLifetimeSourceRisk.Failure Memory dummy prelude step world} := by
    rintro world ⟨fuel,failed⟩
    exact ⟨fuel,failure_implies_any Memory dummy _ world failed⟩
  exact (measure_mono included).trans (NativeGoldBatchLifetimeSourceRisk.lifetime_failure_le_charge Memory dummy prelude step)
end
end FormalProof4FHE.HasteBoots.NativeGoldLookupLifetimeAvailability
