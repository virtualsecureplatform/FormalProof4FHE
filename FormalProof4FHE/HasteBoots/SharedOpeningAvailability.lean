module
public import FormalProof4FHE.HasteBoots.SingleOpeningAvailability
public import FormalProof4FHE.HasteBoots.CacheBackedSingleOpening
public import FormalProof4FHE.HasteBoots.NativeGoldBatchAnySourceRisk
@[expose] public section

/-! Native helper single openings and native source batches use one complete
history exception, including arbitrary causal prequeries and lifetime prefixes.
A single-call view combines authenticated frozen-source equations with actual
allocated-code finishing. This is availability, not final PCS/lookup soundness. -/
namespace FormalProof4FHE.HasteBoots.SharedOpeningAvailability
open NativeRootMessage (Digest)
open InputIndexedOracle (World)
open NativeTranscript (Observation)
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open OracleProgram (Program run)
open MeasureTheory OracleSpec OracleComp
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- Both fields are theorem conclusions; the native verifier receives neither
source-table truth nor a finishing/encoding certificate. -/
structure SingleView (dummy : Digest) (ctx : Context) (work : Prepared) (history : List Observation) (world : World)
    (origin : CacheBackedSingleOpening.Origin ctx) : Prop where
  source : SingleOpeningAvailability.HasSource dummy ctx work history world
  finishes : SingleOpeningFinishing.Finishes ctx work origin.primitive origin.capacity

/-- The original allocation, actual accepted call and shared history provide
both source authentication equations and response finishing, or the shared Bad. -/
theorem single_view_or_bad {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (origin : CacheBackedSingleOpening.Origin ctx) (history : List Observation)
    (choose : NativeGoldPcsProgram.Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : SingleOpeningAvailability.Accepted world history ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world history) :
    SingleView dummy ctx work history world origin ∨ NativeRootFamilyLifetime.Bad dummy history := by
  by_cases missing : SingleOpeningAvailability.HasSource dummy ctx work history world
  · left
    obtain ⟨_,completion,parent,executed,status,_⟩ := accepted
    exact ⟨missing,origin.accepted_finishes choose fuel memory world work completion executed parent status⟩
  · right
    exact SingleOpeningAvailability.failure_implies_bad Memory dummy world history truthful
      ⟨ctx,choose,fuel,memory,work,accepted,missing⟩

/-- Accepted receipts from the actual ordered helper run supply their own
single-call executions and original-position subtraces in the complete history. -/
theorem helper_receipt_view_or_bad {B Memory : Type} (dummy : Digest) (ctx : NativeGoldHelperVerification.Context B)
    (choose : NativeGoldPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (bound : NativeSharedLookupBody.Bound) (plan : NativeSharedLookupHelpers.Plan NativeGoldPcsOpening.Opening)
    (status : NativeGoldHelperVerification.Result Memory)
    (executed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.1 = .helpers bound plan status)
    (receipt : NativeGoldHelperVerification.Receipt Memory) (member : receipt ∈ status.progress.receipts)
    (origin : CacheBackedSingleOpening.Origin (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call))
    (framed : SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call))
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldHelperVerification.program ctx choose memory) world).run.2.Sublist history) :
    SingleView dummy _ receipt.work history world origin ∨ NativeRootFamilyLifetime.Bad dummy history := by
  obtain ⟨checked,trace⟩ := NativeGoldHelperVerification.helpers_receipts ctx choose memory world bound plan status executed receipt member
  exact single_view_or_bad dummy _ world receipt.work origin history choose ctx.workerFuel receipt.memory
    ⟨framed,receipt.completion,receipt.after,checked.1,checked.2,trace.trans observed⟩ truthful

/-- Any missing single-helper or source-batch source in the same history.
The memory types can differ, as in the actual native helper/batch dispatcher. -/
def Failure (HelperMemory BatchMemory : Type) (dummy : Digest) (history : List Observation) (world : World) : Prop :=
  SingleOpeningAvailability.Failure HelperMemory dummy history world ∨
    NativeGoldBatchAnySourceRisk.Failure BatchMemory dummy history world

theorem failure_implies_bad (HelperMemory BatchMemory : Type) (dummy : Digest) (world : World) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history) (failed : Failure HelperMemory BatchMemory dummy history world) :
    NativeRootFamilyLifetime.Bad dummy history := by
  rcases failed with helper | batch
  · exact SingleOpeningAvailability.failure_implies_bad HelperMemory dummy world history truthful helper
  · exact NativeGoldBatchAnySourceRisk.failure_implies_bad BatchMemory dummy world history truthful batch

/-- The disjunction shares one Bad event: no added hash charge or count factor
for helper/source kinds, owner aliases, jobs, columns or verifier calls. -/
theorem failure_le_charge {A : Type} (HelperMemory BatchMemory : Type) (dummy : Digest) (program : Program A) :
    InputIndexedOracle.law {world | Failure HelperMemory BatchMemory dummy (run program world).run.2 world} ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp)
          NativeGoldColumnAuthentication.encoding dummy NativeMerkleShapeFamily.shape)
        (CheckpointCollision.loss unifSpec NativeMerkleShapeFamily.shape)
        ((NativeRootFamilyFreeze.compile NativeParentLedger.empty program).run NativeShakeCache.empty)
        (CheckpointExecution.empty NativeMerkleShapeFamily.shape) := by
  have included : {world | Failure HelperMemory BatchMemory dummy (run program world).run.2 world} ⊆
      {world | NativeRootFamilyLifetime.Bad dummy (run program world).run.2} := by
    intro world failed
    exact failure_implies_bad HelperMemory BatchMemory dummy world _ ((OracleProgram.run_replay program).truthful world) failed
  exact (measure_mono included).trans (NativeRootFamilyAudit.bad_le_charge dummy program)

def LifetimeFailure {S A : Type} (HelperMemory BatchMemory : Type) (dummy : Digest) (prelude : Program S)
    (step : S → OracleMachine.Command S A) (world : World) : Prop :=
  ∃ fuel, Failure HelperMemory BatchMemory dummy (run (NativeRootFamilyLifetime.program prelude step fuel) world).run.2 world

theorem lifetime_failure_covered {S A : Type} (HelperMemory BatchMemory : Type) (dummy : Digest) (prelude : Program S)
    (step : S → OracleMachine.Command S A) (world : World) (failed : LifetimeFailure HelperMemory BatchMemory dummy prelude step world) :
    ∃ fuel, NativeRootFamilyLifetime.Bad dummy (run (NativeRootFamilyLifetime.program prelude step fuel) world).run.2 := by
  obtain ⟨fuel,missing⟩ := failed
  exact ⟨fuel,failure_implies_bad HelperMemory BatchMemory dummy world _
    ((OracleProgram.run_replay (NativeRootFamilyLifetime.program prelude step fuel)).truthful world) missing⟩

/-- All actual prefixes share the supremum of increasing charges. The source
failure predicate need not itself persist after later observations. -/
theorem lifetime_failure_le_charge {S A : Type} (HelperMemory BatchMemory : Type) (dummy : Digest) (prelude : Program S)
    (step : S → OracleMachine.Command S A) :
    InputIndexedOracle.law {world | LifetimeFailure HelperMemory BatchMemory dummy prelude step world} ≤
      ⨆ fuel : ℕ, NativeRootFamilyLifetime.prefixCharge dummy prelude step fuel := by
  have included : {world | LifetimeFailure HelperMemory BatchMemory dummy prelude step world} ⊆
      {world | ∃ fuel, NativeRootFamilyLifetime.Bad dummy (run (NativeRootFamilyLifetime.program prelude step fuel) world).run.2} :=
    fun world failed => lifetime_failure_covered HelperMemory BatchMemory dummy prelude step world failed
  exact (measure_mono included).trans (NativeRootFamilyLifetime.lifetime_bad_le_charge dummy prelude step)

end
end FormalProof4FHE.HasteBoots.SharedOpeningAvailability
