module

public import FormalProof4FHE.HasteBoots.NativeDeferredBatchOwnership
public import FormalProof4FHE.HasteBoots.NativeGoldBatchLifetimeSourceRisk
@[expose] public section

/-! Actual deferred receipts supply accepted-batch and containing-history witnesses. Their original registry owners and grouped claims are retained before later stopped results. Framing remains explicit; consistent sources follow outside the same global persistent bad event. -/
namespace FormalProof4FHE.HasteBoots.NativeDeferredBatchAvailability
open NativeDeferredBatchVerification (Context Result Receipt program)
open NativeGoldBatchPcsProgram (Scheduler)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open NativeGoldBatchAnySourceRisk (Accepted HasSource)
open NativeGoldBatchSourceRisk (Framed)
open NativeGoldBatchFamilyAvailability (reconstructed)
open NativeMerkleShapeFamily (shape)
open OracleProgram (run)
open OracleSpec OracleComp MeasureTheory
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem receipt_accepted {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : Result Memory) (executed : (run (program ctx choose memory) world).run.1 = .verification result)
    (history : List Observation) (observed : (run (program ctx choose memory) world).run.2.Sublist history)
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (framed : Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before)) :
    Accepted world history (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) choose ctx.workerFuel receipt.memory receipt.work := by
  obtain ⟨checked,contained⟩ := NativeDeferredBatchVerification.program_receipts ctx choose memory world result executed receipt member
  exact ⟨framed,receipt.completion,receipt.after,checked.1,checked.2,contained.trans observed⟩

theorem receipt_binding {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : Result Memory) (executed : (run (program ctx choose memory) world).run.1 = .verification result)
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts) :
    receipt.work.root = receipt.call.oracle.root ∧ receipt.work.width = receipt.call.oracle.parameters.width.val ∧
      receipt.work.binding.queries = receipt.call.queries ∧ receipt.work.binding.values = receipt.call.values := by
  have checked := (NativeDeferredBatchVerification.program_receipts ctx choose memory world result executed receipt member).1
  have origin := NativeGoldBatchPcsProgram.completed_origin _ choose ctx.workerFuel receipt.memory world receipt.work receipt.completion checked.1
  exact NativeGoldBatchPcsProgram.prepared_binding _ world receipt.work origin.prepared

/-- Actual accepted receipts retain their first-original owner and grouped
claims, and use a source at the actual owner-context digest. Later stopped
results retain these same earlier accepted receipts. -/
theorem receipt_source {Memory : Type} (dummy : Digest) (ctx : Context) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : Result Memory) (executed : (run (program ctx choose memory) world).run.1 = .verification result)
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (program ctx choose memory) world).run.2.Sublist history)
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (framed : Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (noBad : ¬CheckpointCollision.Bad shape (reconstructed dummy history)) :
    NativeDeferredBatchOwnership.OriginalCall ctx.registry ctx.state receipt.call ∧
      receipt.work.root = receipt.call.oracle.root ∧ receipt.work.width = receipt.call.oracle.parameters.width.val ∧
      receipt.work.binding.queries = receipt.call.queries ∧ receipt.work.binding.values = receipt.call.values ∧
      HasSource dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work history world := by
  have owned := NativeDeferredBatchOwnership.program_owners ctx choose memory world result executed receipt member
  obtain ⟨root,width,queries,values⟩ := receipt_binding ctx choose memory world result executed receipt member
  refine ⟨owned,root,width,queries,values,?_⟩
  by_contra missing
  exact noBad (NativeGoldBatchAnySourceRisk.failure_implies_bad Memory dummy world history truthful
    ⟨_,choose,ctx.workerFuel,receipt.memory,receipt.work,receipt_accepted ctx choose memory world result executed history observed receipt member framed,missing⟩)

def Failure {Memory : Type} (dummy : Digest) (ctx : Context) (choose : Scheduler Memory) (memory : Memory)
    (history : List Observation) (world : World) : Prop :=
  ∃ (result : Result Memory) (receipt : Receipt Memory),
    (run (program ctx choose memory) world).run.1 = .verification result ∧ receipt ∈ result.progress.receipts ∧
    Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) ∧
    ¬HasSource dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work history world

theorem failure_implies_any {Memory : Type} (dummy : Digest) (ctx : Context) (choose : Scheduler Memory) (memory : Memory)
    (history : List Observation) (world : World) (observed : (run (program ctx choose memory) world).run.2.Sublist history)
    (failed : Failure dummy ctx choose memory history world) : NativeGoldBatchAnySourceRisk.Failure Memory dummy history world := by
  obtain ⟨result,receipt,executed,member,framed,missing⟩ := failed
  exact ⟨_,choose,ctx.workerFuel,receipt.memory,receipt.work,
    receipt_accepted ctx choose memory world result executed history observed receipt member framed,missing⟩

theorem failure_le_charge {Memory : Type} (dummy : Digest) (ctx : Context) (choose : Scheduler Memory) (memory : Memory) :
    InputIndexedOracle.law {world | Failure dummy ctx choose memory (run (program ctx choose memory) world).run.2 world} ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (CheckpointCollision.loss unifSpec shape)
        ((NativeRootFamilyFreeze.compile NativeParentLedger.empty (program ctx choose memory)).run NativeShakeCache.empty)
        (CheckpointExecution.empty shape) := by
  have included : {world | Failure dummy ctx choose memory (run (program ctx choose memory) world).run.2 world} ⊆
      {world | NativeGoldBatchAnySourceRisk.Failure Memory dummy (run (program ctx choose memory) world).run.2 world} :=
    fun world failed => failure_implies_any dummy ctx choose memory _ world (List.Sublist.refl _) failed
  exact (measure_mono included).trans (NativeGoldBatchAnySourceRisk.failure_le_charge Memory dummy (program ctx choose memory))
end
end FormalProof4FHE.HasteBoots.NativeDeferredBatchAvailability
