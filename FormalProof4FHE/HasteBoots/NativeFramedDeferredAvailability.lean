module

public import FormalProof4FHE.HasteBoots.NativeLookupBodyFraming
public import FormalProof4FHE.HasteBoots.NativeDeferredBatchFraming
public import FormalProof4FHE.HasteBoots.NativeSourceClaimFraming
public import FormalProof4FHE.HasteBoots.NativeGoldLookupAvailability
@[expose] public section

/-! Receipt source availability now derives per-receipt framing from the initial deferred parent and static serialized-message bounds. Upstream parent framing and native allocation/refinement domains remain explicit, as do lineage, application soundness and physical work. -/
namespace FormalProof4FHE.HasteBoots.NativeFramedDeferredAvailability
open NativeDeferredBatchVerification (Context Receipt Result)
open NativeGoldBatchPcsProgram (Scheduler)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
open NativeGoldBatchAnySourceRisk (HasSource)
open NativeGoldBatchFamilyAvailability (reconstructed)
open NativeMerkleShapeFamily (shape)
open OracleSpec OracleComp MeasureTheory
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- A framed initial parent and pre-oracle serialized-message bounds replace
the former caller-supplied per-receipt framing certificate. -/
theorem receipt_source {Memory : Type} (dummy : Digest) (ctx : Context) (choose : Scheduler Memory) (memory : Memory) (world : World)
    (result : Result Memory) (executed : (run (NativeDeferredBatchVerification.program ctx choose memory) world).run.1 = .verification result)
    (framed : NativeTranscriptFraming.Framed ctx.state.parent) (domain : NativeDeferredBatchFraming.Domain ctx)
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeDeferredBatchVerification.program ctx choose memory) world).run.2.Sublist history)
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (noBad : ¬CheckpointCollision.Bad shape (reconstructed dummy history)) :
    NativeDeferredBatchOwnership.OriginalCall ctx.registry ctx.state receipt.call ∧
      receipt.work.root = receipt.call.oracle.root ∧ receipt.work.width = receipt.call.oracle.parameters.width.val ∧
      receipt.work.binding.queries = receipt.call.queries ∧ receipt.work.binding.values = receipt.call.values ∧
      HasSource dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work history world :=
  NativeDeferredBatchAvailability.receipt_source dummy ctx choose memory world result executed history truthful observed receipt member
    (NativeDeferredBatchFraming.receipt_framed ctx choose memory world result executed framed domain receipt member) noBad

def Failure {Memory : Type} (dummy : Digest) (ctx : Context) (choose : Scheduler Memory) (memory : Memory)
    (history : List Observation) (world : World) : Prop :=
  ∃ (result : Result Memory) (receipt : Receipt Memory),
    (run (NativeDeferredBatchVerification.program ctx choose memory) world).run.1 = .verification result ∧
    receipt ∈ result.progress.receipts ∧ ¬HasSource dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work history world

theorem failure_implies_any {Memory : Type} (dummy : Digest) (ctx : Context) (choose : Scheduler Memory) (memory : Memory)
    (framed : NativeTranscriptFraming.Framed ctx.state.parent) (domain : NativeDeferredBatchFraming.Domain ctx)
    (history : List Observation) (world : World)
    (observed : (run (NativeDeferredBatchVerification.program ctx choose memory) world).run.2.Sublist history)
    (failed : Failure dummy ctx choose memory history world) : NativeGoldBatchAnySourceRisk.Failure Memory dummy history world := by
  obtain ⟨result,receipt,executed,member,missing⟩ := failed
  exact NativeDeferredBatchAvailability.failure_implies_any dummy ctx choose memory history world observed
    ⟨result,receipt,executed,member,NativeDeferredBatchFraming.receipt_framed ctx choose memory world result executed framed domain receipt member,missing⟩

theorem failure_le_charge {Memory : Type} (dummy : Digest) (ctx : Context) (choose : Scheduler Memory) (memory : Memory)
    (framed : NativeTranscriptFraming.Framed ctx.state.parent) (domain : NativeDeferredBatchFraming.Domain ctx) :
    InputIndexedOracle.law {world | Failure dummy ctx choose memory (run (NativeDeferredBatchVerification.program ctx choose memory) world).run.2 world} ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) NativeGoldColumnAuthentication.encoding dummy shape)
        (CheckpointCollision.loss unifSpec shape)
        ((NativeRootFamilyFreeze.compile NativeParentLedger.empty (NativeDeferredBatchVerification.program ctx choose memory)).run NativeShakeCache.empty)
        (CheckpointExecution.empty shape) := by
  have included : {world | Failure dummy ctx choose memory (run (NativeDeferredBatchVerification.program ctx choose memory) world).run.2 world} ⊆
      {world | NativeGoldBatchAnySourceRisk.Failure Memory dummy (run (NativeDeferredBatchVerification.program ctx choose memory) world).run.2 world} :=
    fun world failed => failure_implies_any dummy ctx choose memory framed domain _ world (List.Sublist.refl _) failed
  exact (measure_mono included).trans (NativeGoldBatchAnySourceRisk.failure_le_charge Memory dummy (NativeDeferredBatchVerification.program ctx choose memory))

/-- The whole registered lookup inherits derived receipt framing at its actual
deferred handoff. Upstream parent framing and message allocation bounds remain explicit. -/
theorem lookup_receipt_source {Memory : Type} (dummy : Digest)
    (ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : Scheduler Memory) (memory : Memory) (world : World)
    (prepared : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (framed : NativeTranscriptFraming.Framed progress.state.parent)
    (domain : NativeDeferredBatchFraming.Domain (NativeGoldLookupVerification.batchContext ctx progress))
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (noBad : ¬CheckpointCollision.Bad shape (reconstructed dummy history)) :
    NativeDeferredBatchOwnership.OriginalCall ctx.registry progress.state receipt.call ∧
      receipt.work.root = receipt.call.oracle.root ∧ receipt.work.width = receipt.call.oracle.parameters.width.val ∧
      receipt.work.binding.queries = receipt.call.queries ∧ receipt.work.binding.values = receipt.call.values ∧
      HasSource dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work history world := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress (.verification result) executed
  exact NativeGoldLookupAvailability.receipt_source dummy ctx chooseHelper chooseBatch memory world prepared progress result executed history truthful observed receipt member
    (NativeDeferredBatchFraming.receipt_framed (NativeGoldLookupVerification.batchContext ctx progress) chooseBatch prepared.helpers.memory world result origin.2.2.1 framed domain receipt member) noBad
/-- Source collection derives the deferred initial framing from the helper's
actual last-accepted parent, including alias skips and stopped push paths. -/
theorem lookup_from_helpers {Memory : Type} (dummy : Digest)
    (ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : Scheduler Memory) (memory : Memory) (world : World)
    (prepared : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (framed : NativeTranscriptFraming.Framed prepared.helpers.lastAccepted)
    (claims : NativeSourceClaimFraming.Domain ctx.registry ctx.requests prepared.query ctx.proof.sources)
    (domain : NativeDeferredBatchFraming.Domain (NativeGoldLookupVerification.batchContext ctx progress))
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (noBad : ¬CheckpointCollision.Bad shape (reconstructed dummy history)) :
    NativeDeferredBatchOwnership.OriginalCall ctx.registry progress.state receipt.call ∧
      receipt.work.root = receipt.call.oracle.root ∧ receipt.work.width = receipt.call.oracle.parameters.width.val ∧
      receipt.work.binding.queries = receipt.call.queries ∧ receipt.work.binding.values = receipt.call.values ∧
      HasSource dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work history world := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress (.verification result) executed
  have sourceFramed := NativeSourceClaimFraming.program_framed NativeGoldBlockCode.description.row ctx.registry ctx.requests prepared.query ctx.proof.sources
    (NativeGoldLookupVerification.initial prepared) world framed claims
  change NativeTranscriptFraming.Framed (run (NativeGoldLookupVerification.sourceProgram ctx prepared) world).run.1.progress.state.parent at sourceFramed
  rw [origin.2.1] at sourceFramed
  exact lookup_receipt_source dummy ctx chooseHelper chooseBatch memory world prepared progress result executed sourceFramed domain history truthful observed receipt member noBad

/-- Framing is propagated through the actual ordered helpers before source
collection and deferred verification. Only the earlier lookup-body parent
and serialized-message allocation domains remain explicit. -/
theorem lookup_from_body {Memory : Type} (dummy : Digest)
    (ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : Scheduler Memory) (memory : Memory) (world : World)
    (prepared : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (framed : NativeTranscriptFraming.Framed prepared.body.parent)
    (helpers : NativeGoldHelperFraming.Domain prepared.plan.calls)
    (claims : NativeSourceClaimFraming.Domain ctx.registry ctx.requests prepared.query ctx.proof.sources)
    (domain : NativeDeferredBatchFraming.Domain (NativeGoldLookupVerification.batchContext ctx progress))
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (noBad : ¬CheckpointCollision.Bad shape (reconstructed dummy history)) :
    NativeDeferredBatchOwnership.OriginalCall ctx.registry progress.state receipt.call ∧
      receipt.work.root = receipt.call.oracle.root ∧ receipt.work.width = receipt.call.oracle.parameters.width.val ∧
      receipt.work.binding.queries = receipt.call.queries ∧ receipt.work.binding.values = receipt.call.values ∧
      HasSource dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work history world := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress (.verification result) executed
  have helperFramed := NativeGoldHelperFraming.prepared_framed ctx chooseHelper memory world prepared origin.1 framed helpers
  exact lookup_from_helpers dummy ctx chooseHelper chooseBatch memory world prepared progress result executed helperFramed claims domain history truthful observed receipt member noBad

/-- All intermediate parent framing follows from the original caller parent
and static message allocation bounds along the actual native lookup run. -/
theorem lookup_from_parent {Memory : Type} (dummy : Digest)
    (ctx : NativeGoldHelperVerification.Context (NativePrefixCodec.Vector NativeGoldBatchOpening.Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : Scheduler Memory) (memory : Memory) (world : World)
    (prepared : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (framed : NativeTranscriptFraming.Framed ctx.parent)
    (bodyDomain : NativeLookupBodyFraming.Domain ctx.registry ctx.requests ctx.proof)
    (helpers : NativeGoldHelperFraming.Domain prepared.plan.calls)
    (claims : NativeSourceClaimFraming.Domain ctx.registry ctx.requests prepared.query ctx.proof.sources)
    (domain : NativeDeferredBatchFraming.Domain (NativeGoldLookupVerification.batchContext ctx progress))
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts)
    (noBad : ¬CheckpointCollision.Bad shape (reconstructed dummy history)) :
    NativeDeferredBatchOwnership.OriginalCall ctx.registry progress.state receipt.call ∧
      receipt.work.root = receipt.call.oracle.root ∧ receipt.work.width = receipt.call.oracle.parameters.width.val ∧
      receipt.work.binding.queries = receipt.call.queries ∧ receipt.work.binding.values = receipt.call.values ∧
      HasSource dummy (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) receipt.work history world := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress (.verification result) executed
  have bodyFramed := NativeLookupBodyFraming.prepared_body ctx chooseHelper memory world prepared origin.1 framed bodyDomain
  exact lookup_from_body dummy ctx chooseHelper chooseBatch memory world prepared progress result executed bodyFramed helpers claims domain history truthful observed receipt member noBad

end
end FormalProof4FHE.HasteBoots.NativeFramedDeferredAvailability
