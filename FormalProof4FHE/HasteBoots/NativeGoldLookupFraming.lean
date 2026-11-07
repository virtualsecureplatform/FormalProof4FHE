module

public import FormalProof4FHE.HasteBoots.NativeLookupBodyFraming
public import FormalProof4FHE.HasteBoots.NativeSourceClaimFraming
@[expose] public section

/-! Dispatcher receipt framing follows from original parent framing and the
existing stage message domains. No future receipt framing is supplied. Native
serialization/allocation refinement and physical-work security remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldLookupFraming
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeGoldLookupVerification (Prepared program batchContext)
open NativeDeferredBatchVerification (Receipt Result)
open NativeTranscriptFraming (Framed)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem prepared_parent {Memory : Type} (ctx : Context (Vector Opening))
    (choose : NativeGoldPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (prepared : Prepared Memory)
    (executed : NativeGoldLookupVerification.prepare (run (NativeRegisteredLookup.helpers ctx choose memory) world).run.1 = some prepared)
    (framed : Framed ctx.parent)
    (bodyDomain : NativeLookupBodyFraming.Domain ctx.registry ctx.requests ctx.proof)
    (helperDomain : NativeGoldHelperFraming.Domain prepared.plan.calls) :
    Framed prepared.helpers.lastAccepted :=
  NativeGoldHelperFraming.prepared_framed ctx choose memory world prepared executed
    (NativeLookupBodyFraming.prepared_body ctx choose memory world prepared executed framed bodyDomain) helperDomain

theorem source_parent {Memory : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : NativeDeferredBatchVerification.Outcome Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress result)
    (framed : Framed ctx.parent)
    (bodyDomain : NativeLookupBodyFraming.Domain ctx.registry ctx.requests ctx.proof)
    (helperDomain : NativeGoldHelperFraming.Domain prepared.plan.calls)
    (sourceDomain : NativeSourceClaimFraming.Domain ctx.registry ctx.requests prepared.query ctx.proof.sources) :
    Framed progress.state.parent := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress result executed
  have initial := prepared_parent ctx chooseHelper memory world prepared origin.1 framed bodyDomain helperDomain
  have preserved := NativeSourceClaimFraming.program_framed NativeGoldBlockCode.description.row ctx.registry ctx.requests prepared.query
    ctx.proof.sources (NativeGoldLookupVerification.initial prepared) world initial sourceDomain
  change Framed (run (NativeGoldLookupVerification.sourceProgram ctx prepared) world).run.1.progress.state.parent at preserved
  rw [origin.2.1] at preserved
  exact preserved

theorem receipt_framed {Memory : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (prepared : Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (result : Result Memory)
    (executed : (run (program ctx chooseHelper chooseBatch memory) world).run.1.phase = .batches prepared progress (.verification result))
    (framed : Framed ctx.parent)
    (bodyDomain : NativeLookupBodyFraming.Domain ctx.registry ctx.requests ctx.proof)
    (helperDomain : NativeGoldHelperFraming.Domain prepared.plan.calls)
    (sourceDomain : NativeSourceClaimFraming.Domain ctx.registry ctx.requests prepared.query ctx.proof.sources)
    (batchDomain : NativeDeferredBatchFraming.Domain (batchContext ctx progress))
    (receipt : Receipt Memory) (member : receipt ∈ result.progress.receipts) :
    NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before) := by
  have origin := NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world prepared progress _ executed
  exact NativeDeferredBatchFraming.receipt_framed (batchContext ctx progress) chooseBatch prepared.helpers.memory world result origin.2.2.1
    (source_parent ctx chooseHelper chooseBatch memory world prepared progress _ executed framed bodyDomain helperDomain sourceDomain)
    batchDomain receipt member
end
end FormalProof4FHE.HasteBoots.NativeGoldLookupFraming
