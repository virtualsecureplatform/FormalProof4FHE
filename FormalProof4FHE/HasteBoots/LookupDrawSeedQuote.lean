module
public import FormalProof4FHE.HasteBoots.LookupScalarSeedQuote
public import FormalProof4FHE.HasteBoots.LookupExecutionJob
@[expose] public section

/-! Every retained original lookup draw, including rejected offsets, quotes
the actual caller fork seed. This needs no later helper-root frame or scalar
statement and does not assume a sampled-seed equality. -/
namespace FormalProof4FHE.HasteBoots.LookupDrawSeedQuote
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem quote {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) {index : Fin origin.ready.jobs.length}
    (job : LookupExecutionJob.Job origin index) (draw : NativeLookupChallenge.Draw Goldilocks3)
    (member : draw ∈ job.view.producer.selection.draws) :
    NativeChildSeedView.quote draw.coefficients.phase.pending.input =
      some (InputIndexedOracle.block world (LookupScalarSeedQuote.forkInput ctx world) 0 64) := by
  let transcript := LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world
  have batch := NativeLookupTranscriptExtension.batch_execute transcript goldilocksBasis 7 ctx.lookupFuel
    (NativeLookupBatch.initial (NativeLookupBatch.schedule ctx.requests.property.le
      (fun i => (NativeSharedLookupParent.models ctx.requests i).sampling)) transcript) world (by decide +kernel)
    (NativeLookupTranscriptExtension.batch_initial _ _)
  have retained := (batch.2 job.view.producer job.producerMember).2 draw member
  have header := NativeForkAncestry.start_header world
    (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.1
    ctx.proof.multiplicities
  exact (retained.1.header header).quote

end
end FormalProof4FHE.HasteBoots.LookupDrawSeedQuote
