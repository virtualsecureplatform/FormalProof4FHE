module
public import FormalProof4FHE.HasteBoots.LookupOffsetOrdinal
@[expose] public section

/-! The original first compression input identifies its job by the number
of preceding compression receipts, without a rejection-count certificate. -/
namespace FormalProof4FHE.HasteBoots.LookupCompressionOrdinal
open InputIndexedOracle (World)
open ReceiptFrameView (frames)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open LookupCompressionCount (count fromInput)
open OracleProgram (run)
noncomputable section

theorem original {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) {index : Fin origin.ready.jobs.length}
    (job : LookupExecutionJob.Job origin index) (first : NativeLookupChallenge.Draw Goldilocks3)
    (firstAt : job.view.producer.selection.draws.head? = some first) :
    fromInput first.coefficients.phase.pending.input = index.val := by
  let transcript := LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world
  let actions := NativeLookupBatch.schedule ctx.requests.property.le (fun i => (NativeSharedLookupParent.models ctx.requests i).sampling)
  let batch := NativeLookupBatch.execute goldilocksBasis 7 ctx.lookupFuel (NativeLookupBatch.initial actions transcript) world
  have initial := LookupInitialReceipt.start world
    (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.1 ctx.proof.multiplicities
  have indexed := (LookupJobReceiptPrefix.initialized goldilocksBasis 7 ctx.lookupFuel actions transcript world initial.1 (by decide +kernel)).2
  have producerAt := LookupProducerOrdinal.producer_at origin job
  have before := indexed index.val _ producerAt
  have labels := (LookupBatchReceiptLabels.execute goldilocksBasis 7 ctx.lookupFuel _ world (LookupBatchReceiptLabels.initial actions transcript)).2
  have priorCount : count (LookupJobReceiptPrefix.emitted world (batch.1.completed.take index.val)) = index.val := by
    rw [LookupCompressionCount.emitted world _ (fun entry present => labels entry (List.mem_of_mem_take present))]
    rw [List.length_take,Nat.min_eq_left (Nat.le_of_lt (List.getElem?_eq_some_iff.mp producerAt).1)]
  have initialCount : fromInput transcript.input = 0 := LookupCompressionCount.start world _ ctx.proof.multiplicities
  have earlierCount : count (frames transcript.input ++ LookupJobReceiptPrefix.emitted world (batch.1.completed.take index.val)) = index.val := by
    rw [LookupCompressionCount.append,priorCount]
    change fromInput transcript.input + index.val = index.val
    rw [initialCount,Nat.zero_add]
  have found : job.view.producer.selection.draws[0]? = some first := by simpa only [List.head?_eq_getElem?] using firstAt
  have firstPrefix := before.2 0 first found
  simp only [List.take_zero,List.map_nil,List.append_nil] at firstPrefix
  unfold fromInput
  rw [firstPrefix]
  exact earlierCount

end
end FormalProof4FHE.HasteBoots.LookupCompressionOrdinal
