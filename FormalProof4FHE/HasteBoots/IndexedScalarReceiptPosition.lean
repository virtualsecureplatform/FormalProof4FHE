module
public import FormalProof4FHE.HasteBoots.OriginalScalarReceiptPosition
public import FormalProof4FHE.HasteBoots.LookupProducerOrdinal
public import FormalProof4FHE.HasteBoots.LookupProducedEndpoints
public import FormalProof4FHE.HasteBoots.LookupProducerConsumed
@[expose] public section

/-! Original compression and accepted-offset receipts use the prepared-job
ordinal. Actual production supplies both endpoint records and their decoders. -/
namespace FormalProof4FHE.HasteBoots.IndexedScalarReceiptPosition
open InputIndexedOracle (World)
noncomputable section
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle models)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open LookupExecutionOrigin (Origin childStart)
variable {C S B : Type} {row : RowDescription C} {registry : Vector (Oracle C)} {helper : Parameters C}
  {parent : NativeTranscript.Transcript} {requests : Vector Request} {proof : NativeSharedLookupProofData.Proof S B}
  {lookupFuel equalityFuel scalarFuel : ℕ} {world : World} {result : NativeSharedLookupBody.Bound}



theorem producer_at (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    {index : Fin origin.ready.jobs.length} (job : LookupExecutionJob.Job origin index)
    (rootsFit : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).1.completed)
    (first last : NativeLookupChallenge.Draw NativeExtensionFields.Goldilocks3)
    (firstAt : job.view.producer.selection.draws.head? = some first)
    (lastAt : job.view.producer.selection.draws.getLast? = some last) :
      ScalarReceiptMatching.receiptAt (ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member)
        (.compression index.val) = some (ReceiptFrameView.frame world first.coefficients.phase) ∧
      ScalarReceiptMatching.receiptAt (ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member)
        (.offset index.val) = some (ReceiptFrameView.frame world last.coefficients.phase) := by
  have getter := LookupProducerOrdinal.producer_at origin job
  constructor
  · change ((NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis 7 lookupFuel
        (NativeLookupBatch.initial (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
          (childStart row registry helper parent requests proof world)) world).1.completed.map
          (fun record => record.selection.draws.map (fun draw => ReceiptFrameView.frame world draw.coefficients.phase)))[index.val]?.bind List.head? = _
    rw [List.getElem?_map,getter,Option.map_some,Option.bind_some,List.head?_map,firstAt,Option.map_some]
  · change ((NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis 7 lookupFuel
        (NativeLookupBatch.initial (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
          (childStart row registry helper parent requests proof world)) world).1.completed.map
          (fun record => record.selection.draws.map (fun draw => ReceiptFrameView.frame world draw.coefficients.phase)))[index.val]?.bind List.getLast? = _
    rw [List.getElem?_map,getter,Option.map_some,Option.bind_some,List.getLast?_map,lastAt,Option.map_some]

theorem endpoints (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    {index : Fin origin.ready.jobs.length} (job : LookupExecutionJob.Job origin index)
    (rootsFit : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).1.completed) :
    ∃ first last : NativeLookupChallenge.Draw NativeExtensionFields.Goldilocks3,
      ScalarReceiptMatching.receiptAt (ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member)
        (.compression index.val) = some (ReceiptFrameView.frame world first.coefficients.phase) ∧
      ScalarReceiptMatching.receiptAt (ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member)
        (.offset index.val) = some (ReceiptFrameView.frame world last.coefficients.phase) ∧
      NativeGoldLookupProducer.decode first.coefficients.values = some (origin.ready.jobs.get index).output.y ∧
      NativeGoldLookupProducer.decode last.coefficients.values = some (origin.ready.jobs.get index).output.r ∧
      FieldConsumedReplay.Traced NativeFields.goldilocksModulus first.coefficients ∧
      FieldConsumedReplay.Traced NativeFields.goldilocksModulus last.coefficients := by
  obtain ⟨first,last,firstAt,lastAt,yDecode,rDecode⟩ := LookupProducedEndpoints.draws _ _ _ _ job.view.produced
  have positions := producer_at origin job rootsFit statementFits domain entry member first last firstAt lastAt
  have traces := LookupProducerConsumed.producer origin job
  refine ⟨first,last,positions.1,positions.2,yDecode,rDecode,?_,?_⟩
  · exact traces.2 first (List.mem_of_mem_head? (by rw [firstAt]; rfl))
  · exact traces.2 last (List.mem_of_mem_getLast? (by rw [lastAt]; rfl))

end
end FormalProof4FHE.HasteBoots.IndexedScalarReceiptPosition
