module
public import FormalProof4FHE.HasteBoots.ScalarReceiptMatching
@[expose] public section

/-! Actual original producer and equality records supply receipt positions in
the scalar-bound view. Producer membership chooses its real completed index;
EQ uses its original prepared-job ordinal. No receipt-output witness is supplied. -/
namespace FormalProof4FHE.HasteBoots.OriginalScalarReceiptPosition
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



theorem producer (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
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
    ∃ position : ℕ,
      ScalarReceiptMatching.receiptAt (ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member)
        (.compression position) = some (ReceiptFrameView.frame world first.coefficients.phase) ∧
      ScalarReceiptMatching.receiptAt (ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member)
        (.offset position) = some (ReceiptFrameView.frame world last.coefficients.phase) := by
  obtain ⟨position,found⟩ := List.mem_iff_get.mp job.producerMember
  have getter : (NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis 7 lookupFuel
      (NativeLookupBatch.initial (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
        (childStart row registry helper parent requests proof world)) world).1.completed[position.val]? = some job.view.producer := by
    rw [List.getElem?_eq_getElem position.isLt]
    exact congrArg some found
  refine ⟨position.val,?_,?_⟩
  · change ((NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis 7 lookupFuel
        (NativeLookupBatch.initial (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
          (childStart row registry helper parent requests proof world)) world).1.completed.map
          (fun record => record.selection.draws.map (fun draw => ReceiptFrameView.frame world draw.coefficients.phase)))[position.val]?.bind List.head? = _
    rw [List.getElem?_map,getter,Option.map_some,Option.bind_some,List.head?_map,firstAt,Option.map_some]
  · change ((NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis 7 lookupFuel
        (NativeLookupBatch.initial (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
          (childStart row registry helper parent requests proof world)) world).1.completed.map
          (fun record => record.selection.draws.map (fun draw => ReceiptFrameView.frame world draw.coefficients.phase)))[position.val]?.bind List.getLast? = _
    rw [List.getElem?_map,getter,Option.map_some,Option.bind_some,List.getLast?_map,lastAt,Option.map_some]

theorem equality (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    {index : Fin origin.ready.jobs.length} (job : LookupExecutionJob.Job origin index)
    (rootsFit : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).1.completed) :
    ∃ draw : NativeLookupEquality.Draw origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3,
      NativeGoldLookupEquality.DrawEvidence draw (List.ofFn job.view.eqPoint) ∧
      ScalarReceiptMatching.receiptAt (ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member)
        (.equalityPoint index.val) = some (ReceiptFrameView.frame world draw.coefficients.phase) := by
  obtain ⟨draw,found,evidence⟩ := job.equality
  refine ⟨draw,evidence,?_⟩
  change (origin.ready.machine.draws.map (fun draw => ReceiptFrameView.frame world draw.coefficients.phase))[index.val]? = _
  rw [List.getElem?_map,found,Option.map_some]

end
end FormalProof4FHE.HasteBoots.OriginalScalarReceiptPosition
