module
public import FormalProof4FHE.HasteBoots.LookupFactorFixation
@[expose] public section

/-! Actual original jobs supply fixed-position lookup scalar and EQ samples,
including their native raw values, coefficient traces and receipt bindings.
No independent sampler, decoder or receipt-position certificate is required. -/
namespace FormalProof4FHE.HasteBoots.OriginalLookupFactorSamples
open InputIndexedOracle (World)
open LookupFactorFixation (Sample Scalar Point)
noncomputable section
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle models)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open LookupExecutionOrigin (Origin childStart)
variable {C S B : Type} {row : RowDescription C} {registry : Vector (Oracle C)} {helper : Parameters C}
  {parent : NativeTranscript.Transcript} {requests : Vector Request} {proof : NativeSharedLookupProofData.Proof S B}
  {lookupFuel equalityFuel scalarFuel : ℕ} {world : World} {result : NativeSharedLookupBody.Bound}



theorem scalars (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    {index : Fin origin.ready.jobs.length} (job : LookupExecutionJob.Job origin index)
    (rootsFit : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).1.completed) :
    ∃ compression offset : Scalar,
      compression.view = ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member ∧
      offset.view = ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member ∧
      compression.position = .compression index.val ∧ offset.position = .offset index.val ∧
      compression.word = (origin.ready.jobs.get index).output.y ∧ offset.word = (origin.ready.jobs.get index).output.r := by
  obtain ⟨first,last,firstAt,lastAt,yDecode,rDecode,firstTrace,lastTrace⟩ :=
    IndexedScalarReceiptPosition.endpoints origin job rootsFit statementFits domain entry member
  let view := ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member
  let firstSample : Sample := ⟨view,.compression index.val,first.coefficients,firstTrace,firstAt⟩
  let lastSample : Sample := ⟨view,.offset index.val,last.coefficients,lastTrace,lastAt⟩
  exact ⟨⟨firstSample,(origin.ready.jobs.get index).output.y,yDecode⟩,
    ⟨lastSample,(origin.ready.jobs.get index).output.r,rDecode⟩,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem point (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    {index : Fin origin.ready.jobs.length} (job : LookupExecutionJob.Job origin index)
    (rootsFit : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).1.completed) :
    ∃ sample : Point,
      sample.view = ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member ∧
      sample.position = .equalityPoint index.val ∧ sample.point = List.ofFn job.view.eqPoint := by
  obtain ⟨draw,found,evidence⟩ := job.equality
  have present := List.mem_of_getElem? found
  have contract := NativeSharedLookupPrelude.protocol_contract requests.property.le (models requests) origin.geometry.geometry.1
    proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
    (childStart row registry helper parent requests proof world) world origin.ready origin.prepared
  obtain ⟨transcript,_,machine,_⟩ := contract.lookup
  have traces := LookupConsumedTrace.equality_request NativeExtensionFields.goldilocksBasis 7 origin.geometry.geometry.1.val equalityFuel transcript
    proof.values.roots proof.roots.property world
  have valid := NativeLookupEquality.request_valid NativeExtensionFields.goldilocksBasis 7 origin.geometry.geometry.1.val equalityFuel transcript
    proof.values.roots proof.roots.property world
  rw [← machine] at traces valid
  have atReceipt : ScalarReceiptMatching.receiptAt (ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member)
      (.equalityPoint index.val) = some (ReceiptFrameView.frame world draw.coefficients.phase) := by
    change (origin.ready.machine.draws.map (fun draw => ReceiptFrameView.frame world draw.coefficients.phase))[index.val]? = _
    rw [List.getElem?_map,found,Option.map_some]
  let sampled : Sample := ⟨ScalarReceiptSegmentation.original origin rootsFit statementFits domain entry member,
    .equalityPoint index.val,draw.coefficients,traces.2 draw present,atReceipt⟩
  exact ⟨⟨sampled,origin.geometry.geometry.1.val,List.ofFn job.view.eqPoint,(valid.2 draw present).1,evidence.raw⟩,rfl,rfl,rfl⟩

end
end FormalProof4FHE.HasteBoots.OriginalLookupFactorSamples
