module
public import FormalProof4FHE.HasteBoots.LookupExecutionJob
public import FormalProof4FHE.HasteBoots.LookupPreludeReceiptOrder
@[expose] public section

/-! Original successful native execution supplies the exact prelude receipt
sequence and its initial framing, without a caller-supplied header certificate. -/
namespace FormalProof4FHE.HasteBoots.OriginalLookupReceiptOrder
open NativeBrakedownContext (RowDescription Parameters)
open NativeSharedLookupParent (Oracle models)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open NativeSharedLookupBody (Bound)
open LookupExecutionOrigin (Origin childStart)
noncomputable section

variable {C S B : Type} {row : RowDescription C} {registry : Vector (Oracle C)} {helper : Parameters C}
  {parent : Transcript} {requests : Vector Request} {proof : NativeSharedLookupProofData.Proof S B}
  {lookupFuel equalityFuel scalarFuel : ℕ} {world : World} {result : Bound}


open NativeTranscriptExtension (Extends)


theorem sequence (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (rootsFit : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit) :
    ReceiptFrameView.frames origin.ready.equality.transcript.input =
      ReceiptFrameView.frames (childStart row registry helper parent requests proof world).input ++
      (NativeLookupBatch.execute NativeExtensionFields.goldilocksBasis 7 lookupFuel
        (NativeLookupBatch.initial (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
          (childStart row registry helper parent requests proof world)) world).1.completed.flatMap
        (fun entry => entry.selection.draws.map (fun draw => ReceiptFrameView.frame world draw.coefficients.phase)) ++
      origin.ready.machine.draws.map (fun draw => ReceiptFrameView.frame world draw.coefficients.phase) := by
  have header := NativeForkAncestry.start_header world
    (OracleProgram.run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 proof.multiplicities
  obtain ⟨suffix,valid,bytes⟩ := header
  have decoded := TranscriptFrame.decodeAll_encodeMany _ valid
  rw [← bytes] at decoded
  have old : ReceiptSequence.Framed (childStart row registry helper parent requests proof world) := ⟨_,decoded⟩
  exact LookupPreludeReceiptOrder.protocol requests.property.le (models requests) origin.geometry.geometry.1
    proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
    (childStart row registry helper parent requests proof world) world origin.ready old (by decide +kernel) rootsFit origin.prepared

end
end FormalProof4FHE.HasteBoots.OriginalLookupReceiptOrder
