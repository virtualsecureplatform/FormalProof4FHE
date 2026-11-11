module
public import FormalProof4FHE.HasteBoots.ScalarReceiptLineage
public import FormalProof4FHE.HasteBoots.ReceiptFrameView
@[expose] public section

/-! Receipt frames of actual original lookup and equality draws are exposed
by structural decoding of every completed scalar reader input. -/
namespace FormalProof4FHE.HasteBoots.ScalarReceiptFrames
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


theorem producer (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    {index : Fin origin.ready.jobs.length} (job : LookupExecutionJob.Job origin index)
    (draw : NativeLookupChallenge.Draw NativeExtensionFields.Goldilocks3) (drawMember : draw ∈ job.view.producer.selection.draws)
    (rootsFit : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).1.completed) :
    ReceiptFrameView.frame world draw.coefficients.phase ∈ ReceiptFrameView.frames entry.coefficients.phase.pending.input := by
  have ancestry := NativeLookupTranscriptExtension.batch_execute
    (childStart row registry helper parent requests proof world) NativeExtensionFields.goldilocksBasis 7 lookupFuel _ world (by decide +kernel)
    (NativeLookupTranscriptExtension.batch_initial _
      (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling)))
  have reader := (ancestry.2 _ job.producerMember).2 draw drawMember
  have header := reader.1.header (NativeForkAncestry.start_header world
    (OracleProgram.run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 proof.multiplicities)
  obtain ⟨suffix,valid,bytes⟩ := header
  have decoded := TranscriptFrame.decodeAll_encodeMany _ valid
  rw [← bytes] at decoded
  exact ReceiptFrameView.member world draw.coefficients.phase _ _ decoded reader.2
    (ScalarReceiptLineage.producer origin job draw drawMember rootsFit statementFits domain entry member)

theorem equality (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (draw : NativeLookupEquality.Draw origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3)
    (drawMember : draw ∈ origin.ready.machine.draws)
    (rootsFit : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).1.completed) :
    ReceiptFrameView.frame world draw.coefficients.phase ∈ ReceiptFrameView.frames entry.coefficients.phase.pending.input := by
  obtain ⟨child,earlier,_,readers⟩ := NativeLookupTranscriptExtension.ready_origins requests.property.le (models requests) origin.geometry.geometry.1
    proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
    (childStart row registry helper parent requests proof world) world origin.ready origin.prepared (by decide +kernel)
  have reader := readers.2.2 draw drawMember
  have header := reader.1.header ((NativeLookupTranscriptExtension.bind_roots child proof.values.roots proof.roots.property rootsFit).header
    (earlier.header (NativeForkAncestry.start_header world
      (OracleProgram.run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 proof.multiplicities)))
  obtain ⟨suffix,valid,bytes⟩ := header
  have decoded := TranscriptFrame.decodeAll_encodeMany _ valid
  rw [← bytes] at decoded
  exact ReceiptFrameView.member world draw.coefficients.phase _ _ decoded reader.2
    (ScalarReceiptLineage.equality origin draw drawMember statementFits domain entry member)

end
end FormalProof4FHE.HasteBoots.ScalarReceiptFrames
