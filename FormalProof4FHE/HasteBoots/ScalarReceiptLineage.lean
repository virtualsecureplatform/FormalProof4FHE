module
public import FormalProof4FHE.HasteBoots.LookupExecutionJob
public import FormalProof4FHE.HasteBoots.LookupReceiptBatchLineage
public import FormalProof4FHE.HasteBoots.EqualityReceiptLineage
@[expose] public section

/-! Finalized receipts of original lookup/EQ draws occur in the ancestry of
every actual completed scalar reader. No independent receipt equality is
supplied; only the existing native framing domains are retained. -/
namespace FormalProof4FHE.HasteBoots.ScalarReceiptLineage
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
    Extends (NativeTranscript.finishField world draw.coefficients.phase).run.1 entry.coefficients.phase.pending := by
  have lineage := LookupReceiptBatchLineage.execute NativeExtensionFields.goldilocksBasis 7 lookupFuel _ world (by decide +kernel)
    (LookupReceiptBatchLineage.initial
      (NativeLookupBatch.schedule requests.property.le (fun i => (models requests i).sampling))
      (childStart row registry helper parent requests proof world) world)
  have quoted := lineage.2.2 _ job.producerMember draw drawMember
  have contract := NativeSharedLookupPrelude.protocol_contract requests.property.le (models requests) origin.geometry.geometry.1
    proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
    (childStart row registry helper parent requests proof world) world origin.ready origin.prepared
  obtain ⟨transcript,finished,machine,_⟩ := contract.lookup
  simp only [LookupReceiptBatchLineage.current,finished] at quoted
  have equality := NativeLookupTranscriptExtension.equality_request NativeExtensionFields.goldilocksBasis 7 origin.geometry.geometry.1.val
    equalityFuel transcript proof.values.roots proof.roots.property world (by decide +kernel)
  rw [← machine] at equality
  have ready := (NativeLookupTranscriptExtension.bind_roots transcript proof.values.roots proof.roots.property rootsFit).trans equality.1
  rw [← contract.child] at ready
  have scalar := NativeScalarTranscriptExtension.execute origin.ready.equality.transcript origin.ready.statement proof.algebra scalarFuel _ world domain
    (NativeScalarTranscriptExtension.initial origin.ready.equality.transcript origin.ready.statement proof.algebra statementFits)
  exact quoted.trans (ready.trans (scalar.2.2 entry member).1)

theorem equality (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (draw : NativeLookupEquality.Draw origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3)
    (drawMember : draw ∈ origin.ready.machine.draws)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).1.completed) :
    Extends (NativeTranscript.finishField world draw.coefficients.phase).run.1 entry.coefficients.phase.pending := by
  have contract := NativeSharedLookupPrelude.protocol_contract requests.property.le (models requests) origin.geometry.geometry.1
    proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
    (childStart row registry helper parent requests proof world) world origin.ready origin.prepared
  obtain ⟨transcript,_,machine,_⟩ := contract.lookup
  have lineage := EqualityReceiptLineage.request NativeExtensionFields.goldilocksBasis 7 origin.geometry.geometry.1.val equalityFuel transcript
    proof.values.roots proof.roots.property world (by decide +kernel)
  rw [← machine] at lineage
  have quoted := lineage.2 draw drawMember
  rw [← contract.child] at quoted
  have scalar := NativeScalarTranscriptExtension.execute origin.ready.equality.transcript origin.ready.statement proof.algebra scalarFuel _ world domain
    (NativeScalarTranscriptExtension.initial origin.ready.equality.transcript origin.ready.statement proof.algebra statementFits)
  exact quoted.trans (scalar.2.2 entry member).1

end
end FormalProof4FHE.HasteBoots.ScalarReceiptLineage
