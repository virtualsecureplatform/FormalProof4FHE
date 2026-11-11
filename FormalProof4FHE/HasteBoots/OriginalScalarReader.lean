module
public import FormalProof4FHE.HasteBoots.ScalarParentRecovery
public import FormalProof4FHE.HasteBoots.OriginalReceiptSegmentation
@[expose] public section

/-! An original successful lookup/scalar execution supplies all completed
reader recovery premises, retaining only the existing framing domains. -/
namespace FormalProof4FHE.HasteBoots.OriginalScalarReader
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


def original (origin : Origin row registry helper parent requests proof lookupFuel equalityFuel scalarFuel world result)
    (rootsFit : (NativeRootMessage.encode proof.roots.val proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement proof.algebra scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).1.completed) :
    ScalarParentRecovery.Completed where
  transcript := origin.ready.equality.transcript
  statement := origin.ready.statement
  proof := proof.algebra
  world := world
  fuel := scalarFuel
  entry := entry
  framed := by
    have old := (LookupInitialReceipt.start world
      (OracleProgram.run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.1 proof.multiplicities).1
    have extension := NativeLookupTranscriptExtension.ready_extends requests.property.le (models requests) origin.geometry.geometry.1
      proof.values.multiplicities proof.values.roots proof.roots.property 7 lookupFuel equalityFuel
      (childStart row registry helper parent requests proof world) world origin.ready origin.prepared (by decide +kernel) rootsFit
    obtain ⟨suffix,valid,bytes,_⟩ := extension
    exact (ReceiptSequence.append _ _ suffix old valid bytes).1
  accepted := by
    obtain ⟨bound,_,accepted,_⟩ := NativeSharedLookupBody.finished_preflight origin.ready.equality.transcript origin.ready.statement
      proof.algebra scalarFuel world result.claims origin.scalar
    exact ⟨bound,accepted⟩
  statementFits := statementFits
  domain := domain
  member := member

end
end FormalProof4FHE.HasteBoots.OriginalScalarReader
