module
public import FormalProof4FHE.HasteBoots.OriginalScalarReader
@[expose] public section

/-! Equal completed outer scalar inputs bind the original prelude and its
ordered lookup/EQ receipt groups, without independently supplied parent or
boundary-count equalities. -/
namespace FormalProof4FHE.HasteBoots.ScalarReceiptSegmentation
open InputIndexedOracle (World)
noncomputable section

structure View where
  prelude : OriginalReceiptSegmentation.View
  reader : ScalarParentRecovery.Completed
  linked : reader.transcript.input = prelude.transcript.input

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
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement proof.algebra) world).1.completed) : View :=
  ⟨OriginalReceiptSegmentation.original origin rootsFit,
    OriginalScalarReader.original origin rootsFit statementFits domain entry member,rfl⟩

theorem prelude_equal (left right : View)
    (same : left.reader.entry.coefficients.phase.pending.input = right.reader.entry.coefficients.phase.pending.input) :
    left.prelude.transcript.input = right.prelude.transcript.input := by
  have parents := (ScalarParentRecovery.compare left.reader right.reader same).1
  exact left.linked.symm.trans (parents.trans right.linked)

/-- The two views may be built from different worlds, contexts, proofs,
rounds and budgets. Only equality of their actual reader inputs is supplied. -/
theorem compare (left right : View)
    (same : left.reader.entry.coefficients.phase.pending.input = right.reader.entry.coefficients.phase.pending.input) :
    left.prelude.groups = right.prelude.groups ∧ left.prelude.equality = right.prelude.equality :=
  OriginalReceiptSegmentation.compare left.prelude right.prelude (prelude_equal left right same)

end
end FormalProof4FHE.HasteBoots.ScalarReceiptSegmentation
