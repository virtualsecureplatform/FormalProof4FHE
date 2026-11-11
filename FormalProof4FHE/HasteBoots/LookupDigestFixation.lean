module
public import FormalProof4FHE.HasteBoots.ReceiptDigestFixation
public import FormalProof4FHE.HasteBoots.LookupConsumedTrace
@[expose] public section

/-! Typed lookup scalars and equality points inherit receipt-based fixation
on the refined replay fiber. Digest binding and named-key membership stay
explicit, as does the SHAKE receipt collision alternative. -/
namespace FormalProof4FHE.HasteBoots.LookupDigestFixation
open InputIndexedOracle (World)
open NativeTranscript (Execution)
open ReceiptCandidateCompletion (digest extend)
noncomputable section
variable {p degree count : ℕ} {K : Type} [Field K] [Algebra (ZMod p) K]

theorem scalar {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world other : World) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (positive : 0 < CanonicalByteSampler.byteCount p)
    (left right : NativeLookupChallenge.Machine K)
    (leftTrace : LookupConsumedTrace.Lookup p left) (rightTrace : LookupConsumedTrace.Lookup p right)
    (leftValid : NativeLookupChallenge.MachineValid basis left) (rightValid : NativeLookupChallenge.MachineValid basis right)
    (leftDraw rightDraw : NativeLookupChallenge.Draw K) (leftMember : leftDraw ∈ left.draws) (rightMember : rightDraw ∈ right.draws)
    (leftNamed : leftDraw.coefficients.phase.consumed ∈ ReceiptPayloadView.payloads (past world).run.2)
    (rightNamed : rightDraw.coefficients.phase.consumed ∈ ReceiptPayloadView.payloads (past other).run.2)
    (same : (extend past other).run = (extend past world).run)
    (sameDigest : digest other rightDraw.coefficients.phase.consumed = digest world leftDraw.coefficients.phase.consumed) :
    rightDraw.value = leftDraw.value ∨ ReceiptDigestFixation.Collision (past world).run.2 world := by
  rcases ReceiptDigestFixation.coefficients_on_fiber replay world other p positive _ _
    (leftTrace.2 leftDraw leftMember) (rightTrace.2 rightDraw rightMember) leftNamed rightNamed same sameDigest with equal | bad
  · exact Or.inl ((rightValid.2 rightDraw rightMember).2.2.trans
      ((congrArg (TypedFieldRequest.scalarValue basis) equal).trans (leftValid.2 leftDraw leftMember).2.2.symm))
  · exact Or.inr bad

theorem point {A : Type} {past : World → Execution A} (replay : ObservationReplay.Replayable past)
    (world other : World) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (positive : 0 < CanonicalByteSampler.byteCount p)
    (left right : NativeLookupEquality.Machine count K)
    (leftTrace : LookupConsumedTrace.Equality p left) (rightTrace : LookupConsumedTrace.Equality p right)
    (leftValid : NativeLookupEquality.Valid basis left) (rightValid : NativeLookupEquality.Valid basis right)
    (leftDraw rightDraw : NativeLookupEquality.Draw count K) (leftMember : leftDraw ∈ left.draws) (rightMember : rightDraw ∈ right.draws)
    (leftNamed : leftDraw.coefficients.phase.consumed ∈ ReceiptPayloadView.payloads (past world).run.2)
    (rightNamed : rightDraw.coefficients.phase.consumed ∈ ReceiptPayloadView.payloads (past other).run.2)
    (same : (extend past other).run = (extend past world).run)
    (sameDigest : digest other rightDraw.coefficients.phase.consumed = digest world leftDraw.coefficients.phase.consumed) :
    rightDraw.point = leftDraw.point ∨ ReceiptDigestFixation.Collision (past world).run.2 world := by
  rcases ReceiptDigestFixation.coefficients_on_fiber replay world other p positive _ _
    (leftTrace.2 leftDraw leftMember) (rightTrace.2 rightDraw rightMember) leftNamed rightNamed same sameDigest with equal | bad
  · exact Or.inl ((rightValid.2 rightDraw rightMember).2.2.trans
      ((congrArg (TypedFieldVector.value basis count) equal).trans (leftValid.2 leftDraw leftMember).2.2.symm))
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.LookupDigestFixation
