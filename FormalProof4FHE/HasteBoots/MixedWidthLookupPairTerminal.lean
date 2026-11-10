module
public import FormalProof4FHE.HasteBoots.MixedWidthLookupScalarSubclaim
public import FormalProof4FHE.HasteBoots.MixedWidthLookupOpeningFamily
@[expose] public section

/-! The existing computed local check exposes joint scalar truth or a wrong
original source/helper opening, with independently packed original helpers. -/
namespace FormalProof4FHE.HasteBoots.MixedWidthLookupPairTerminal
open scoped BigOperators Classical
open PackedSumcheckSubclaim
open LookupPairTerminal (check check_sound coefficients_finish_encode sum_truthful_or_wrong)
open MixedWidthLookupOpeningFamily (WrongOpenings)
noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {d padding helperPadding c row count : ℕ}

/-- A computed partial-table terminal check exposes exactly the original PCS
obligations needed by the concrete pair arithmetic theorem. -/
theorem partial_truthful_or_wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K) (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F)
    (claim : Subclaim K 1 (c + row)) (claims : Fin count → Fin (d + padding) → F) (helper : K)
    (accepted : check basis shape eqPoint (ScalarSumcheckQuery.point claim.query) r y active enough claims helper (claim.expected 0) = true) :
    ScalarSumcheckOracle.MLETruthful ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient r) ExtensionLookupIdentity.partialIndices
      (ExtensionLookupIdentity.factors eqPoint y (fun i => LookupSourceFlattening.flatten shape (sources i))
        (fun cell => PaddedExtension.decode basis (helpers cell)) active) (some (claim, ())) ∨
      (∃ i, claims i ≠ (ExtensionLookupTerminal.sourceQuery basis shape (ScalarSumcheckQuery.point claim.query)).query.fold (sources i)) ∨
      PaddedExtension.encode (padding := helperPadding) basis helper ≠ (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point claim.query)).query.fold helpers := by
  obtain ⟨values, decoded, identity⟩ := check_sound basis shape eqPoint _ r y active enough claims helper _ accepted
  exact MixedWidthLookupScalarSubclaim.checked_partial_or_wrong basis shape eqPoint r y active enough sources helpers claim () claims
    (PaddedExtension.encode (padding := helperPadding) basis helper) values helper decoded
    (by rw [coefficients_finish_encode, PaddedExtension.element_encode]) identity

/-- Full-table checker uses the same literal formula and retains the
smaller degree-three arithmetic event. -/
theorem full_truthful_or_wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F)
    (claim : Subclaim K 1 (c + row)) (claims : Fin count → Fin (d + padding) → F) (helper : K)
    (accepted : check basis shape eqPoint (ScalarSumcheckQuery.point claim.query) r y (2 ^ (c + row)) le_rfl claims helper (claim.expected 0) = true) :
    ScalarSumcheckOracle.MLETruthful ExtensionLookupIdentity.fullArity
      (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
      (fun factor cell => if factor = .hash then
        ExtensionLookupIdentity.hashTable y (fun i => LookupSourceFlattening.flatten shape (sources i)) cell + r else
        ExtensionLookupIdentity.factors eqPoint y (fun i => LookupSourceFlattening.flatten shape (sources i))
          (fun cell => PaddedExtension.decode basis (helpers cell)) (2 ^ (c + row)) factor cell) (some (claim, ())) ∨
      (∃ i, claims i ≠ (ExtensionLookupTerminal.sourceQuery basis shape (ScalarSumcheckQuery.point claim.query)).query.fold (sources i)) ∨
      PaddedExtension.encode (padding := helperPadding) basis helper ≠ (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point claim.query)).query.fold helpers := by
  obtain ⟨values, decoded, identity⟩ := check_sound basis shape eqPoint _ r y (2 ^ (c + row)) le_rfl claims helper _ accepted
  exact MixedWidthLookupScalarSubclaim.checked_full_or_wrong basis shape eqPoint r y sources helpers claim () claims
    (PaddedExtension.encode (padding := helperPadding) basis helper) values helper decoded
    (by rw [coefficients_finish_encode, PaddedExtension.element_encode]) identity

/-- The complete local partial check implies the joint arithmetic event or
one of the sum-helper, identity-helper and original-source opening failures. -/
theorem partial_joint_or_wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K) (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F)
    (sumClaim zeroClaim : Subclaim K 1 (c + row)) (claims : Fin count → Fin (d + padding) → F) (helper : K)
    (accepted : check basis shape eqPoint (ScalarSumcheckQuery.point zeroClaim.query) r y active enough claims helper (zeroClaim.expected 0) = true) :
    LookupPairSequence.JointTruthful ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient r) ExtensionLookupIdentity.partialIndices
      (fun eqPoint => ExtensionLookupIdentity.factors eqPoint y (fun i => LookupSourceFlattening.flatten shape (sources i))
        (fun cell => PaddedExtension.decode basis (helpers cell)) active)
      (fun cell => PaddedExtension.decode basis (helpers cell))
      (some (sumClaim, ()), some (eqPoint, some (zeroClaim, ()))) ∨
      WrongOpenings basis shape sources helpers sumClaim zeroClaim claims helper := by
  rcases sum_truthful_or_wrong basis sumClaim helpers with sumTrue | sumWrong
  · rcases partial_truthful_or_wrong basis shape eqPoint r y active enough sources helpers zeroClaim claims helper accepted with
      zeroTrue | zeroWrong
    · exact Or.inl ⟨sumTrue, zeroTrue⟩
    · exact Or.inr (Or.inr zeroWrong)
  · exact Or.inr (Or.inl sumWrong)

/-- Full-table version retains its degree-three joint event and the same
three original opening obligations. -/
theorem full_joint_or_wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F)
    (sumClaim zeroClaim : Subclaim K 1 (c + row)) (claims : Fin count → Fin (d + padding) → F) (helper : K)
    (accepted : check basis shape eqPoint (ScalarSumcheckQuery.point zeroClaim.query) r y (2 ^ (c + row)) le_rfl claims helper (zeroClaim.expected 0) = true) :
    LookupPairSequence.JointTruthful ExtensionLookupIdentity.fullArity
      (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
      (fun eqPoint => LookupPairArithmetic.fullTables eqPoint r y (fun i => LookupSourceFlattening.flatten shape (sources i))
        (fun cell => PaddedExtension.decode basis (helpers cell)))
      (fun cell => PaddedExtension.decode basis (helpers cell))
      (some (sumClaim, ()), some (eqPoint, some (zeroClaim, ()))) ∨
      WrongOpenings basis shape sources helpers sumClaim zeroClaim claims helper := by
  rcases sum_truthful_or_wrong basis sumClaim helpers with sumTrue | sumWrong
  · rcases full_truthful_or_wrong basis shape eqPoint r y sources helpers zeroClaim claims helper accepted with
      zeroTrue | zeroWrong
    · exact Or.inl ⟨sumTrue, zeroTrue⟩
    · exact Or.inr (Or.inr zeroWrong)
  · exact Or.inr (Or.inl sumWrong)

end
end FormalProof4FHE.HasteBoots.MixedWidthLookupPairTerminal
