module
public import FormalProof4FHE.HasteBoots.LookupScalarSubclaim
public import FormalProof4FHE.HasteBoots.MixedWidthExtensionLookupTerminal
@[expose] public section

/-! Scalar lookup arithmetic with independently packed original helpers. -/
namespace FormalProof4FHE.HasteBoots.MixedWidthLookupScalarSubclaim
open scoped BigOperators Classical
open PackedSumcheckSubclaim
noncomputable section
variable {F K Memory : Type} [Field F] [Field K] [Algebra F K]
  {d padding helperPadding c row count : ℕ}

theorem partial_truthful_iff (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K) (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F)
    (claim : Subclaim K 1 (c + row)) (memory : Memory) :
    ScalarSumcheckOracle.MLETruthful ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient r) ExtensionLookupIdentity.partialIndices
      (ExtensionLookupIdentity.factors eqPoint y (fun i => LookupSourceFlattening.flatten shape (sources i))
        (fun cell => PaddedExtension.decode basis (helpers cell)) active) (some (claim, memory)) ↔
    claim.expected 0 = ExtensionLookupIdentity.terminal eqPoint (ScalarSumcheckQuery.point claim.query) r
      (∑ i, y ^ i.val * ExtensionLookupTerminal.sourceTruth shape (ScalarSumcheckQuery.point claim.query) (sources i))
      (ExtensionQuery.evaluate (c + row) (ScalarSumcheckQuery.point claim.query)
        (fun cell => PaddedExtension.decode basis (helpers cell))) active enough := by
  simp only [ScalarSumcheckOracle.MLETruthful]
  rw [ExtensionLookupIdentity.partial_terminal, ← LookupSourceFlattening.hash_evaluate shape _ y sources]

theorem full_truthful_iff (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F)
    (claim : Subclaim K 1 (c + row)) (memory : Memory) :
    ScalarSumcheckOracle.MLETruthful ExtensionLookupIdentity.fullArity
      (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
      (fun factor cell => if factor = .hash then
        ExtensionLookupIdentity.hashTable y (fun i => LookupSourceFlattening.flatten shape (sources i)) cell + r else
        ExtensionLookupIdentity.factors eqPoint y (fun i => LookupSourceFlattening.flatten shape (sources i))
          (fun cell => PaddedExtension.decode basis (helpers cell)) (2 ^ (c + row)) factor cell) (some (claim, memory)) ↔
    claim.expected 0 = ExtensionLookupIdentity.terminal eqPoint (ScalarSumcheckQuery.point claim.query) r
      (∑ i, y ^ i.val * ExtensionLookupTerminal.sourceTruth shape (ScalarSumcheckQuery.point claim.query) (sources i))
      (ExtensionQuery.evaluate (c + row) (ScalarSumcheckQuery.point claim.query)
        (fun cell => PaddedExtension.decode basis (helpers cell))) (2 ^ (c + row)) le_rfl := by
  simp only [ScalarSumcheckOracle.MLETruthful]
  rw [ExtensionLookupIdentity.full_terminal, ← LookupSourceFlattening.hash_evaluate shape _ y sources]

/-- A successful local partial-lookup terminal has the actual sumcheck MLE
arithmetic event or a false original source/helper base opening. -/
theorem checked_partial_or_wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K) (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F)
    (claim : Subclaim K 1 (c + row)) (memory : Memory)
    (sourceClaims : Fin count → Fin (d + padding) → F) (helperClaim : Fin (d + helperPadding) → F)
    (sourceValues : Fin count → K) (helperValue : K)
    (sourceDecoded : ∀ i, PaddedExtension.element basis
      ((ExtensionLookupTerminal.sourceQuery basis shape (ScalarSumcheckQuery.point claim.query)).finish (sourceClaims i)) = some (sourceValues i))
    (helperDecoded : PaddedExtension.element basis
      ((ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point claim.query)).finish helperClaim) = some helperValue)
    (checked : ExtensionLookupIdentity.terminal eqPoint (ScalarSumcheckQuery.point claim.query) r
      (∑ i, y ^ i.val * sourceValues i) helperValue active enough = claim.expected 0) :
    ScalarSumcheckOracle.MLETruthful ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient r) ExtensionLookupIdentity.partialIndices
      (ExtensionLookupIdentity.factors eqPoint y (fun i => LookupSourceFlattening.flatten shape (sources i))
        (fun cell => PaddedExtension.decode basis (helpers cell)) active) (some (claim, memory)) ∨
      (∃ i, sourceClaims i ≠
        (ExtensionLookupTerminal.sourceQuery basis shape (ScalarSumcheckQuery.point claim.query)).query.fold (sources i)) ∨
      helperClaim ≠ (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point claim.query)).query.fold helpers := by
  have alternatives := MixedWidthExtensionLookupTerminal.checked_truthful_or_wrong basis shape eqPoint
    (ScalarSumcheckQuery.point claim.query) r y active enough sources helpers sourceClaims helperClaim sourceValues
    helperValue (claim.expected 0) sourceDecoded helperDecoded checked
  exact alternatives.imp_left ((partial_truthful_iff basis shape eqPoint r y active enough sources helpers claim memory).mpr)

/-- The full-table branch uses the degree-three event, with the same original
source/helper opening alternatives and local decoding checks. -/
theorem checked_full_or_wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + helperPadding) → F)
    (claim : Subclaim K 1 (c + row)) (memory : Memory)
    (sourceClaims : Fin count → Fin (d + padding) → F) (helperClaim : Fin (d + helperPadding) → F)
    (sourceValues : Fin count → K) (helperValue : K)
    (sourceDecoded : ∀ i, PaddedExtension.element basis
      ((ExtensionLookupTerminal.sourceQuery basis shape (ScalarSumcheckQuery.point claim.query)).finish (sourceClaims i)) = some (sourceValues i))
    (helperDecoded : PaddedExtension.element basis
      ((ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point claim.query)).finish helperClaim) = some helperValue)
    (checked : ExtensionLookupIdentity.terminal eqPoint (ScalarSumcheckQuery.point claim.query) r
      (∑ i, y ^ i.val * sourceValues i) helperValue (2 ^ (c + row)) le_rfl = claim.expected 0) :
    ScalarSumcheckOracle.MLETruthful ExtensionLookupIdentity.fullArity
      (ExtensionLookupIdentity.fullCoefficient (K := K)) ExtensionLookupIdentity.fullIndices
      (fun factor cell => if factor = .hash then
        ExtensionLookupIdentity.hashTable y (fun i => LookupSourceFlattening.flatten shape (sources i)) cell + r else
        ExtensionLookupIdentity.factors eqPoint y (fun i => LookupSourceFlattening.flatten shape (sources i))
          (fun cell => PaddedExtension.decode basis (helpers cell)) (2 ^ (c + row)) factor cell) (some (claim, memory)) ∨
      (∃ i, sourceClaims i ≠
        (ExtensionLookupTerminal.sourceQuery basis shape (ScalarSumcheckQuery.point claim.query)).query.fold (sources i)) ∨
      helperClaim ≠ (ExtensionQuery.coefficientsQuery basis (ScalarSumcheckQuery.point claim.query)).query.fold helpers := by
  have alternatives := MixedWidthExtensionLookupTerminal.checked_truthful_or_wrong basis shape eqPoint
    (ScalarSumcheckQuery.point claim.query) r y (2 ^ (c + row)) le_rfl sources helpers sourceClaims helperClaim sourceValues
    helperValue (claim.expected 0) sourceDecoded helperDecoded checked
  exact alternatives.imp_left ((full_truthful_iff basis shape eqPoint r y sources helpers claim memory).mpr)

end
end FormalProof4FHE.HasteBoots.MixedWidthLookupScalarSubclaim
