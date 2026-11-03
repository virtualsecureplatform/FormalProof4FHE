module

public import FormalProof4FHE.HasteBoots.ScalarSumcheckOracle

@[expose] public section

/-!
# Scalar sumcheck subclaims for the native lookup terminals

The helper-sum, partial identity and full identity MLE terminal events are
identified with the literal native terminal formulas, using the original
packed-source flattening. Local terminal checking exposes the same arithmetic
MLE event or a wrong original base opening. Complete operational lookup stage
and grouped-PCS/shared-work composition remain open.
-/

open scoped BigOperators Classical
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.LookupScalarSubclaim

noncomputable section

variable {F K Memory : Type} [Field F] [Field K] [Algebra F K] {n d padding c row count : ℕ}

def sumArity (_ : Unit) : ℕ := 1
def sumCoefficient (_ : Unit) : K := 1
def sumIndices (_ : Unit) (_ : Fin 1) : Unit := ()

theorem sum_expression (values : Unit → K) :
    PackedSumcheckRound.expression sumArity (sumCoefficient (K := K)) sumIndices values = values () := by
  simp [PackedSumcheckRound.expression, sumArity, sumCoefficient, sumIndices]
  change values () ^ (Finset.univ : Finset (Fin 1)).card = values ()
  simp

theorem sum_truthful_iff (helpers : MatrixFold.Cube n → K) (claim : Subclaim K 1 n) (memory : Memory) :
    ScalarSumcheckOracle.MLETruthful sumArity (sumCoefficient (K := K)) sumIndices (fun _ => helpers) (some (claim, memory)) ↔
      claim.expected 0 = ExtensionQuery.evaluate n (ScalarSumcheckQuery.point claim.query) helpers := by
  simp only [ScalarSumcheckOracle.MLETruthful, sum_expression]

theorem partial_truthful_iff (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K) (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
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
  rw [← LookupSourceFlattening.terminal_eq_identity basis shape eqPoint _ r y active enough sources helpers]

theorem full_truthful_iff (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
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
  rw [← LookupSourceFlattening.terminal_eq_full_identity basis shape eqPoint _ r y sources helpers]

/-- A successful local partial-lookup terminal has the actual sumcheck MLE
arithmetic event or a false original source/helper base opening. -/
theorem checked_partial_or_wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K) (active : ℕ) (enough : active ≤ 2 ^ (c + row))
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (claim : Subclaim K 1 (c + row)) (memory : Memory)
    (sourceClaims : Fin count → Fin (d + padding) → F) (helperClaim : Fin (d + padding) → F)
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
  have alternatives := ExtensionLookupTerminal.checked_truthful_or_wrong basis shape eqPoint
    (ScalarSumcheckQuery.point claim.query) r y active enough sources helpers sourceClaims helperClaim sourceValues
    helperValue (claim.expected 0) sourceDecoded helperDecoded checked
  exact alternatives.imp_left ((partial_truthful_iff basis shape eqPoint r y active enough sources helpers claim memory).mpr)

/-- The full-table branch uses the degree-three event, with the same original
source/helper opening alternatives and local decoding checks. -/
theorem checked_full_or_wrong (basis : Module.Basis (Fin d) F K) (shape : d + padding = 2 ^ c)
    (eqPoint : Fin (c + row) → K) (r y : K)
    (sources : Fin count → MatrixFold.Cube row → Fin (d + padding) → F)
    (helpers : MatrixFold.Cube (c + row) → Fin (d + padding) → F)
    (claim : Subclaim K 1 (c + row)) (memory : Memory)
    (sourceClaims : Fin count → Fin (d + padding) → F) (helperClaim : Fin (d + padding) → F)
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
  have alternatives := ExtensionLookupTerminal.checked_truthful_or_wrong basis shape eqPoint
    (ScalarSumcheckQuery.point claim.query) r y (2 ^ (c + row)) le_rfl sources helpers sourceClaims helperClaim sourceValues
    helperValue (claim.expected 0) sourceDecoded helperDecoded checked
  exact alternatives.imp_left ((full_truthful_iff basis shape eqPoint r y sources helpers claim memory).mpr)

end

end FormalProof4FHE.HasteBoots.LookupScalarSubclaim
