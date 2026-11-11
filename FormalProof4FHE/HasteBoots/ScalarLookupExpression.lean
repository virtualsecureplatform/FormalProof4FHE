module
public import FormalProof4FHE.HasteBoots.ScalarSourcePolynomial
public import FormalProof4FHE.HasteBoots.LookupPairArithmetic
public import FormalProof4FHE.HasteBoots.MixedWidthExtensionLookupTerminal
@[expose] public section

/-! The exact helper-sum and reciprocal identity grammars used by the shared
native lookup scalar batch. Every honest polynomial is constructed from the
original factor tables; degrees are one, three, and four respectively. -/
namespace FormalProof4FHE.HasteBoots.ScalarLookupExpression
open scoped BigOperators
open MatrixFold (Cube)
open ExtensionLookupIdentity (Factor)
noncomputable section
variable {F K : Type} [Field F] [Field K] [Algebra F K] {n columns : ℕ}

def sumArity (_ : Unit) : ℕ := 1
def sumCoefficient (_ : Unit) : K := 1
def sumIndices (term : Unit) (_ : Fin (sumArity term)) : Factor := .helper

theorem sum_expression (values : Factor → K) :
    PackedSumcheckRound.expression sumArity sumCoefficient sumIndices values = values .helper := by
  unfold PackedSumcheckRound.expression
  rw [Fintype.sum_subsingleton _ ()]
  change (1 : K) * (∏ _j : Fin 1, values .helper) = _
  rw [Fin.prod_univ_one,one_mul]

theorem sum_initial (helpers : Cube n → K) :
    ScalarSourcePolynomial.truth sumArity sumCoefficient sumIndices n [] (fun _ => helpers) = ∑ cell, helpers cell := by
  simp only [ScalarSourcePolynomial.truth,sum_expression]

theorem sum_terminal (helpers : Cube n → K) (point : Fin n → K) :
    ScalarSourcePolynomial.truth sumArity sumCoefficient sumIndices n (List.ofFn point) (fun _ => helpers) =
      ExtensionQuery.evaluate n point helpers := by
  rw [ScalarSourcePolynomial.terminal,sum_expression]

theorem sum_degree (helpers : Cube n → K) (point : List K) :
    (ScalarSourcePolynomial.honest sumArity sumCoefficient sumIndices n point (fun _ => helpers)).natDegree ≤ 1 :=
  ScalarSourcePolynomial.degree _ _ _ 1 (fun _ => Nat.le_refl 1) n point _

/-- Partial active prefixes keep the public mask as a separate MLE factor. -/
theorem partial_initial (eqPoint : Fin n → K) (r y : K) (sources : Fin columns → Cube n → F)
    (helpers : Cube n → K) (count : ℕ) :
    ScalarSourcePolynomial.truth ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient r)
      ExtensionLookupIdentity.partialIndices n [] (ExtensionLookupIdentity.factors eqPoint y sources helpers count) =
      ∑ cell, PackedEqualityCube.weight eqPoint cell * ReciprocalMask.residual r
        (ExtensionLookupIdentity.hashTable y sources cell) (helpers cell)
        (decide ((FlatMatrixFold.index n cell).val < count)) :=
  by simpa only [ScalarSourcePolynomial.truth] using ExtensionLookupIdentity.partial_sum eqPoint r y sources helpers count

/-- The full identity shifts the compressed source by r. This affine factor
is derived locally; it does not introduce a new committed source. -/
theorem full_initial (eqPoint : Fin n → K) (r y : K) (sources : Fin columns → Cube n → F)
    (helpers : Cube n → K) :
    ScalarSourcePolynomial.truth ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient
      ExtensionLookupIdentity.fullIndices n [] (LookupPairArithmetic.fullTables eqPoint r y sources helpers) =
      ∑ cell, PackedEqualityCube.weight eqPoint cell * ReciprocalMask.residual r
        (ExtensionLookupIdentity.hashTable y sources cell) (helpers cell)
        (decide ((FlatMatrixFold.index n cell).val < 2^n)) := by
  simpa only [ScalarSourcePolynomial.truth] using (LookupPairArithmetic.full_sum_eq_partial eqPoint r y sources helpers).trans
    (ExtensionLookupIdentity.partial_sum eqPoint r y sources helpers (2^n))

theorem partial_terminal (eqPoint point : Fin n → K) (r y : K) (sources : Fin columns → Cube n → F)
    (helpers : Cube n → K) (count : ℕ) (enough : count ≤ 2^n) :
    ScalarSourcePolynomial.truth ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient r)
      ExtensionLookupIdentity.partialIndices n (List.ofFn point) (ExtensionLookupIdentity.factors eqPoint y sources helpers count) =
      ExtensionLookupIdentity.terminal eqPoint point r
        (∑ column, y^column.val * ExtensionQuery.evaluate n point (fun cell => algebraMap F K (sources column cell)))
        (ExtensionQuery.evaluate n point helpers) count enough := by
  rw [ScalarSourcePolynomial.terminal,ExtensionLookupIdentity.partial_terminal,ExtensionLookupIdentity.evaluate_hash]

theorem full_terminal (eqPoint point : Fin n → K) (r y : K) (sources : Fin columns → Cube n → F)
    (helpers : Cube n → K) :
    ScalarSourcePolynomial.truth ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient
      ExtensionLookupIdentity.fullIndices n (List.ofFn point) (LookupPairArithmetic.fullTables eqPoint r y sources helpers) =
      ExtensionLookupIdentity.terminal eqPoint point r
        (∑ column, y^column.val * ExtensionQuery.evaluate n point (fun cell => algebraMap F K (sources column cell)))
        (ExtensionQuery.evaluate n point helpers) (2^n) le_rfl := by
  rw [ScalarSourcePolynomial.terminal]
  exact (ExtensionLookupIdentity.full_terminal eqPoint point r y sources helpers).trans
    (by rw [ExtensionLookupIdentity.evaluate_hash])

theorem partial_degree (eqPoint : Fin n → K) (r y : K) (sources : Fin columns → Cube n → F)
    (helpers : Cube n → K) (count : ℕ) (point : List K) :
    (ScalarSourcePolynomial.honest ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient r)
      ExtensionLookupIdentity.partialIndices n point (ExtensionLookupIdentity.factors eqPoint y sources helpers count)).natDegree ≤ 4 :=
  ScalarSourcePolynomial.degree _ _ _ 4 ExtensionLookupIdentity.partial_degree n point _

theorem full_degree (eqPoint : Fin n → K) (r y : K) (sources : Fin columns → Cube n → F)
    (helpers : Cube n → K) (point : List K) :
    (ScalarSourcePolynomial.honest ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient
      ExtensionLookupIdentity.fullIndices n point (LookupPairArithmetic.fullTables eqPoint r y sources helpers)).natDegree ≤ 3 :=
  ScalarSourcePolynomial.degree _ _ _ 3 ExtensionLookupIdentity.full_degree n point _

/-- Source lanes flatten into the full point; helper lanes decode at each
full-point row. Source and helper padding widths are independent. -/
theorem packed_partial_terminal {d sourcePadding helperPadding c row : ℕ}
    (basis : Module.Basis (Fin d) F K) (shape : d+sourcePadding = 2^c)
    (eqPoint point : Fin (c+row) → K) (r y : K)
    (sources : Fin columns → Cube row → Fin (d+sourcePadding) → F)
    (helpers : Cube (c+row) → Fin (d+helperPadding) → F) (count : ℕ) (enough : count ≤ 2^(c+row)) :
    ScalarSourcePolynomial.truth ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient r)
      ExtensionLookupIdentity.partialIndices (c+row) (List.ofFn point)
      (ExtensionLookupIdentity.factors eqPoint y (fun column => LookupSourceFlattening.flatten shape (sources column))
        (fun cell => PaddedExtension.decode basis (helpers cell)) count) =
      ExtensionLookupIdentity.terminal eqPoint point r
        (∑ column, y^column.val * ExtensionLookupTerminal.sourceTruth shape point (sources column))
        (ExtensionQuery.evaluate (c+row) point (fun cell => PaddedExtension.decode basis (helpers cell))) count enough := by
  simpa only [← LookupSourceFlattening.sourceTruth_eq_evaluate shape point] using
    partial_terminal eqPoint point r y (fun column => LookupSourceFlattening.flatten shape (sources column))
      (fun cell => PaddedExtension.decode basis (helpers cell)) count enough

theorem packed_full_terminal {d sourcePadding helperPadding c row : ℕ}
    (basis : Module.Basis (Fin d) F K) (shape : d+sourcePadding = 2^c)
    (eqPoint point : Fin (c+row) → K) (r y : K)
    (sources : Fin columns → Cube row → Fin (d+sourcePadding) → F)
    (helpers : Cube (c+row) → Fin (d+helperPadding) → F) :
    ScalarSourcePolynomial.truth ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient
      ExtensionLookupIdentity.fullIndices (c+row) (List.ofFn point)
      (LookupPairArithmetic.fullTables eqPoint r y (fun column => LookupSourceFlattening.flatten shape (sources column))
        (fun cell => PaddedExtension.decode basis (helpers cell))) =
      ExtensionLookupIdentity.terminal eqPoint point r
        (∑ column, y^column.val * ExtensionLookupTerminal.sourceTruth shape point (sources column))
        (ExtensionQuery.evaluate (c+row) point (fun cell => PaddedExtension.decode basis (helpers cell))) (2^(c+row)) le_rfl := by
  simpa only [← LookupSourceFlattening.sourceTruth_eq_evaluate shape point] using
    full_terminal eqPoint point r y (fun column => LookupSourceFlattening.flatten shape (sources column))
      (fun cell => PaddedExtension.decode basis (helpers cell))

/-- Passing terminal decoding/checking yields the actual honest partial
source expression or a wrong original source/helper opening, at their own
independent widths and the same original point. -/
theorem partial_checked_or_wrong {d sourcePadding helperPadding c row : ℕ}
    (basis : Module.Basis (Fin d) F K) (shape : d+sourcePadding = 2^c)
    (eqPoint point : Fin (c+row) → K) (r y : K) (count : ℕ) (enough : count ≤ 2^(c+row))
    (sources : Fin columns → Cube row → Fin (d+sourcePadding) → F)
    (helpers : Cube (c+row) → Fin (d+helperPadding) → F)
    (sourceClaims : Fin columns → Fin (d+sourcePadding) → F) (helperClaim : Fin (d+helperPadding) → F)
    (sourceValues : Fin columns → K) (helperValue expected : K)
    (sourceDecoded : ∀ i, PaddedExtension.element basis ((ExtensionLookupTerminal.sourceQuery basis shape point).finish (sourceClaims i)) = some (sourceValues i))
    (helperDecoded : PaddedExtension.element basis ((ExtensionQuery.coefficientsQuery basis point).finish helperClaim) = some helperValue)
    (checked : ExtensionLookupIdentity.terminal eqPoint point r (∑ i, y^i.val * sourceValues i) helperValue count enough = expected) :
    expected = ScalarSourcePolynomial.truth ExtensionLookupIdentity.partialArity (ExtensionLookupIdentity.partialCoefficient r)
      ExtensionLookupIdentity.partialIndices (c+row) (List.ofFn point)
      (ExtensionLookupIdentity.factors eqPoint y (fun column => LookupSourceFlattening.flatten shape (sources column))
        (fun cell => PaddedExtension.decode basis (helpers cell)) count) ∨
      (∃ i, sourceClaims i ≠ (ExtensionLookupTerminal.sourceQuery basis shape point).query.fold (sources i)) ∨
      helperClaim ≠ (ExtensionQuery.coefficientsQuery basis point).query.fold helpers := by
  rw [packed_partial_terminal basis shape eqPoint point r y sources helpers count enough]
  exact MixedWidthExtensionLookupTerminal.checked_truthful_or_wrong basis shape eqPoint point r y count enough
    sources helpers sourceClaims helperClaim sourceValues helperValue expected sourceDecoded helperDecoded checked

theorem full_checked_or_wrong {d sourcePadding helperPadding c row : ℕ}
    (basis : Module.Basis (Fin d) F K) (shape : d+sourcePadding = 2^c)
    (eqPoint point : Fin (c+row) → K) (r y : K)
    (sources : Fin columns → Cube row → Fin (d+sourcePadding) → F)
    (helpers : Cube (c+row) → Fin (d+helperPadding) → F)
    (sourceClaims : Fin columns → Fin (d+sourcePadding) → F) (helperClaim : Fin (d+helperPadding) → F)
    (sourceValues : Fin columns → K) (helperValue expected : K)
    (sourceDecoded : ∀ i, PaddedExtension.element basis ((ExtensionLookupTerminal.sourceQuery basis shape point).finish (sourceClaims i)) = some (sourceValues i))
    (helperDecoded : PaddedExtension.element basis ((ExtensionQuery.coefficientsQuery basis point).finish helperClaim) = some helperValue)
    (checked : ExtensionLookupIdentity.terminal eqPoint point r (∑ i, y^i.val * sourceValues i) helperValue (2^(c+row)) le_rfl = expected) :
    expected = ScalarSourcePolynomial.truth ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient
      ExtensionLookupIdentity.fullIndices (c+row) (List.ofFn point)
      (LookupPairArithmetic.fullTables eqPoint r y (fun column => LookupSourceFlattening.flatten shape (sources column))
        (fun cell => PaddedExtension.decode basis (helpers cell))) ∨
      (∃ i, sourceClaims i ≠ (ExtensionLookupTerminal.sourceQuery basis shape point).query.fold (sources i)) ∨
      helperClaim ≠ (ExtensionQuery.coefficientsQuery basis point).query.fold helpers := by
  rw [packed_full_terminal basis shape eqPoint point r y sources helpers]
  exact MixedWidthExtensionLookupTerminal.checked_truthful_or_wrong basis shape eqPoint point r y (2^(c+row)) le_rfl
    sources helpers sourceClaims helperClaim sourceValues helperValue expected sourceDecoded helperDecoded checked

/-- The paired sum guard uses the same decoded helper, at the helper's row
dimension, with no source lane coordinates added to its point. -/
theorem sum_checked_or_wrong {d padding : ℕ} (basis : Module.Basis (Fin d) F K) (point : Fin n → K)
    (helpers : Cube n → Fin (d+padding) → F) (claim : Fin (d+padding) → F) (value expected : K)
    (decoded : PaddedExtension.element basis ((ExtensionQuery.coefficientsQuery basis point).finish claim) = some value)
    (matched : expected = value) :
    expected = ScalarSourcePolynomial.truth sumArity sumCoefficient sumIndices n (List.ofFn point)
        (fun _ cell => PaddedExtension.decode basis (helpers cell)) ∨
      claim ≠ (ExtensionQuery.coefficientsQuery basis point).query.fold helpers := by
  rw [sum_terminal,matched]
  by_cases truthful : value = ExtensionQuery.evaluate n point (fun cell => PaddedExtension.decode basis (helpers cell))
  · exact Or.inl truthful
  · exact Or.inr (ExtensionQuery.coefficients_false_claim basis point helpers value claim decoded truthful)

end
end FormalProof4FHE.HasteBoots.ScalarLookupExpression
