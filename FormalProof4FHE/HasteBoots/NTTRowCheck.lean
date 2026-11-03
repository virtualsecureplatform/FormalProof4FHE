module

public import FormalProof4FHE.HasteBoots.PackedEqualityCube
public import FormalProof4FHE.HasteBoots.NativeEqualityTable

@[expose] public section

/-!
# Tensor-row detection in the canonical NTT verifier

The native verifier folds polynomial blocks by Boolean-MLE tensor weights and
checks the transform of every proposed coefficient row. A fixed false linear
transform relation survives k independent row points with probability at most
(r/card(F))^k, where r is the number of polynomial-block variables. Repeated
points and zero row variables are included. Proposed rows may depend on all
sampled points; passing local checks then yields the row-miss event or a wrong
proposed row that later independent compression/openings must detect.

Polynomial evaluation gives a concrete linear transform. The native NTT root,
bit-reversed output, optimized transform and Rust refinement remain to be linked.
-/

open scoped BigOperators

namespace FormalProof4FHE.HasteBoots.NTTRowCheck

noncomputable section

variable {F Position : Type} [Field F] {r k : ℕ}

/-- Coefficients are in increasing monomial order; nodes choose output order. -/
def evaluation {size : ℕ} (nodes : Fin size → F) : (Fin size → F) →ₗ[F] (Fin size → F) where
  toFun coefficients := fun index => ∑ power, coefficients power * nodes index ^ power.val
  map_add' first second := by funext index; simp [add_mul, Finset.sum_add_distrib]
  map_smul' scalar coefficients := by funext index; simp [Finset.mul_sum, mul_assoc]

/-- The row index is high in the flat source address. Within each polynomial,
coefficient/lane coordinates are retained without permutation. -/
def fold (point : Fin r → F) (table : MatrixFold.Cube r → Position → F) : Position → F :=
  ∑ row, PackedEqualityCube.weight point row • table row

theorem fold_sub (point : Fin r → F) (first second : MatrixFold.Cube r → Position → F) :
    fold point (fun row => first row - second row) = fold point first - fold point second := by
  simp only [fold, smul_sub, Finset.sum_sub_distrib]

/-- Linear transforms commute with the native weighted sum of polynomial rows. -/
theorem map_fold (transform : (Position → F) →ₗ[F] (Position → F))
    (point : Fin r → F) (table : MatrixFold.Cube r → Position → F) :
    transform (fold point table) = fold point (fun row => transform (table row)) := by
  simp only [fold, map_sum, map_smul]

/-- Tensor weights agree with the already-checked native two-block table. -/
theorem fold_native (point : Fin r → F) (table : MatrixFold.Cube r → Position → F) :
    fold point table = ∑ index : Fin (2 ^ r), NativeEqualityTable.table r point index •
      table ((FlatMatrixFold.index r).symm index) := by
  rw [← (FlatMatrixFold.index r).sum_comp]
  apply Finset.sum_congr rfl
  intro row _
  rw [NativeEqualityTable.table_index, Equiv.symm_apply_apply]

/-- All polynomial blocks must use the same trusted transform and row order. -/
def Relation (transform : (Position → F) →ₗ[F] (Position → F))
    (coefficients evaluations : MatrixFold.Cube r → Position → F) : Prop :=
  ∀ row, transform (coefficients row) = evaluations row

def RowsPass (transform : (Position → F) →ₗ[F] (Position → F))
    (coefficients evaluations : MatrixFold.Cube r → Position → F) (points : Fin k → Fin r → F) : Prop :=
  ∀ repetition, transform (fold (points repetition) coefficients) = fold (points repetition) evaluations

theorem honest_rows (transform : (Position → F) →ₗ[F] (Position → F))
    (coefficients evaluations : MatrixFold.Cube r → Position → F)
    (valid : Relation transform coefficients evaluations) (points : Fin k → Fin r → F) :
    RowsPass transform coefficients evaluations points := by
  intro repetition
  rw [map_fold]
  exact congrArg (fold (points repetition)) (funext valid)

/-- A false source relation is fixed before all row points. No assumption on
rank, invertibility or independence of source rows is used. -/
theorem miss_bound [Fintype F] [DecidableEq F] [SampleableType F]
    [SampleableType (Fin r → F)] [SampleableType (Fin k → Fin r → F)]
    (transform : (Position → F) →ₗ[F] (Position → F))
    (coefficients evaluations : MatrixFold.Cube r → Position → F)
    (falseRelation : ¬Relation transform coefficients evaluations) :
    Pr{let points ← $ᵗ (Fin k → Fin r → F)}[RowsPass transform coefficients evaluations points] ≤
      (((r : ENNReal) / Fintype.card F) ^ k) := by
  classical
  obtain ⟨row, different⟩ := not_forall.mp falseRelation
  obtain ⟨position, different⟩ := Function.ne_iff.mp different
  let residual := fun row => transform (coefficients row) - evaluations row
  let values := fun cell : PackedZeroEquality.Cell r => residual ((PackedEqualityCube.bits r).symm cell) position
  have nonzero : ∃ cell, values cell ≠ 0 := by
    refine ⟨PackedEqualityCube.bits r row, ?_⟩
    simpa only [values, residual, Equiv.symm_apply_apply, Pi.sub_apply, sub_ne_zero] using different
  apply le_trans (prEvent_mono _ _ _ ?_) (PackedZeroEquality.points_bound values nonzero)
  intro points passed repetition
  have zero : fold (points repetition) residual = 0 := by
    rw [fold_sub, ← map_fold, passed repetition, sub_self]
  have scalar := congrFun zero position
  have weighted : (∑ cell, PackedEqualityCube.weight (points repetition) cell * residual cell position) = 0 := by
    simpa only [fold, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using scalar
  simpa only [values, PackedEqualityCube.weighted_sum] using weighted

variable [Fintype Position]

/-- Literal typed local transform checking of all k proposed polynomial pairs. -/
def check [DecidableEq F] (transform : (Position → F) →ₗ[F] (Position → F))
    (coefficients evaluations : Fin k → Position → F) : Bool :=
  (List.ofFn fun repetition => decide (transform (coefficients repetition) = evaluations repetition)).all id

theorem check_iff [DecidableEq F] (transform : (Position → F) →ₗ[F] (Position → F))
    (coefficients evaluations : Fin k → Position → F) :
    check transform coefficients evaluations = true ↔
      ∀ repetition, transform (coefficients repetition) = evaluations repetition := by
  simp [check, List.all_eq_true, List.mem_ofFn]

/-- Proposals adaptive to the row points either expose a wrong original
coefficient/evaluation fold or imply that every row point missed the relation. -/
theorem checked_miss_or_wrong [DecidableEq F] (transform : (Position → F) →ₗ[F] (Position → F))
    (coefficients evaluations : MatrixFold.Cube r → Position → F) (points : Fin k → Fin r → F)
    (proposedCoefficients proposedEvaluations : Fin k → Position → F)
    (checked : check transform proposedCoefficients proposedEvaluations = true) :
    RowsPass transform coefficients evaluations points ∨
      ∃ repetition, proposedCoefficients repetition ≠ fold (points repetition) coefficients ∨
        proposedEvaluations repetition ≠ fold (points repetition) evaluations := by
  classical
  by_cases wrong : ∃ repetition, proposedCoefficients repetition ≠ fold (points repetition) coefficients ∨
      proposedEvaluations repetition ≠ fold (points repetition) evaluations
  · exact Or.inr wrong
  left
  intro repetition
  have correct := not_or.mp (not_exists.mp wrong repetition)
  have localCheck := (check_iff transform proposedCoefficients proposedEvaluations).mp checked repetition
  rw [Classical.not_not.mp correct.1, Classical.not_not.mp correct.2] at localCheck
  exact localCheck

end

end FormalProof4FHE.HasteBoots.NTTRowCheck
