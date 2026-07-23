/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDiagonalPairCollisionNormalForm
import FormalProof4FHE.TFHE.NativePowerOfTwoLocalRing
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Binary Rectangular Rank Form of the Native Paired Diagonal

At exact gadget capacity with an even base, each native difference ciphertext produces an
independent uniform square binary row matrix after coefficient parity evaluation.  Two independent
differences therefore produce a uniform matrix with twice as many rows as columns after horizontal
concatenation and transposition.  Its rank-failure probability has the finite-field bound

`2 / 2^(m + 1)`,

where `m` is the native TGSW row count.  This is the first quantitative entropy-slack statement
for the paired diagonal and contrasts with the constant failure probability of one square block.

The binary matrix is also identified entrywise with the parity reduction of the concrete paired
row matrix.  The local-ring lift is abstract over any parity map that reflects units.  The
nilpotent-kernel theorems in `NativePowerOfTwoLocalRing` discharge this premise both at binary
coefficient modulus and for the production ring with modulus `2^k`, `k > 0`, and degree `2^d`.
-/

open Matrix OracleComp
open scoped ENNReal

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

variable {q degree ringRank : ℕ}

/-! ## Generic concatenated matrix equivalence -/

/-- Transpose of the horizontal concatenation of two square matrices. -/
def pairedTransposeMatrix {R : Type} {dimension : ℕ}
    (left right : Matrix (Fin dimension) (Fin dimension) R) :
    Matrix (Fin (dimension + dimension)) (Fin dimension) R :=
  fun combinedColumn row =>
    (finSumFinEquiv.symm combinedColumn).elim
      (fun column => left row column)
      (fun column => right row column)

/-- A pair of square matrices is equivalent to their transposed horizontal concatenation. -/
def pairedTransposeMatrixEquiv (R : Type) (dimension : ℕ) :
    (Matrix (Fin dimension) (Fin dimension) R ×
      Matrix (Fin dimension) (Fin dimension) R) ≃
        Matrix (Fin (dimension + dimension)) (Fin dimension) R where
  toFun matrices := pairedTransposeMatrix matrices.1 matrices.2
  invFun matrix :=
    (fun row column => matrix (finSumFinEquiv (Sum.inl column)) row,
      fun row column => matrix (finSumFinEquiv (Sum.inr column)) row)
  left_inv := by
    intro matrices
    apply Prod.ext
    · ext row column
      change (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl column))).elim
        (fun column => matrices.1 row column)
        (fun column => matrices.2 row column) = matrices.1 row column
      rw [Equiv.symm_apply_apply]
      rfl
    · ext row column
      change (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr column))).elim
        (fun column => matrices.1 row column)
        (fun column => matrices.2 row column) = matrices.2 row column
      rw [Equiv.symm_apply_apply]
      rfl
  right_inv := by
    intro matrix
    ext combinedColumn row
    obtain ⟨column, rfl⟩ := finSumFinEquiv.surjective combinedColumn
    cases column with
    | inl column =>
        change (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl column))).elim _ _ = _
        rw [Equiv.symm_apply_apply]
        rfl
    | inr column =>
        change (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr column))).elim _ _ = _
        rw [Equiv.symm_apply_apply]
        rfl

/-- Uniform independent square matrices concatenate to one uniform rectangular matrix. -/
theorem pairedTransposeMatrix_uniform_evalDist
    {R : Type} [Fintype R] [SampleableType R] (dimension : ℕ) :
    evalDist
        ((fun matrices :
            Matrix (Fin dimension) (Fin dimension) R ×
              Matrix (Fin dimension) (Fin dimension) R =>
            pairedTransposeMatrix matrices.1 matrices.2) <$>
          ($ᵗ (Matrix (Fin dimension) (Fin dimension) R ×
            Matrix (Fin dimension) (Fin dimension) R))) =
      evalDist
        ($ᵗ Matrix (Fin (dimension + dimension)) (Fin dimension) R) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin dimension) (Fin dimension) R ×
      Matrix (Fin dimension) (Fin dimension) R)
    (β := Matrix (Fin (dimension + dimension)) (Fin dimension) R)
    (pairedTransposeMatrixEquiv R dimension)
    (pairedTransposeMatrixEquiv R dimension).bijective

/-! ## A generic local-homomorphism lift -/

/-- If the transpose of a rectangular matrix becomes injective after a surjective ring map that
reflects units, then the original row operator is surjective.  The proof lifts a field-valued left
inverse entrywise.  Its product with the original transpose maps to the identity, so the product
has unit determinant over the source ring.  Transposing an inverse of that product gives a right
inverse for the original rectangular matrix. -/
theorem mulVec_surjective_of_map_transpose_mulVec_injective
    {R S rowIndex columnIndex : Type}
    [CommRing R] [Field S]
    [Fintype rowIndex] [DecidableEq rowIndex]
    [Fintype columnIndex] [DecidableEq columnIndex]
    (hom : R →+* S) [IsLocalHom hom]
    (hom_surjective : Function.Surjective hom)
    (matrix : Matrix rowIndex columnIndex R)
    (mappedTranspose_injective :
      Function.Injective ((matrix.map hom).transpose.mulVec)) :
    Function.Surjective matrix.mulVec := by
  classical
  let mappedTranspose := (matrix.map hom).transpose
  have mappedTranspose_injective' :
      Function.Injective mappedTranspose.mulVecLin :=
    mappedTranspose_injective
  obtain ⟨leftInverse, leftInverse_comp⟩ :=
    mappedTranspose.mulVecLin.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr mappedTranspose_injective')
  let leftMatrix : Matrix rowIndex columnIndex S :=
    LinearMap.toMatrix' leftInverse
  have leftMatrix_mul : leftMatrix * mappedTranspose = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    exact leftInverse_comp
  let liftedLeftMatrix : Matrix rowIndex columnIndex R :=
    fun row column ↦ Function.surjInv hom_surjective (leftMatrix row column)
  have liftedLeftMatrix_map : liftedLeftMatrix.map hom = leftMatrix := by
    ext row column
    exact Function.surjInv_eq hom_surjective _
  let squareProduct : Matrix rowIndex rowIndex R :=
    liftedLeftMatrix * matrix.transpose
  have squareProduct_map : squareProduct.map hom = 1 := by
    change (liftedLeftMatrix * matrix.transpose).map hom = 1
    rw [Matrix.map_mul, liftedLeftMatrix_map]
    calc
      leftMatrix * matrix.transpose.map hom =
          leftMatrix * (matrix.map hom).transpose := by
            congr 1
      _ = 1 := by simpa [mappedTranspose] using leftMatrix_mul
  have mappedDeterminant_unit : IsUnit (hom squareProduct.det) := by
    have hmappedDeterminant : hom squareProduct.det = 1 := by
      calc
        hom squareProduct.det = (squareProduct.map hom).det :=
          RingHom.map_det hom squareProduct
        _ = 1 := by rw [squareProduct_map, Matrix.det_one]
    rw [hmappedDeterminant]
    exact isUnit_one
  have determinant_unit : IsUnit squareProduct.det :=
    IsUnit.of_map hom squareProduct.det mappedDeterminant_unit
  have squareProduct_unit : IsUnit squareProduct :=
    (Matrix.isUnit_iff_isUnit_det squareProduct).2 determinant_unit
  have transposeProduct_unit : IsUnit squareProduct.transpose :=
    (Matrix.isUnit_transpose (A := squareProduct)).2 squareProduct_unit
  obtain ⟨inverse, transposeProduct_mul_inverse⟩ :=
    isUnit_iff_exists_inv.mp transposeProduct_unit
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  refine ⟨liftedLeftMatrix.transpose * inverse, ?_⟩
  calc
    matrix * (liftedLeftMatrix.transpose * inverse) =
        (matrix * liftedLeftMatrix.transpose) * inverse := by
          rw [Matrix.mul_assoc]
    _ = squareProduct.transpose * inverse := by
      change (matrix * liftedLeftMatrix.transpose) * inverse =
        (liftedLeftMatrix * matrix.transpose).transpose * inverse
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = 1 := transposeProduct_mul_inverse

/-- Over a field, attaining the full column rank is equivalent to injectivity of the matrix-vector
map.  This small bridge keeps the probabilistic rank statement separate from the local lift. -/
theorem mulVec_injective_of_rank_eq_card_width
    {F rowIndex columnIndex : Type}
    [Field F] [Fintype rowIndex] [Fintype columnIndex]
    (matrix : Matrix rowIndex columnIndex F)
    (fullRank : matrix.rank = Fintype.card columnIndex) :
    Function.Injective matrix.mulVec := by
  rw [Matrix.mulVec_injective_iff,
    linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card columnIndex =
    Module.finrank F (Submodule.span F (Set.range matrix.col))
  rw [← matrix.rank_eq_finrank_span_cols]
  exact fullRank.symm

/-! ## Concrete paired native matrix -/

/-- Matrix of the paired row operator before transposition.  Its first block is the left row
matrix and its second block is the negated right row matrix. -/
noncomputable def pairedRowMatrix {R : Type} [CommRing R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    Matrix (Fin (TGSW.rowCount dimension levels))
      (Fin (TGSW.rowCount dimension levels + TGSW.rowCount dimension levels)) R :=
  fun row combinedColumn =>
    (finSumFinEquiv.symm combinedColumn).elim
      (fun column => rowMatrix candidate leftDigits row column)
      (fun column => -rowMatrix candidate rightDigits row column)

/-- Reindex a pair of row vectors as the column vector consumed by `pairedRowMatrix`. -/
def pairedRowInputEquiv (R : Type) (dimension : ℕ) :
    ((Fin dimension → R) × (Fin dimension → R)) ≃
      (Fin (dimension + dimension) → R) where
  toFun values combinedColumn :=
    (finSumFinEquiv.symm combinedColumn).elim values.1 values.2
  invFun combined :=
    (fun column ↦ combined (finSumFinEquiv (Sum.inl column)),
      fun column ↦ combined (finSumFinEquiv (Sum.inr column)))
  left_inv := by
    intro values
    apply Prod.ext <;> funext column
    · change (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl column))).elim
        values.1 values.2 = values.1 column
      rw [Equiv.symm_apply_apply]
      rfl
    · change (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr column))).elim
        values.1 values.2 = values.2 column
      rw [Equiv.symm_apply_apply]
      rfl
  right_inv := by
    intro combined
    funext combinedColumn
    obtain ⟨column, rfl⟩ := finSumFinEquiv.surjective combinedColumn
    cases column with
    | inl column =>
        change (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl column))).elim _ _ = _
        rw [Equiv.symm_apply_apply]
        rfl
    | inr column =>
        change (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr column))).elim _ _ = _
        rw [Equiv.symm_apply_apply]
        rfl

/-- The concrete concatenated matrix computes exactly the paired row-difference operator after
the canonical reindexing of its two input vectors. -/
theorem pairedRowMatrix_mulVec_pairedRowInput
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (values :
      (Fin (TGSW.rowCount dimension levels) → R) ×
        (Fin (TGSW.rowCount dimension levels) → R)) :
    pairedRowMatrix candidate leftDigits rightDigits *ᵥ
        pairedRowInputEquiv R (TGSW.rowCount dimension levels) values =
      pairedRowDifferenceOperator candidate leftDigits rightDigits values := by
  classical
  funext row
  change
    (Sum.elim
        (fun column ↦ rowMatrix candidate leftDigits row column)
        (fun column ↦ -rowMatrix candidate rightDigits row column) ∘
      finSumFinEquiv.symm) ⬝ᵥ
        (Sum.elim values.1 values.2 ∘ finSumFinEquiv.symm) =
      rowOperator candidate leftDigits values.1 row -
        rowOperator candidate rightDigits values.2 row
  rw [comp_equiv_dotProduct_comp_equiv]
  rw [sumElim_dotProduct_sumElim]
  simp only [dotProduct, neg_mul, Finset.sum_neg_distrib]
  have leftRow := congrFun
    (rowMatrix_mulVec candidate leftDigits values.1) row
  have rightRow := congrFun
    (rowMatrix_mulVec candidate rightDigits values.2) row
  change
    (∑ column, rowMatrix candidate leftDigits row column * values.1 column) =
      rowOperator candidate leftDigits values.1 row at leftRow
  change
    (∑ column, rowMatrix candidate rightDigits row column * values.2 column) =
      rowOperator candidate rightDigits values.2 row at rightRow
  rw [leftRow, rightRow]
  simp [sub_eq_add_neg]

/-- Surjectivity of the concatenated matrix-vector map is the row-level surjectivity needed by
the paired-collision normal form. -/
theorem pairedRowDifferenceOperator_surjective_of_pairedRowMatrix
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (matrix_surjective : Function.Surjective
      (pairedRowMatrix candidate leftDigits rightDigits).mulVec) :
    Function.Surjective
      (pairedRowDifferenceOperator candidate leftDigits rightDigits) := by
  intro target
  obtain ⟨combinedInput, combinedInput_spec⟩ := matrix_surjective target
  let pairedInput :=
    (pairedRowInputEquiv R (TGSW.rowCount dimension levels)).symm combinedInput
  refine ⟨pairedInput, ?_⟩
  rw [← pairedRowMatrix_mulVec_pairedRowInput]
  rw [show pairedRowInputEquiv R (TGSW.rowCount dimension levels) pairedInput =
      combinedInput by exact Equiv.apply_symm_apply _ _]
  exact combinedInput_spec

/-- Binary rectangular matrix extracted from two native differences. -/
def differencePairBinaryTransposeMatrix [NeZero q]
    (params : Gadget.Base.Parameters q)
    (differences :
      RingGSWCiphertext q (degree + 1) ringRank params.levels ×
        RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    Matrix
      (Fin (TGSW.rowCount ringRank params.levels +
        TGSW.rowCount ringRank params.levels))
      (Fin (TGSW.rowCount ringRank params.levels)) (ZMod 2) :=
  pairedTransposeMatrix
    (differenceBinaryRowMatrix params differences.1)
    (differenceBinaryRowMatrix params differences.2)

/-- Parity reduction of the concrete paired row matrix is the transpose of the explicit binary
rectangular matrix. -/
theorem rqParityEval_mapMatrix_pairedRowMatrix_difference [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    (pairedRowMatrix candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference)).map
        (rqParityEval heven (Nat.succ_pos degree)) =
      (differencePairBinaryTransposeMatrix params
        (leftDifference, rightDifference)).transpose := by
  classical
  ext row combinedColumn
  obtain ⟨column, rfl⟩ := finSumFinEquiv.surjective combinedColumn
  cases column with
  | inl column =>
      have hleft := congrArg (fun matrix => matrix row column)
        (rqParityEval_mapMatrix_rowMatrix_difference
          params heven candidate leftDifference)
      simpa [pairedRowMatrix, differencePairBinaryTransposeMatrix,
        pairedTransposeMatrix] using hleft
  | inr column =>
      have hright := congrArg (fun matrix => matrix row column)
        (rqParityEval_mapMatrix_rowMatrix_difference
          params heven candidate rightDifference)
      change rqParityEval heven (Nat.succ_pos degree)
          (rowMatrix candidate (differenceEntryDigits params rightDifference)
            row column) =
        differenceBinaryRowMatrix params rightDifference row column at hright
      simp only [pairedRowMatrix, Matrix.map_apply,
        differencePairBinaryTransposeMatrix, Matrix.transpose_apply,
        pairedTransposeMatrix]
      rw [Equiv.symm_apply_apply]
      simp only [Sum.elim_inr, map_neg]
      rw [hright]
      exact ZMod.neg_eq_self_mod_two _

/-- Conditional local-ring lift for one concrete native difference pair.  Full column rank of the
explicit binary rectangle makes the original concatenated row matrix surjective as soon as parity
evaluation reflects units. -/
theorem pairedRowMatrix_surjective_of_differencePairBinaryFullRank [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (fullRank :
      (differencePairBinaryTransposeMatrix params
        (leftDifference, rightDifference)).rank =
          TGSW.rowCount ringRank params.levels) :
    Function.Surjective
      (pairedRowMatrix candidate
        (differenceEntryDigits params leftDifference)
        (differenceEntryDigits params rightDifference)).mulVec := by
  letI : IsLocalHom (rqParityEval heven (Nat.succ_pos degree)) :=
    localParity
  apply mulVec_surjective_of_map_transpose_mulVec_injective
    (rqParityEval heven (Nat.succ_pos degree))
    (ZMod.ringHom_surjective
      (rqParityEval heven (Nat.succ_pos degree)))
  rw [rqParityEval_mapMatrix_pairedRowMatrix_difference]
  simp only [Matrix.transpose_transpose]
  apply mulVec_injective_of_rank_eq_card_width
  simpa using fullRank

/-- The matrix lift supplies exactly the row-level surjectivity premise used by the direct paired
collision proof. -/
theorem pairedRowDifferenceOperator_surjective_of_differencePairBinaryFullRank [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (fullRank :
      (differencePairBinaryTransposeMatrix params
        (leftDifference, rightDifference)).rank =
          TGSW.rowCount ringRank params.levels) :
    Function.Surjective
      (pairedRowDifferenceOperator candidate
        (differenceEntryDigits params leftDifference)
        (differenceEntryDigits params rightDifference)) := by
  apply pairedRowDifferenceOperator_surjective_of_pairedRowMatrix
  exact pairedRowMatrix_surjective_of_differencePairBinaryFullRank
    params heven candidate leftDifference rightDifference localParity fullRank

/-! ## Full-rank zero excess and explicit deficient-pair accounting -/

/-- A fixed pair's challenge-collision count is at most the number of all ordered challenge
pairs. -/
theorem pairedChallengeCollisionCount_le_card_sq
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    pairedChallengeCollisionCount candidate leftDigits rightDigits ≤
      (Fintype.card
        (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) : ℝ) ^ 2 := by
  unfold pairedChallengeCollisionCount
  calc
    (∑ leftChallenge : Matrix (Fin dimension)
          (Fin (TGSW.rowCount dimension levels)) R,
        ∑ rightChallenge : Matrix (Fin dimension)
            (Fin (TGSW.rowCount dimension levels)) R,
          if challengeOperator candidate leftDigits leftChallenge =
              challengeOperator candidate rightDigits rightChallenge then
            1
          else 0) ≤
        ∑ _leftChallenge : Matrix (Fin dimension)
            (Fin (TGSW.rowCount dimension levels)) R,
          ∑ _rightChallenge : Matrix (Fin dimension)
              (Fin (TGSW.rowCount dimension levels)) R, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro leftChallenge _
      apply Finset.sum_le_sum
      intro rightChallenge _
      split_ifs <;> norm_num
    _ = (Fintype.card
        (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) : ℝ) ^ 2 := by
      simp [pow_two]

/-- Consequently, one native difference pair's excess is at most the square of the complete
challenge-space cardinality.  This intentionally simple bound is used only to expose the
magnitude charged by rank-deficient pairs. -/
theorem differencePairChallengeCollisionExcess_le_challengeCard_sq [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    differencePairChallengeCollisionExcess params candidate
        leftDifference rightDifference ≤
      (Fintype.card (DiagonalChallenge q degree ringRank params.levels) : ℝ) ^ 2 := by
  have count_bound := pairedChallengeCollisionCount_le_card_sq candidate
    (differenceEntryDigits params leftDifference)
    (differenceEntryDigits params rightDifference)
  have challenge_card_nonneg :
      (0 : ℝ) ≤ Fintype.card (DiagonalChallenge q degree ringRank params.levels) := by
    positivity
  unfold differencePairChallengeCollisionExcess differencePairChallengeCollisionCount
  linarith

/-- Under the same explicit local-homomorphism premise, every full-rank binary difference pair
has exactly zero challenge-collision excess over the uniform baseline. -/
theorem differencePairChallengeCollisionExcess_eq_zero_of_binaryFullRank [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (fullRank :
      (differencePairBinaryTransposeMatrix params
        (leftDifference, rightDifference)).rank =
          TGSW.rowCount ringRank params.levels) :
    differencePairChallengeCollisionExcess params candidate
        leftDifference rightDifference = 0 := by
  apply differencePairChallengeCollisionExcess_eq_zero_of_surjective
  exact pairedRowDifferenceOperator_surjective_of_differencePairBinaryFullRank
    params heven candidate leftDifference rightDifference localParity fullRank

/-- Number of ordered native difference pairs whose explicit binary rectangle is not full column
rank. -/
def differencePairBinaryRankFailureCount [NeZero q]
    (params : Gadget.Base.Parameters q) : ℕ :=
  ∑ leftDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels,
    ((Finset.univ : Finset
        (RingGSWCiphertext q (degree + 1) ringRank params.levels)).filter
      (fun rightDifference ↦
        (differencePairBinaryTransposeMatrix params
          (leftDifference, rightDifference)).rank <
            TGSW.rowCount ringRank params.levels)).card

theorem differencePairBinaryRankFailureCount_eq_filter_card [NeZero q]
    (params : Gadget.Base.Parameters q) :
    differencePairBinaryRankFailureCount
        (degree := degree) (ringRank := ringRank) params =
      ((Finset.univ : Finset
          (RingGSWCiphertext q (degree + 1) ringRank params.levels ×
            RingGSWCiphertext q (degree + 1) ringRank params.levels)).filter
        (fun differences ↦
          (differencePairBinaryTransposeMatrix params differences).rank <
            TGSW.rowCount ringRank params.levels)).card := by
  classical
  let Difference :=
    RingGSWCiphertext q (degree + 1) ringRank params.levels
  let bad : Difference × Difference → Prop := fun differences ↦
    (differencePairBinaryTransposeMatrix params differences).rank <
      TGSW.rowCount ringRank params.levels
  change (∑ leftDifference : Difference,
      ((Finset.univ : Finset Difference).filter
        (fun rightDifference ↦ bad (leftDifference, rightDifference))).card) =
    ((Finset.univ : Finset (Difference × Difference)).filter bad).card
  calc
    (∑ leftDifference : Difference,
        ((Finset.univ : Finset Difference).filter
          (fun rightDifference ↦ bad (leftDifference, rightDifference))).card) =
      ∑ leftDifference : Difference,
        ∑ rightDifference : Difference,
          if bad (leftDifference, rightDifference) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro leftDifference _
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ differences : Difference × Difference,
        if bad differences then 1 else 0 := by
      exact (Fintype.sum_prod_type
        (f := fun differences : Difference × Difference ↦
          if bad differences then 1 else 0)).symm
    _ = ((Finset.univ : Finset (Difference × Difference)).filter bad).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- If parity reflects units, total paired collision excess is supported only on binary
rank-deficient pairs.  The explicit upper bound retains both their count and the worst-case
challenge-collision magnitude; it does not conflate failure probability with collision loss. -/
theorem totalDifferencePairChallengeCollisionExcess_le_rankFailureCount_mul
    [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree))) :
    totalDifferencePairChallengeCollisionExcess
        (degree := degree) (ringRank := ringRank) params candidate ≤
      (differencePairBinaryRankFailureCount
          (degree := degree) (ringRank := ringRank) params : ℝ) *
        (Fintype.card
          (DiagonalChallenge q degree ringRank params.levels) : ℝ) ^ 2 := by
  classical
  unfold totalDifferencePairChallengeCollisionExcess
  calc
    (∑ leftDifference :
        RingGSWCiphertext q (degree + 1) ringRank params.levels,
      ∑ rightDifference :
          RingGSWCiphertext q (degree + 1) ringRank params.levels,
        differencePairChallengeCollisionExcess params candidate
          leftDifference rightDifference) ≤
      ∑ leftDifference :
          RingGSWCiphertext q (degree + 1) ringRank params.levels,
        ∑ rightDifference :
            RingGSWCiphertext q (degree + 1) ringRank params.levels,
          if (differencePairBinaryTransposeMatrix params
              (leftDifference, rightDifference)).rank <
              TGSW.rowCount ringRank params.levels then
            (Fintype.card
              (DiagonalChallenge q degree ringRank params.levels) : ℝ) ^ 2
          else 0 := by
      apply Finset.sum_le_sum
      intro leftDifference _
      apply Finset.sum_le_sum
      intro rightDifference _
      by_cases rank_failure :
          (differencePairBinaryTransposeMatrix params
            (leftDifference, rightDifference)).rank <
              TGSW.rowCount ringRank params.levels
      · simp only [rank_failure, if_true]
        exact differencePairChallengeCollisionExcess_le_challengeCard_sq
          params candidate leftDifference rightDifference
      · simp only [rank_failure, if_false]
        have rank_le := Matrix.rank_le_width
          (differencePairBinaryTransposeMatrix params
            (leftDifference, rightDifference))
        have full_rank :
            (differencePairBinaryTransposeMatrix params
              (leftDifference, rightDifference)).rank =
              TGSW.rowCount ringRank params.levels := by
          omega
        rw [differencePairChallengeCollisionExcess_eq_zero_of_binaryFullRank
          params heven candidate leftDifference rightDifference localParity full_rank]
    _ = (differencePairBinaryRankFailureCount
          (degree := degree) (ringRank := ringRank) params : ℝ) *
        (Fintype.card
          (DiagonalChallenge q degree ringRank params.levels) : ℝ) ^ 2 := by
      simp [differencePairBinaryRankFailureCount, nsmul_eq_mul]
      rw [Finset.sum_mul]

/-- The corresponding source-independent global budget is bounded by the rank-failure ratio
times one explicit difference-space and challenge-space magnitude factor.  This formula records
why the rank-failure probability alone is not yet a negligible collision bound. -/
theorem globalDifferencePairCollisionBudget_le_rankFailureRatio_mul
    [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree))) :
    globalDifferencePairCollisionBudget
        (degree := degree) (ringRank := ringRank) params candidate ≤
      ((differencePairBinaryRankFailureCount
          (degree := degree) (ringRank := ringRank) params : ℝ) /
        (Fintype.card
          (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) ^ 2) *
        (Fintype.card
          (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) *
        (Fintype.card
          (DiagonalChallenge q degree ringRank params.levels) : ℝ) := by
  let D : ℝ :=
    Fintype.card
      (RingGSWCiphertext q (degree + 1) ringRank params.levels)
  let C : ℝ :=
    Fintype.card (DiagonalChallenge q degree ringRank params.levels)
  let B : ℝ :=
    differencePairBinaryRankFailureCount
      (degree := degree) (ringRank := ringRank) params
  have D_positive : 0 < D := by
    dsimp only [D]
    exact_mod_cast Fintype.card_pos
  have C_positive : 0 < C := by
    dsimp only [C]
    exact_mod_cast Fintype.card_pos
  have total_bound :
      totalDifferencePairChallengeCollisionExcess
          (degree := degree) (ringRank := ringRank) params candidate ≤
        B * C ^ 2 := by
    simpa only [B, C] using
      totalDifferencePairChallengeCollisionExcess_le_rankFailureCount_mul
        params heven candidate localParity
  unfold globalDifferencePairCollisionBudget
  change
    totalDifferencePairChallengeCollisionExcess
        (degree := degree) (ringRank := ringRank) params candidate / (D * C) ≤
      (B / D ^ 2) * D * C
  calc
    totalDifferencePairChallengeCollisionExcess
          (degree := degree) (ringRank := ringRank) params candidate / (D * C) ≤
        (B * C ^ 2) / (D * C) := by
      exact div_le_div_of_nonneg_right total_bound
        (mul_nonneg D_positive.le C_positive.le)
    _ = (B / D ^ 2) * D * C := by
      field_simp [D_positive.ne', C_positive.ne']

/-- For coefficient modulus two and a power-of-two ring degree, the local-homomorphism premise
is automatic: full rank of the explicit binary difference pair alone forces exactly zero
challenge-collision excess. -/
theorem differencePairChallengeCollisionExcess_eq_zero_of_binaryFullRank_binaryPowerOfTwo
    (exponent : ℕ)
    (params : Gadget.Base.Parameters 2)
    (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext 2 ((2 ^ exponent - 1) + 1) ringRank params.levels)
    (fullRank :
      (differencePairBinaryTransposeMatrix
        (degree := 2 ^ exponent - 1) params
        (leftDifference, rightDifference)).rank =
          TGSW.rowCount ringRank params.levels) :
    differencePairChallengeCollisionExcess
        (degree := 2 ^ exponent - 1) params candidate
        leftDifference rightDifference = 0 := by
  have degree_positive : 0 < 2 ^ exponent := pow_pos (by omega) exponent
  have degree_eq : (2 ^ exponent - 1) + 1 = 2 ^ exponent := by
    omega
  have localParity : IsLocalHom
      (rqParityEval dvd_rfl (Nat.succ_pos (2 ^ exponent - 1))) := by
    exact PowerOfTwoLocalRing.rqParityEval_isLocalHom_binary_powerOfTwo_of_degree_eq
      degree_eq (Nat.succ_pos (2 ^ exponent - 1))
  exact differencePairChallengeCollisionExcess_eq_zero_of_binaryFullRank
    params dvd_rfl candidate leftDifference rightDifference localParity fullRank

/-- Production specialization: for coefficient modulus `2^k`, `k > 0`, and power-of-two ring
degree, full rank of the explicit binary difference pair alone forces exactly zero native
challenge-collision excess. -/
theorem differencePairChallengeCollisionExcess_eq_zero_of_binaryFullRank_powerOfTwo
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (degreeExponent : ℕ)
    (params : Gadget.Base.Parameters (2 ^ modulusExponent))
    (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext (2 ^ modulusExponent)
        ((2 ^ degreeExponent - 1) + 1) ringRank params.levels)
    (fullRank :
      (differencePairBinaryTransposeMatrix
        (degree := 2 ^ degreeExponent - 1) params
        (leftDifference, rightDifference)).rank =
          TGSW.rowCount ringRank params.levels) :
    differencePairChallengeCollisionExcess
        (degree := 2 ^ degreeExponent - 1) params candidate
        leftDifference rightDifference = 0 := by
  have degree_eq : (2 ^ degreeExponent - 1) + 1 = 2 ^ degreeExponent := by
    have degree_positive : 0 < 2 ^ degreeExponent := pow_pos (by omega) degreeExponent
    omega
  let heven : 2 ∣ 2 ^ modulusExponent :=
    pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)
  have localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos (2 ^ degreeExponent - 1))) := by
    exact PowerOfTwoLocalRing.rqParityEval_isLocalHom_powerOfTwo_of_degree_eq
      modulusExponent modulusExponent_positive degree_eq
        (Nat.succ_pos (2 ^ degreeExponent - 1))
  exact differencePairChallengeCollisionExcess_eq_zero_of_binaryFullRank
    params heven candidate leftDifference rightDifference localParity fullRank

/-- At production power-of-two modulus and degree, the complete collision excess is bounded by
the number of binary-rank-deficient ordered pairs times the explicit worst-case challenge-pair
magnitude. -/
theorem totalDifferencePairChallengeCollisionExcess_le_rankFailureCount_mul_powerOfTwo
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (degreeExponent : ℕ)
    (params : Gadget.Base.Parameters (2 ^ modulusExponent))
    (candidate : Bool) :
    totalDifferencePairChallengeCollisionExcess
        (degree := 2 ^ degreeExponent - 1) (ringRank := ringRank)
        params candidate ≤
      (differencePairBinaryRankFailureCount
          (degree := 2 ^ degreeExponent - 1) (ringRank := ringRank) params : ℝ) *
        (Fintype.card
          (DiagonalChallenge (2 ^ modulusExponent)
            (2 ^ degreeExponent - 1) ringRank params.levels) : ℝ) ^ 2 := by
  have degree_eq : (2 ^ degreeExponent - 1) + 1 = 2 ^ degreeExponent := by
    have degree_positive : 0 < 2 ^ degreeExponent := pow_pos (by omega) degreeExponent
    omega
  let heven : 2 ∣ 2 ^ modulusExponent :=
    pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)
  have localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos (2 ^ degreeExponent - 1))) := by
    exact PowerOfTwoLocalRing.rqParityEval_isLocalHom_powerOfTwo_of_degree_eq
      modulusExponent modulusExponent_positive degree_eq
        (Nat.succ_pos (2 ^ degreeExponent - 1))
  exact totalDifferencePairChallengeCollisionExcess_le_rankFailureCount_mul
    params heven candidate localParity

/-- Premise-free production form of the normalized bad-pair accounting bound. -/
theorem globalDifferencePairCollisionBudget_le_rankFailureRatio_mul_powerOfTwo
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (degreeExponent : ℕ)
    (params : Gadget.Base.Parameters (2 ^ modulusExponent))
    (candidate : Bool) :
    globalDifferencePairCollisionBudget
        (degree := 2 ^ degreeExponent - 1) (ringRank := ringRank)
        params candidate ≤
      ((differencePairBinaryRankFailureCount
          (degree := 2 ^ degreeExponent - 1) (ringRank := ringRank) params : ℝ) /
        (Fintype.card
          (RingGSWCiphertext (2 ^ modulusExponent)
            ((2 ^ degreeExponent - 1) + 1) ringRank params.levels) : ℝ) ^ 2) *
        (Fintype.card
          (RingGSWCiphertext (2 ^ modulusExponent)
            ((2 ^ degreeExponent - 1) + 1) ringRank params.levels) : ℝ) *
        (Fintype.card
          (DiagonalChallenge (2 ^ modulusExponent)
            (2 ^ degreeExponent - 1) ringRank params.levels) : ℝ) := by
  have degree_eq : (2 ^ degreeExponent - 1) + 1 = 2 ^ degreeExponent := by
    have degree_positive : 0 < 2 ^ degreeExponent := pow_pos (by omega) degreeExponent
    omega
  let heven : 2 ∣ 2 ^ modulusExponent :=
    pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)
  have localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos (2 ^ degreeExponent - 1))) := by
    exact PowerOfTwoLocalRing.rqParityEval_isLocalHom_powerOfTwo_of_degree_eq
      modulusExponent modulusExponent_positive degree_eq
        (Nat.succ_pos (2 ^ degreeExponent - 1))
  exact globalDifferencePairCollisionBudget_le_rankFailureRatio_mul
    params heven candidate localParity

/-- Sample two independent native differences and expose their binary rectangular matrix. -/
noncomputable def differencePairBinaryTransposeSampler [NeZero q]
    (params : Gadget.Base.Parameters q) :
    ProbComp
      (Matrix
        (Fin (TGSW.rowCount ringRank params.levels +
          TGSW.rowCount ringRank params.levels))
        (Fin (TGSW.rowCount ringRank params.levels)) (ZMod 2)) := do
  let leftDifference ←
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  let rightDifference ←
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  return differencePairBinaryTransposeMatrix params
    (leftDifference, rightDifference)

/-- At exact capacity and even base, the concrete paired binary matrix is exactly uniform on the
`2m`-by-`m` binary matrix space. -/
theorem differencePairBinaryTransposeSampler_uniform_evalDist [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (halfBase : ℕ) [NeZero halfBase]
    (hbase : params.base = halfBase * 2) :
    evalDist
        (differencePairBinaryTransposeSampler
          (degree := degree) (ringRank := ringRank) params) =
      evalDist
        ($ᵗ Matrix
          (Fin (TGSW.rowCount ringRank params.levels +
            TGSW.rowCount ringRank params.levels))
          (Fin (TGSW.rowCount ringRank params.levels)) (ZMod 2)) := by
  let dimension := TGSW.rowCount ringRank params.levels
  let Difference := RingGSWCiphertext q (degree + 1) ringRank params.levels
  let BinaryMatrix := Matrix (Fin dimension) (Fin dimension) (ZMod 2)
  let RectangularMatrix := Matrix (Fin (dimension + dimension)) (Fin dimension) (ZMod 2)
  let transform := differenceBinaryRowMatrix
    (degree := degree) (ringRank := ringRank) params
  have hsingle : evalDist (transform <$> ($ᵗ Difference)) =
      evalDist ($ᵗ BinaryMatrix) :=
    differenceBinaryRowMatrix_uniform_evalDist
      params hcapacity halfBase hbase
  have hfirst :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      hsingle (fun leftMatrix =>
        (transform <$> ($ᵗ Difference)) >>= fun rightMatrix =>
          pure (pairedTransposeMatrix leftMatrix rightMatrix))
  have hsecond :
      evalDist (do
        let leftMatrix ← $ᵗ BinaryMatrix
        let rightMatrix ← transform <$> ($ᵗ Difference)
        pure (pairedTransposeMatrix leftMatrix rightMatrix)) =
      evalDist (do
        let leftMatrix ← $ᵗ BinaryMatrix
        let rightMatrix ← $ᵗ BinaryMatrix
        pure (pairedTransposeMatrix leftMatrix rightMatrix)) := by
    refine evalDist_bind_congr' ($ᵗ BinaryMatrix) fun leftMatrix => ?_
    exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      hsingle (fun rightMatrix => pure
        (pairedTransposeMatrix leftMatrix rightMatrix))
  let PairSampler : ProbComp (BinaryMatrix × BinaryMatrix) := do
    let leftMatrix ← $ᵗ BinaryMatrix
    let rightMatrix ← $ᵗ BinaryMatrix
    return (leftMatrix, rightMatrix)
  have hpair : evalDist PairSampler =
      evalDist ($ᵗ (BinaryMatrix × BinaryMatrix)) :=
    FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
  have hcombined := evalDist_map_eq_of_evalDist_eq hpair
    (fun matrices : BinaryMatrix × BinaryMatrix =>
      pairedTransposeMatrix matrices.1 matrices.2)
  have huniform :
      evalDist
          ((fun matrices : BinaryMatrix × BinaryMatrix =>
            pairedTransposeMatrix matrices.1 matrices.2) <$>
            ($ᵗ (BinaryMatrix × BinaryMatrix))) =
        evalDist ($ᵗ RectangularMatrix) :=
    pairedTransposeMatrix_uniform_evalDist dimension
  calc
    evalDist
        (differencePairBinaryTransposeSampler
          (degree := degree) (ringRank := ringRank) params) =
      evalDist (do
        let leftMatrix ← transform <$> ($ᵗ Difference)
        let rightMatrix ← transform <$> ($ᵗ Difference)
        pure (pairedTransposeMatrix leftMatrix rightMatrix)) := by
          congr 1
          simp [differencePairBinaryTransposeSampler,
            differencePairBinaryTransposeMatrix, transform, Difference,
            map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (do
        let leftMatrix ← $ᵗ BinaryMatrix
        let rightMatrix ← transform <$> ($ᵗ Difference)
        pure (pairedTransposeMatrix leftMatrix rightMatrix)) := hfirst
    _ = evalDist (do
        let leftMatrix ← $ᵗ BinaryMatrix
        let rightMatrix ← $ᵗ BinaryMatrix
        pure (pairedTransposeMatrix leftMatrix rightMatrix)) := hsecond
    _ = evalDist
        ((fun matrices : BinaryMatrix × BinaryMatrix =>
          pairedTransposeMatrix matrices.1 matrices.2) <$> PairSampler) := by
            congr 1
            simp [PairSampler, map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist
        ((fun matrices : BinaryMatrix × BinaryMatrix =>
          pairedTransposeMatrix matrices.1 matrices.2) <$>
            ($ᵗ (BinaryMatrix × BinaryMatrix))) := hcombined
    _ = evalDist ($ᵗ RectangularMatrix) := huniform

/-- Exact counting interpretation of the concrete binary rank-failure event before applying the
finite-field estimate. -/
theorem differencePairBinaryRankFailureProbability_eq_count_div [NeZero q]
    (params : Gadget.Base.Parameters q) :
    Pr[(fun matrix : Matrix
          (Fin (TGSW.rowCount ringRank params.levels +
            TGSW.rowCount ringRank params.levels))
          (Fin (TGSW.rowCount ringRank params.levels)) (ZMod 2) ↦
          matrix.rank < TGSW.rowCount ringRank params.levels) |
        differencePairBinaryTransposeSampler
          (degree := degree) (ringRank := ringRank) params] =
      (differencePairBinaryRankFailureCount
          (degree := degree) (ringRank := ringRank) params : ℝ≥0∞) /
        (Fintype.card
          (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ≥0∞) ^ 2 := by
  classical
  let Difference := RingGSWCiphertext q (degree + 1) ringRank params.levels
  let RectangularMatrix := Matrix
    (Fin (TGSW.rowCount ringRank params.levels +
      TGSW.rowCount ringRank params.levels))
    (Fin (TGSW.rowCount ringRank params.levels)) (ZMod 2)
  let transform : Difference × Difference → RectangularMatrix :=
    differencePairBinaryTransposeMatrix params
  let PairSampler : ProbComp (Difference × Difference) := do
    let leftDifference ← $ᵗ Difference
    let rightDifference ← $ᵗ Difference
    return (leftDifference, rightDifference)
  have pair_uniform : evalDist PairSampler =
      evalDist ($ᵗ (Difference × Difference)) :=
    FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
  have mapped_uniform := evalDist_map_eq_of_evalDist_eq pair_uniform transform
  have sampler_dist :
      evalDist
          (differencePairBinaryTransposeSampler
            (degree := degree) (ringRank := ringRank) params) =
        evalDist (transform <$> ($ᵗ (Difference × Difference))) := by
    calc
      evalDist
          (differencePairBinaryTransposeSampler
            (degree := degree) (ringRank := ringRank) params) =
        evalDist (transform <$> PairSampler) := by
          congr 1
          simp [differencePairBinaryTransposeSampler, PairSampler, transform, Difference,
            map_eq_bind_pure_comp, bind_assoc]
      _ = evalDist (transform <$> ($ᵗ (Difference × Difference))) :=
        mapped_uniform
  calc
    Pr[(fun matrix : RectangularMatrix ↦
          matrix.rank < TGSW.rowCount ringRank params.levels) |
        differencePairBinaryTransposeSampler
          (degree := degree) (ringRank := ringRank) params] =
      Pr[(fun matrix : RectangularMatrix ↦
          matrix.rank < TGSW.rowCount ringRank params.levels) |
        transform <$> ($ᵗ (Difference × Difference))] :=
      probEvent_congr' (fun _ _ ↦ Iff.rfl) sampler_dist
    _ = Pr[(fun differences : Difference × Difference ↦
          (transform differences).rank < TGSW.rowCount ringRank params.levels) |
        ($ᵗ (Difference × Difference))] := by
      rw [probEvent_map]
      rfl
    _ = (differencePairBinaryRankFailureCount
          (degree := degree) (ringRank := ringRank) params : ℝ≥0∞) /
        (Fintype.card Difference : ℝ≥0∞) ^ 2 := by
      rw [probEvent_uniformSample]
      change
        (((Finset.univ : Finset (Difference × Difference)).filter
          (fun differences ↦
            (differencePairBinaryTransposeMatrix params differences).rank <
              TGSW.rowCount ringRank params.levels)).card : ℝ≥0∞) /
            Fintype.card (Difference × Difference) = _
      rw [← differencePairBinaryRankFailureCount_eq_filter_card params,
        Fintype.card_prod, Nat.cast_mul, pow_two]

/-- The concrete paired binary rank-failure probability has exponential slack in the native row
count, unlike the constant square-matrix obstruction. -/
theorem differencePairBinaryRankFailure_le [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (halfBase : ℕ) [NeZero halfBase]
    (hbase : params.base = halfBase * 2) :
    Pr[(fun matrix : Matrix
          (Fin (TGSW.rowCount ringRank params.levels +
            TGSW.rowCount ringRank params.levels))
          (Fin (TGSW.rowCount ringRank params.levels)) (ZMod 2) =>
          matrix.rank < TGSW.rowCount ringRank params.levels) |
        differencePairBinaryTransposeSampler
          (degree := degree) (ringRank := ringRank) params] ≤
      2 / (2 : ℝ≥0∞) ^ (TGSW.rowCount ringRank params.levels + 1) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let dimension := TGSW.rowCount ringRank params.levels
  let RectangularMatrix := Matrix
    (Fin (dimension + dimension)) (Fin dimension) (ZMod 2)
  have hdist :
      evalDist
          (differencePairBinaryTransposeSampler
            (degree := degree) (ringRank := ringRank) params) =
        evalDist ($ᵗ RectangularMatrix) :=
    differencePairBinaryTransposeSampler_uniform_evalDist
      params hcapacity halfBase hbase
  calc
    Pr[(fun matrix : RectangularMatrix => matrix.rank < dimension) |
        differencePairBinaryTransposeSampler
          (degree := degree) (ringRank := ringRank) params] =
      Pr[(fun matrix : RectangularMatrix => matrix.rank < dimension) |
        ($ᵗ RectangularMatrix)] :=
      probEvent_congr' (fun _ _ => Iff.rfl) hdist
    _ ≤ 2 / (Fintype.card (ZMod 2) : ℝ≥0∞) ^ (dimension + 1) :=
      FormalProof4FHE.FiniteFieldRank.rankFailure_le
        (F := ZMod 2) dimension dimension
    _ = 2 / (2 : ℝ≥0∞) ^ (dimension + 1) := by norm_num

/-- Cardinal form of the exact-capacity rank-failure estimate.  This is the probability factor
appearing in any subsequent deficient-pair magnitude bound. -/
theorem differencePairBinaryRankFailureCount_div_le [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (halfBase : ℕ) [NeZero halfBase]
    (hbase : params.base = halfBase * 2) :
    (differencePairBinaryRankFailureCount
        (degree := degree) (ringRank := ringRank) params : ℝ≥0∞) /
      (Fintype.card
        (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ≥0∞) ^ 2 ≤
      2 / (2 : ℝ≥0∞) ^ (TGSW.rowCount ringRank params.levels + 1) := by
  rw [← differencePairBinaryRankFailureProbability_eq_count_div params]
  exact differencePairBinaryRankFailure_le params hcapacity halfBase hbase

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
