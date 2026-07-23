/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDiagonalResidualNormalForm
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Determinant Form of the Native Selected-Diagonal Rank Event

The fixed-difference selected-diagonal operator is a linear endomorphism of a finite free module.
This module gives it a canonical matrix and proves that its function-level bijectivity predicate
is exactly the statement that the matrix determinant is a unit.  Consequently the diagonal
bad-rank probability already used by the whole-key TFHE certificate is exactly an explicit
determinant non-unit probability over the production coefficient ring.

No field assumption is used: invertibility of a square matrix over an arbitrary commutative ring
is characterized by its determinant being a unit.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

variable {q degree ringRank : ℕ}

/-- Scalar-linearity of the fixed-difference row operator. -/
theorem rowOperator_smul {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (scalar : R) (values : Fin (TGSW.rowCount dimension levels) → R) :
    rowOperator candidate digits (scalar • values) =
      scalar • rowOperator candidate digits values := by
  funext row
  simp only [rowOperator, Pi.smul_apply, smul_eq_mul]
  cases candidate
  · simp only [signedValue_false, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro index _
    ring
  · simp only [signedValue_true, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro index _
    ring

/-- The fixed-difference row operator as a linear endomorphism. -/
def rowLinearMap {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    (Fin (TGSW.rowCount dimension levels) → R) →ₗ[R]
      (Fin (TGSW.rowCount dimension levels) → R) where
  toFun := rowOperator candidate digits
  map_add' := rowOperator_add candidate digits
  map_smul' := rowOperator_smul candidate digits

/-- Canonical square matrix of the fixed-difference selected-diagonal row operator. -/
noncomputable def rowMatrix {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    Matrix (Fin (TGSW.rowCount dimension levels))
      (Fin (TGSW.rowCount dimension levels)) R :=
  LinearMap.toMatrix' (rowLinearMap candidate digits)

@[simp]
theorem rowMatrix_mulVec {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (values : Fin (TGSW.rowCount dimension levels) → R) :
    rowMatrix candidate digits *ᵥ values = rowOperator candidate digits values := by
  simp [rowMatrix, rowLinearMap]

/-- Entrywise identity-plus-digit form of the concrete row matrix.  This is the form intended for
determinant estimates over a chosen coefficient ring. -/
theorem rowMatrix_apply {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (row column : Fin (TGSW.rowCount dimension levels)) :
    rowMatrix candidate digits row column =
      (if row = column then 1 else 0) +
        digits row (finProdFinEquiv.symm column).1
            (finProdFinEquiv.symm column).2 *
          signedValue candidate 1 := by
  classical
  change (Pi.single column (1 : R) :
      Fin (TGSW.rowCount dimension levels) → R) row +
      (∑ index : Fin (dimension + 1) × Fin levels,
        digits row index.1 index.2 *
          signedValue candidate
            ((Pi.single column (1 : R) :
              Fin (TGSW.rowCount dimension levels) → R)
                (finProdFinEquiv index))) = _
  rw [Pi.single_apply]
  congr 1
  rw [Finset.sum_eq_single (finProdFinEquiv.symm column)]
  · rw [finProdFinEquiv.apply_symm_apply]
    simp
  · intro other _ hne
    have himage : finProdFinEquiv other ≠ column := by
      intro heq
      apply hne
      exact finProdFinEquiv.injective
        (heq.trans (finProdFinEquiv.apply_symm_apply column).symm)
    simp [himage, signedValue]
  · simp

/-- Over a commutative ring, a square matrix acts bijectively on its finite free module exactly
when its determinant is a unit. -/
theorem matrix_mulVec_bijective_iff_isUnit_det
    {R Index : Type} [CommRing R] [Fintype Index] [DecidableEq Index]
    (matrix : Matrix Index Index R) :
    Function.Bijective (fun values => matrix *ᵥ values) ↔ IsUnit matrix.det := by
  constructor
  · intro hbijective
    let equivalence := LinearEquiv.ofBijective matrix.mulVecLin hbijective
    let inverseMatrix : Matrix Index Index R :=
      LinearMap.toMatrix' equivalence.symm.toLinearMap
    have hmatrix : LinearMap.toMatrix' matrix.mulVecLin = matrix := by
      rw [← Matrix.toLin'_apply' matrix, LinearMap.toMatrix'_toLin']
    have hright : matrix * inverseMatrix = 1 := by
      calc
        matrix * inverseMatrix =
            LinearMap.toMatrix' matrix.mulVecLin *
              LinearMap.toMatrix' equivalence.symm.toLinearMap := by
                rw [hmatrix]
        _ = LinearMap.toMatrix'
              (matrix.mulVecLin.comp equivalence.symm.toLinearMap) :=
            (LinearMap.toMatrix'_comp _ _).symm
        _ = LinearMap.toMatrix' LinearMap.id := by
            congr 1
            apply LinearMap.ext
            intro values
            exact equivalence.apply_symm_apply values
        _ = 1 := LinearMap.toMatrix'_id
    exact Matrix.isUnit_det_of_right_inverse hright
  · intro hdet
    let invertible : Invertible matrix := Matrix.invertibleOfIsUnitDet matrix hdet
    have hbijective := (matrix.toLinearEquiv' invertible).bijective
    have heq :
        (matrix.toLinearEquiv' invertible : (Index → R) → Index → R) =
          (fun values => matrix *ᵥ values) := by
      funext values
      rfl
    rw [← heq]
    exact hbijective

/-- Exact determinant criterion for the concrete fixed-difference row operator. -/
theorem rowOperator_bijective_iff_isUnit_det
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    Function.Bijective (rowOperator candidate digits) ↔
      IsUnit (rowMatrix candidate digits).det := by
  simpa only [rowMatrix_mulVec] using
    (matrix_mulVec_bijective_iff_isUnit_det (rowMatrix candidate digits))

/-- Determinant form of the bad-rank event for one uniform difference ciphertext. -/
def DiagonalRowDeterminantFailure [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) : Prop :=
  ¬ IsUnit
    (rowMatrix candidate (differenceEntryDigits params difference)).det

/-- The original function-level bad-rank event is exactly determinant noninvertibility. -/
theorem diagonalRowRankFailure_iff_determinantFailure [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    DiagonalRowRankFailure params candidate difference ↔
      DiagonalRowDeterminantFailure params candidate difference := by
  unfold DiagonalRowRankFailure DiagonalRowDeterminantFailure
  rw [rowOperator_bijective_iff_isUnit_det]

/-- Exact probability that the concrete fixed-difference row determinant is not a unit. -/
noncomputable def diagonalRowDeterminantFailureProbability [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool) : ℝ :=
  Pr[DiagonalRowDeterminantFailure params candidate |
    ($ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels)].toReal

/-- The determinant event is not a relaxation: its probability equals the existing exact
bad-rank probability definitionally up to the proved event equivalence. -/
theorem diagonalRowRankFailureProbability_eq_determinantFailureProbability [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool) :
    diagonalRowRankFailureProbability (degree := degree) (ringRank := ringRank)
        params candidate =
      diagonalRowDeterminantFailureProbability (degree := degree) (ringRank := ringRank)
        params candidate := by
  unfold diagonalRowRankFailureProbability diagonalRowDeterminantFailureProbability
  congr 2
  funext difference
  exact propext (diagonalRowRankFailure_iff_determinantFailure
    params candidate difference)

/-- Determinant expansion of the rank-sharp selected-diagonal loss used by the whole-key
certificate. -/
theorem rankSharpDiagonalOperatorLoss_eq_determinantFailure_add_mixedError [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    rankSharpDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate =
      diagonalRowDeterminantFailureProbability (degree := degree)
          (ringRank := ringRank) params candidate +
        mixedDiagonalErrorDistance (ringRank := ringRank) params
          sourceErrorSampler targetErrorSampler candidate := by
  unfold rankSharpDiagonalOperatorLoss
  rw [diagonalRowRankFailureProbability_eq_determinantFailureProbability]

/-- Selected-diagonal budget after replacing the exact determinant-failure probability by any
proved scalar bound for each candidate bit. -/
noncomputable def determinantBoundedDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (determinantFailureBound : Bool → ℝ)
    (candidate : Bool) : ℝ :=
  determinantFailureBound candidate +
    mixedDiagonalErrorDistance (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate

/-- Coordinate-independent determinant-bounded diagonal budget. -/
noncomputable def worstCaseDeterminantBoundedDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (determinantFailureBound : Bool → ℝ) : ℝ :=
  max
    (determinantBoundedDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler determinantFailureBound false)
    (determinantBoundedDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler determinantFailureBound true)

theorem determinantBoundedDiagonalOperatorLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (determinantFailureBound : Bool → ℝ)
    (hbound_nonneg : ∀ candidate, 0 ≤ determinantFailureBound candidate)
    (candidate : Bool) :
    0 ≤ determinantBoundedDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler determinantFailureBound candidate :=
  add_nonneg (hbound_nonneg candidate)
    (mixedDiagonalErrorDistance_nonneg (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate)

theorem worstCaseDeterminantBoundedDiagonalOperatorLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (determinantFailureBound : Bool → ℝ)
    (hbound_nonneg : ∀ candidate, 0 ≤ determinantFailureBound candidate) :
    0 ≤ worstCaseDeterminantBoundedDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler determinantFailureBound := by
  exact (determinantBoundedDiagonalOperatorLoss_nonneg (ringRank := ringRank) params
    sourceErrorSampler targetErrorSampler determinantFailureBound hbound_nonneg false).trans
      (le_max_left _ _)

/-- Install any proved determinant-failure estimate in the selected-diagonal reduction while
retaining the exact mixed transformed-error distance. -/
theorem tvDist_diagonalExperiment_directEntry_le_determinantBoundedOperatorLoss [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (determinantFailureBound : Bool → ℝ)
    (hdeterminant : ∀ candidate,
      diagonalRowDeterminantFailureProbability (degree := degree)
          (ringRank := ringRank) params candidate ≤
        determinantFailureBound candidate)
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      determinantBoundedDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler determinantFailureBound
        (hidden coordinate) := by
  have h := tvDist_diagonalExperiment_directEntry_le_rankSharpOperatorLoss
    params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate
  calc
    _ ≤ rankSharpDiagonalOperatorLoss (ringRank := ringRank) params
          sourceErrorSampler targetErrorSampler (hidden coordinate) := h
    _ = diagonalRowDeterminantFailureProbability (degree := degree)
          (ringRank := ringRank) params (hidden coordinate) +
        mixedDiagonalErrorDistance (ringRank := ringRank) params
          sourceErrorSampler targetErrorSampler (hidden coordinate) :=
      rankSharpDiagonalOperatorLoss_eq_determinantFailure_add_mixedError
        params sourceErrorSampler targetErrorSampler (hidden coordinate)
    _ ≤ determinantFailureBound (hidden coordinate) +
        mixedDiagonalErrorDistance (ringRank := ringRank) params
          sourceErrorSampler targetErrorSampler (hidden coordinate) :=
      add_le_add (hdeterminant (hidden coordinate)) le_rfl
    _ = _ := rfl

/-- Uniform version of the determinant-bounded selected-diagonal theorem for whole-key
certificates. -/
theorem tvDist_diagonalExperiment_directEntry_le_worstCaseDeterminantBoundedOperatorLoss
    [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (determinantFailureBound : Bool → ℝ)
    (hdeterminant : ∀ candidate,
      diagonalRowDeterminantFailureProbability (degree := degree)
          (ringRank := ringRank) params candidate ≤
        determinantFailureBound candidate)
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      worstCaseDeterminantBoundedDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler determinantFailureBound := by
  have h := tvDist_diagonalExperiment_directEntry_le_determinantBoundedOperatorLoss
    params sourceErrorSampler targetErrorSampler determinantFailureBound hdeterminant
    hidden ringSecret coordinate
  cases hbit : hidden coordinate
  · exact h.trans (by
      simpa only [hbit, worstCaseDeterminantBoundedDiagonalOperatorLoss] using
        (le_max_left
          (determinantBoundedDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler determinantFailureBound false)
          (determinantBoundedDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler determinantFailureBound true)))
  · exact h.trans (by
      simpa only [hbit, worstCaseDeterminantBoundedDiagonalOperatorLoss] using
        (le_max_right
          (determinantBoundedDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler determinantFailureBound false)
          (determinantBoundedDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler determinantFailureBound true)))

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
