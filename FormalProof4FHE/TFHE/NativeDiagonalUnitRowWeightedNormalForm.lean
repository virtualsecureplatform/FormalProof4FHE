/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDiagonalUnitRowSlice
import FormalProof4FHE.TFHE.NativeDiagonalRetainedFiberCokernel
import FormalProof4FHE.Probability.FiniteRowKernelMoment

/-!
# Unit-Row Weighted Retained-Fiber Normal Form

The unit-row slice embeds every retained transformed-error fiber into the coefficient-digit tensor
with one matrix column omitted.  This module upgrades that embedding to an exact equivalence with
its valid-image subtype and transports the weighted self-kernel sum to that image.

This is the form needed for a subsequent Fourier or rank estimate: the remaining coordinates are
explicit independent base digits, while validity records exactly when the uniquely reconstructed
selected digit column lies in the small digit alphabet.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-! ## Explicit algebraic reconstruction of the selected digit column -/

/-- Fill one distinguished digit column into an omitted-column tensor. -/
def completeDigitTensor
    {base degree ringRank levels : ℕ}
    (selected : DifferenceDigitColumn ringRank levels)
    (omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected)
    (selectedDigits :
      Fin (TGSW.rowCount ringRank levels) → Fin (degree + 1) → Fin base) :
    DifferenceDigitTensor base degree ringRank levels :=
  fun row block coefficient level =>
    if hcolumn : (block, level) = selected then
      selectedDigits row coefficient
    else
      omitted row ⟨(block, level), hcolumn⟩ coefficient

@[simp]
theorem completeDigitTensor_selected
    {base degree ringRank levels : ℕ}
    (selected : DifferenceDigitColumn ringRank levels)
    (omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected)
    (selectedDigits :
      Fin (TGSW.rowCount ringRank levels) → Fin (degree + 1) → Fin base)
    (row : Fin (TGSW.rowCount ringRank levels))
    (coefficient : Fin (degree + 1)) :
    completeDigitTensor selected omitted selectedDigits row selected.1 coefficient selected.2 =
      selectedDigits row coefficient := by
  simp [completeDigitTensor]

@[simp]
theorem completeDigitTensor_other
    {base degree ringRank levels : ℕ}
    (selected : DifferenceDigitColumn ringRank levels)
    (omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected)
    (selectedDigits :
      Fin (TGSW.rowCount ringRank levels) → Fin (degree + 1) → Fin base)
    (row : Fin (TGSW.rowCount ringRank levels))
    (column : DifferenceDigitColumn ringRank levels) (hcolumn : column ≠ selected)
    (coefficient : Fin (degree + 1)) :
    completeDigitTensor selected omitted selectedDigits row column.1 coefficient column.2 =
      omitted row ⟨column, hcolumn⟩ coefficient := by
  simp [completeDigitTensor, hcolumn]

@[simp]
theorem digitTensorWithoutColumn_completeDigitTensor
    {base degree ringRank levels : ℕ}
    (selected : DifferenceDigitColumn ringRank levels)
    (omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected)
    (selectedDigits :
      Fin (TGSW.rowCount ringRank levels) → Fin (degree + 1) → Fin base) :
    digitTensorWithoutColumn selected
        (completeDigitTensor selected omitted selectedDigits) =
      omitted := by
  funext row column coefficient
  simp [digitTensorWithoutColumn, column.property]

@[simp]
theorem completeDigitTensor_digitTensorWithoutColumn
    {base degree ringRank levels : ℕ}
    (selected : DifferenceDigitColumn ringRank levels)
    (digits : DifferenceDigitTensor base degree ringRank levels) :
    completeDigitTensor selected (digitTensorWithoutColumn selected digits)
        (fun row coefficient =>
          digits row selected.1 coefficient selected.2) =
      digits := by
  funext row block coefficient level
  by_cases hcolumn : (block, level) = selected
  · have hblock : block = selected.1 := congrArg Prod.fst hcolumn
    have hlevel : level = selected.2 := congrArg Prod.snd hcolumn
    subst block
    subst level
    simp
  · simp [completeDigitTensor, digitTensorWithoutColumn, hcolumn]

@[simp]
theorem digitTensorRingDigits_completeDigitTensor_selected
    {q base degree ringRank levels : ℕ} [NeZero q]
    (selected : DifferenceDigitColumn ringRank levels)
    (omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected)
    (selectedDigits :
      Fin (TGSW.rowCount ringRank levels) → Fin (degree + 1) → Fin base)
    (row : Fin (TGSW.rowCount ringRank levels)) :
    digitTensorRingDigits (q := q)
        (completeDigitTensor selected omitted selectedDigits)
        row selected.1 selected.2 =
      coefficientDigitPolynomial q (selectedDigits row) := by
  unfold digitTensorRingDigits
  congr 1
  funext coefficient
  simp

@[simp]
theorem digitTensorRingDigits_completeDigitTensor_other
    {q base degree ringRank levels : ℕ} [NeZero q]
    (selected : DifferenceDigitColumn ringRank levels)
    (omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected)
    (selectedDigits :
      Fin (TGSW.rowCount ringRank levels) → Fin (degree + 1) → Fin base)
    (row : Fin (TGSW.rowCount ringRank levels))
    (column : DifferenceDigitColumn ringRank levels) (hcolumn : column ≠ selected) :
    digitTensorRingDigits (q := q)
        (completeDigitTensor selected omitted selectedDigits)
        row column.1 column.2 =
      coefficientDigitPolynomial q (fun coefficient =>
        omitted row ⟨column, hcolumn⟩ coefficient) := by
  unfold digitTensorRingDigits
  congr 1
  funext coefficient
  simp [hcolumn]

 /-- One row of a coefficient-digit tensor with the distinguished matrix column omitted. -/
abbrev DifferenceDigitRowWithoutColumn
    (base degree ringRank levels : ℕ)
    (selected : DifferenceDigitColumn ringRank levels) :=
  {column : DifferenceDigitColumn ringRank levels // column ≠ selected} →
    Fin (degree + 1) → Fin base

/-- Contribution of all nonselected digit columns to one retained-error row. -/
def omittedDigitRowWeightedSum
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (omitted : DifferenceDigitRowWithoutColumn base degree ringRank levels selected) :
    RLWE.Rq q (degree + 1) :=
  ∑ column : {column : DifferenceDigitColumn ringRank levels // column ≠ selected},
    coefficientDigitPolynomial q (fun coefficient => omitted column coefficient) *
      signedValue candidate (sourceError (finProdFinEquiv column.1))

/-- Tensor-level spelling of the omitted-column contribution in one row. -/
def omittedDigitWeightedSum
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected)
    (row : Fin (TGSW.rowCount ringRank levels)) : RLWE.Rq q (degree + 1) :=
  omittedDigitRowWeightedSum candidate sourceError selected (omitted row)

/-- Splitting the completed row sum isolates the selected digit polynomial from the explicit sum
over all remaining columns. -/
theorem digitTensorRingDigits_completeDigitTensor_sum
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected)
    (selectedDigits :
      Fin (TGSW.rowCount ringRank levels) → Fin (degree + 1) → Fin base)
    (row : Fin (TGSW.rowCount ringRank levels)) :
    (∑ column : DifferenceDigitColumn ringRank levels,
        digitTensorRingDigits (q := q)
            (completeDigitTensor selected omitted selectedDigits)
            row column.1 column.2 *
          signedValue candidate (sourceError (finProdFinEquiv column))) =
      coefficientDigitPolynomial q (selectedDigits row) *
          signedValue candidate (sourceError (finProdFinEquiv selected)) +
        omittedDigitWeightedSum candidate sourceError selected omitted row := by
  rw [Fintype.sum_eq_add_sum_subtype_ne]
  apply congrArg₂ (· + ·)
  · rw [digitTensorRingDigits_completeDigitTensor_selected]
  · unfold omittedDigitWeightedSum
    apply Finset.sum_congr rfl
    intro column _
    rw [digitTensorRingDigits_completeDigitTensor_other]

/-- The candidate-dependent sign preserves the unit property. -/
theorem signedValue_isUnit_of_isUnit
    {R : Type} [CommRing R] (candidate : Bool) {value : R}
    (hunit : IsUnit value) : IsUnit (signedValue candidate value) := by
  cases candidate
  · simpa [signedValue] using hunit
  · simpa [signedValue] using hunit.neg

/-- Canonical unit witnessing the signed selected source-error entry. -/
noncomputable def selectedSignedSourceUnit
    {q degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    (RLWE.Rq q (degree + 1))ˣ :=
  (signedValue_isUnit_of_isUnit candidate hunit).unit

@[simp]
theorem selectedSignedSourceUnit_spec
    {q degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    (selectedSignedSourceUnit candidate sourceError selected hunit :
        RLWE.Rq q (degree + 1)) =
      signedValue candidate (sourceError (finProdFinEquiv selected)) := by
  exact (signedValue_isUnit_of_isUnit candidate hunit).unit_spec

/-- The unique ring polynomial forced into the selected digit column of one row by the
transformed error and the remaining digit columns in that row. -/
noncomputable def reconstructedSelectedDigitPolynomialRow
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (omitted : DifferenceDigitRowWithoutColumn base degree ringRank levels selected) :
    RLWE.Rq q (degree + 1) :=
  (transformedError row - sourceError row -
      omittedDigitRowWeightedSum candidate sourceError selected omitted) *
    (↑((selectedSignedSourceUnit candidate sourceError selected hunit)⁻¹) :
      RLWE.Rq q (degree + 1))

/-- Tensor-level spelling of the selected digit polynomial reconstructed in one row. -/
noncomputable def reconstructedSelectedDigitPolynomial
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected)
    (row : Fin (TGSW.rowCount ringRank levels)) : RLWE.Rq q (degree + 1) :=
  reconstructedSelectedDigitPolynomialRow candidate sourceError transformedError selected
    hunit row (omitted row)

/-- Multiplying the reconstructed selected polynomial by its unit coefficient recovers exactly
the row residual left after the omitted columns. -/
theorem reconstructedSelectedDigitPolynomial_mul_signedValue
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected)
    (row : Fin (TGSW.rowCount ringRank levels)) :
    reconstructedSelectedDigitPolynomial candidate sourceError transformedError selected hunit
        omitted row *
        signedValue candidate (sourceError (finProdFinEquiv selected)) =
      transformedError row - sourceError row -
        omittedDigitWeightedSum candidate sourceError selected omitted row := by
  unfold reconstructedSelectedDigitPolynomial reconstructedSelectedDigitPolynomialRow
    omittedDigitWeightedSum
  rw [← selectedSignedSourceUnit_spec candidate sourceError selected hunit]
  rw [mul_assoc, Units.inv_mul, mul_one]

/-- If the supplied selected digits cast to the forced polynomial in every row, completing the
tensor produces exactly the requested retained transformed error. -/
theorem digitTensorFixedErrorSide_completeDigitTensor_eq
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected)
    (selectedDigits :
      Fin (TGSW.rowCount ringRank levels) → Fin (degree + 1) → Fin base)
    (hselected : ∀ row,
      coefficientDigitPolynomial q (selectedDigits row) =
        reconstructedSelectedDigitPolynomial candidate sourceError transformedError selected
          hunit omitted row) :
    digitTensorFixedErrorSide candidate sourceError
        (completeDigitTensor selected omitted selectedDigits) =
      transformedError := by
  funext row
  unfold digitTensorFixedErrorSide rowOperator
  rw [digitTensorRingDigits_completeDigitTensor_sum,
    hselected row,
    reconstructedSelectedDigitPolynomial_mul_signedValue]
  ring

/-- Conversely, equality of the completed transformed error forces its selected digit polynomial
to be the explicit reconstructed value. -/
theorem coefficientDigitPolynomial_eq_reconstructed_of_complete_side_eq
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected)
    (selectedDigits :
      Fin (TGSW.rowCount ringRank levels) → Fin (degree + 1) → Fin base)
    (hside : digitTensorFixedErrorSide candidate sourceError
        (completeDigitTensor selected omitted selectedDigits) = transformedError)
    (row : Fin (TGSW.rowCount ringRank levels)) :
    coefficientDigitPolynomial q (selectedDigits row) =
      reconstructedSelectedDigitPolynomial candidate sourceError transformedError selected
        hunit omitted row := by
  have hrow := congrFun hside row
  unfold digitTensorFixedErrorSide rowOperator at hrow
  rw [digitTensorRingDigits_completeDigitTensor_sum] at hrow
  have hmul :
      coefficientDigitPolynomial q (selectedDigits row) *
          signedValue candidate (sourceError (finProdFinEquiv selected)) =
        reconstructedSelectedDigitPolynomial candidate sourceError transformedError selected
            hunit omitted row *
          signedValue candidate (sourceError (finProdFinEquiv selected)) := by
    rw [reconstructedSelectedDigitPolynomial_mul_signedValue]
    linear_combination hrow
  exact (signedValue_isUnit_of_isUnit candidate hunit).mul_left_inj.mp hmul

/-- One omitted-column row is valid exactly when its explicitly reconstructed selected ring
polynomial has a coefficient representation in the small digit alphabet. -/
def OmittedDigitRowCompletable
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (omitted : DifferenceDigitRowWithoutColumn base degree ringRank levels selected) : Prop :=
  ∃ selectedDigits : Fin (degree + 1) → Fin base,
    coefficientDigitPolynomial q selectedDigits =
      reconstructedSelectedDigitPolynomialRow candidate sourceError transformedError selected
        hunit row omitted

/-- An omitted-column tensor is valid exactly when every explicitly reconstructed selected ring
polynomial has a coefficient representation in the small digit alphabet.  The predicate is
definitionally row-local. -/
def OmittedDigitTensorCompletable
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected) : Prop :=
  ∀ row : Fin (TGSW.rowCount ringRank levels),
    OmittedDigitRowCompletable candidate sourceError transformedError selected hunit row
      (omitted row)

/-- Explicit finite carrier of valid remaining digit assignments in one row. -/
abbrev CompletableOmittedDigitRow
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels)) :=
  {omitted : DifferenceDigitRowWithoutColumn base degree ringRank levels selected //
    OmittedDigitRowCompletable candidate sourceError transformedError selected hunit row omitted}

noncomputable instance instFintypeCompletableOmittedDigitRow
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels)) :
    Fintype (CompletableOmittedDigitRow (base := base)
      candidate sourceError transformedError selected hunit row) :=
  Fintype.ofFinite _

/-- Explicit finite carrier of valid remaining digit assignments. -/
abbrev CompletableOmittedDigitTensor
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :=
  {omitted : DifferenceDigitTensorWithoutColumn base degree ringRank levels selected //
    OmittedDigitTensorCompletable candidate sourceError transformedError selected hunit omitted}

noncomputable instance instFintypeCompletableOmittedDigitTensor
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    Fintype (CompletableOmittedDigitTensor (base := base)
      candidate sourceError transformedError selected hunit) :=
  Fintype.ofFinite _

/-- The retained-fiber validity subtype is exactly a product of independent row-validity
subtypes.  In particular, conditioning on the complete transformed-error vector introduces no
cross-row constraint. -/
def completableOmittedDigitTensorEquivRows
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    CompletableOmittedDigitTensor (base := base)
        candidate sourceError transformedError selected hunit ≃
      (∀ row : Fin (TGSW.rowCount ringRank levels),
        CompletableOmittedDigitRow (base := base)
          candidate sourceError transformedError selected hunit row) where
  toFun omitted row := ⟨omitted.1 row, omitted.property row⟩
  invFun rows := ⟨fun row ↦ (rows row).1, fun row ↦ (rows row).property⟩
  left_inv omitted := by
    apply Subtype.ext
    rfl
  right_inv rows := by
    funext row
    apply Subtype.ext
    rfl

/-- Exact product formula for the number of valid remaining-digit assignments in a retained
fiber. -/
theorem card_completableOmittedDigitTensor_eq_prod_rows
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    Fintype.card
        (CompletableOmittedDigitTensor (base := base)
          candidate sourceError transformedError selected hunit) =
      ∏ row : Fin (TGSW.rowCount ringRank levels),
        Fintype.card
          (CompletableOmittedDigitRow (base := base)
            candidate sourceError transformedError selected hunit row) := by
  rw [Fintype.card_congr
    (completableOmittedDigitTensorEquivRows (base := base) candidate sourceError
      transformedError selected hunit), Fintype.card_pi]

/-! ## Row-local ring matrices -/

/-- Ring digit in one reconstructed valid row.  The selected column is the forced polynomial;
all other columns are the explicit small digit polynomials. -/
noncomputable def reconstructedRowRingDigit
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (omitted : CompletableOmittedDigitRow (base := base)
      candidate sourceError transformedError selected hunit row)
    (column : DifferenceDigitColumn ringRank levels) : RLWE.Rq q (degree + 1) :=
  if hcolumn : column = selected then
    reconstructedSelectedDigitPolynomialRow candidate sourceError transformedError selected
      hunit row omitted.1
  else
    coefficientDigitPolynomial q (fun coefficient =>
      omitted.1 ⟨column, hcolumn⟩ coefficient)

@[simp]
theorem reconstructedRowRingDigit_selected
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (omitted : CompletableOmittedDigitRow (base := base)
      candidate sourceError transformedError selected hunit row) :
    reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
        omitted selected =
      reconstructedSelectedDigitPolynomialRow candidate sourceError transformedError selected
        hunit row omitted.1 := by
  simp [reconstructedRowRingDigit]

@[simp]
theorem reconstructedRowRingDigit_other
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (omitted : CompletableOmittedDigitRow (base := base)
      candidate sourceError transformedError selected hunit row)
    (column : DifferenceDigitColumn ringRank levels) (hcolumn : column ≠ selected) :
    reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
        omitted column =
      coefficientDigitPolynomial q (fun coefficient =>
        omitted.1 ⟨column, hcolumn⟩ coefficient) := by
  simp [reconstructedRowRingDigit, hcolumn]

/-- One component of the row operator assembled from a valid reconstructed digit row. -/
noncomputable def reconstructedRowOperatorEntry
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (omitted : CompletableOmittedDigitRow (base := base)
      candidate sourceError transformedError selected hunit row)
    (value : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1)) :
    RLWE.Rq q (degree + 1) :=
  value row +
    ∑ column : DifferenceDigitColumn ringRank levels,
      reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
          omitted column *
        signedValue candidate (value (finProdFinEquiv column))

/-- Local acceptance predicate whose simultaneous row-choice counts control the exact kernel
moments. -/
def ReconstructedRowAccepts
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (omitted : CompletableOmittedDigitRow (base := base)
      candidate sourceError transformedError selected hunit row)
    (value : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1)) : Prop :=
  reconstructedRowOperatorEntry candidate sourceError transformedError selected hunit row
    omitted value = 0

/-- Choose the unique small digit vector representing one reconstructed selected polynomial. -/
noncomputable def reconstructedSelectedDigits
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : CompletableOmittedDigitTensor (base := base)
      candidate sourceError transformedError
      selected hunit)
    (row : Fin (TGSW.rowCount ringRank levels)) : Fin (degree + 1) → Fin base :=
  Classical.choose (omitted.property row)

theorem coefficientDigitPolynomial_reconstructedSelectedDigits
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : CompletableOmittedDigitTensor (base := base)
      candidate sourceError transformedError
      selected hunit)
    (row : Fin (TGSW.rowCount ringRank levels)) :
    coefficientDigitPolynomial q
        (reconstructedSelectedDigits candidate sourceError transformedError selected hunit
          omitted row) =
      reconstructedSelectedDigitPolynomial candidate sourceError transformedError selected
        hunit omitted.1 row := by
  exact Classical.choose_spec (omitted.property row)

/-- Complete a valid omitted tensor using its explicitly reconstructed selected digits. -/
noncomputable def reconstructedCompleteDigitTensor
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : CompletableOmittedDigitTensor (base := base)
      candidate sourceError transformedError
      selected hunit) : DifferenceDigitTensor base degree ringRank levels :=
  completeDigitTensor selected omitted.1
    (reconstructedSelectedDigits candidate sourceError transformedError selected hunit omitted)

theorem reconstructedCompleteDigitTensor_side
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : CompletableOmittedDigitTensor (base := base)
      candidate sourceError transformedError
      selected hunit) :
    digitTensorFixedErrorSide candidate sourceError
        (reconstructedCompleteDigitTensor candidate sourceError transformedError selected hunit
          omitted) =
      transformedError := by
  apply digitTensorFixedErrorSide_completeDigitTensor_eq
  intro row
  exact coefficientDigitPolynomial_reconstructedSelectedDigits candidate sourceError
    transformedError selected hunit omitted row

@[simp]
theorem digitTensorWithoutColumn_reconstructedCompleteDigitTensor
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : CompletableOmittedDigitTensor (base := base)
      candidate sourceError transformedError
      selected hunit) :
    digitTensorWithoutColumn selected
        (reconstructedCompleteDigitTensor candidate sourceError transformedError selected hunit
          omitted) =
      omitted.1 := by
  exact digitTensorWithoutColumn_completeDigitTensor selected omitted.1 _

/-- Every ring digit of the reconstructed tensor is computed by the corresponding row-local
reconstruction. -/
theorem digitTensorRingDigits_reconstructedCompleteDigitTensor_row
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : CompletableOmittedDigitTensor (base := base)
      candidate sourceError transformedError selected hunit)
    (row : Fin (TGSW.rowCount ringRank levels))
    (column : DifferenceDigitColumn ringRank levels) :
    digitTensorRingDigits (q := q)
        (reconstructedCompleteDigitTensor candidate sourceError transformedError selected hunit
          omitted) row column.1 column.2 =
      reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
        ⟨omitted.1 row, omitted.property row⟩ column := by
  unfold reconstructedCompleteDigitTensor
  by_cases hcolumn : column = selected
  · subst column
    rw [digitTensorRingDigits_completeDigitTensor_selected,
      coefficientDigitPolynomial_reconstructedSelectedDigits]
    simp [reconstructedRowRingDigit, reconstructedSelectedDigitPolynomial]
  · rw [digitTensorRingDigits_completeDigitTensor_other
      selected omitted.1 _ row column hcolumn]
    simp [reconstructedRowRingDigit, hcolumn]

/-- Exact equivalence between one finite digit retained fiber and the explicit validity subtype
on its remaining digit columns. -/
noncomputable def digitTensorFixedErrorFiberEquivCompletableOmitted
    {q base degree ringRank levels : ℕ} [NeZero q]
    (hbase : base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    DigitTensorFixedErrorFiber (base := base) candidate sourceError transformedError ≃
      CompletableOmittedDigitTensor (base := base)
        candidate sourceError transformedError selected hunit where
  toFun digits := by
    refine ⟨digitTensorWithoutColumn selected digits.1, ?_⟩
    let allSelectedDigits :
        Fin (TGSW.rowCount ringRank levels) → Fin (degree + 1) → Fin base :=
      fun row coefficient => digits.1 row selected.1 coefficient selected.2
    intro row
    refine ⟨allSelectedDigits row, ?_⟩
    apply coefficientDigitPolynomial_eq_reconstructed_of_complete_side_eq
      (selectedDigits := allSelectedDigits)
    simpa only [allSelectedDigits,
      completeDigitTensor_digitTensorWithoutColumn selected digits.1] using digits.property
  invFun omitted :=
    ⟨reconstructedCompleteDigitTensor candidate sourceError transformedError selected hunit
        omitted,
      reconstructedCompleteDigitTensor_side candidate sourceError transformedError selected hunit
        omitted⟩
  left_inv := by
    intro digits
    apply digitTensorFixedErrorFiberProjection_injective hbase candidate sourceError
      transformedError selected hunit
    exact digitTensorWithoutColumn_reconstructedCompleteDigitTensor candidate sourceError
      transformedError selected hunit _
  right_inv := by
    intro omitted
    apply Subtype.ext
    exact digitTensorWithoutColumn_reconstructedCompleteDigitTensor candidate sourceError
      transformedError selected hunit omitted

/-! ## Exact native transfer to the explicit validity subtype -/

/-- At exact capacity, the native retained-error fiber is equivalent to its finite
coefficient-digit retained-error fiber. -/
noncomputable def fixedErrorDifferenceFiberEquivDigitTensor
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    FixedErrorDifferenceFiber params candidate sourceError transformedError ≃
      DigitTensorFixedErrorFiber (base := params.base)
        candidate sourceError transformedError where
  toFun difference :=
    ⟨differenceDigitCoefficientVector params difference.1, by
      rw [digitTensorFixedErrorSide_differenceDigitCoefficientVector]
      exact difference.property⟩
  invFun digits :=
    ⟨(differenceDigitCoefficientEquiv
        (degree := degree) (ringRank := ringRank) params hcapacity).symm digits.1, by
      rw [← digitTensorFixedErrorSide_differenceDigitCoefficientVector]
      rw [← differenceDigitCoefficientEquiv_apply params hcapacity,
        (differenceDigitCoefficientEquiv
          (degree := degree) (ringRank := ringRank) params hcapacity).apply_symm_apply]
      exact digits.property⟩
  left_inv := by
    intro difference
    apply Subtype.ext
    exact (differenceDigitCoefficientEquiv
      (degree := degree) (ringRank := ringRank) params hcapacity).symm_apply_apply difference.1
  right_inv := by
    intro digits
    apply Subtype.ext
    change differenceDigitCoefficientVector params
      ((differenceDigitCoefficientEquiv
        (degree := degree) (ringRank := ringRank) params hcapacity).symm digits.1) = digits.1
    rw [← differenceDigitCoefficientEquiv_apply params hcapacity]
    exact (differenceDigitCoefficientEquiv
      (degree := degree) (ringRank := ringRank) params hcapacity).apply_symm_apply digits.1

/-- The native retained fiber is exactly the explicit subtype of remaining digit assignments
whose forced selected polynomial has small base digits. -/
noncomputable def fixedErrorDifferenceFiberEquivCompletableOmitted
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    FixedErrorDifferenceFiber params candidate sourceError transformedError ≃
      CompletableOmittedDigitTensor (base := params.base)
        candidate sourceError transformedError selected hunit :=
  (fixedErrorDifferenceFiberEquivDigitTensor params hcapacity candidate sourceError
    transformedError).trans
      (digitTensorFixedErrorFiberEquivCompletableOmitted hbase candidate sourceError
        transformedError selected hunit)

/-- Reconstruct the unique native difference ciphertext directly from a valid assignment of the
remaining coefficient-digit columns. -/
noncomputable def reconstructFixedErrorDifferenceFromCompletable
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : CompletableOmittedDigitTensor (base := params.base)
      candidate sourceError transformedError selected hunit) :
    RingGSWCiphertext q (degree + 1) ringRank params.levels :=
  ((fixedErrorDifferenceFiberEquivCompletableOmitted params hcapacity hbase candidate
    sourceError transformedError selected hunit).symm omitted).1

/-- Reconstructing the native difference and decomposing it again returns the complete
reconstructed coefficient-digit tensor. -/
theorem differenceDigitCoefficientVector_reconstructFixedErrorDifferenceFromCompletable
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : CompletableOmittedDigitTensor (base := params.base)
      candidate sourceError transformedError selected hunit) :
    differenceDigitCoefficientVector params
        (reconstructFixedErrorDifferenceFromCompletable params hcapacity hbase candidate
          sourceError transformedError selected hunit omitted) =
      reconstructedCompleteDigitTensor candidate sourceError transformedError selected hunit
        omitted := by
  simp only [reconstructFixedErrorDifferenceFromCompletable,
    fixedErrorDifferenceFiberEquivCompletableOmitted,
    fixedErrorDifferenceFiberEquivDigitTensor,
    digitTensorFixedErrorFiberEquivCompletableOmitted]
  rw [← differenceDigitCoefficientEquiv_apply params hcapacity]
  exact (differenceDigitCoefficientEquiv
    (degree := degree) (ringRank := ringRank) params hcapacity).apply_symm_apply _

theorem reconstructFixedErrorDifferenceFromCompletable_side
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : CompletableOmittedDigitTensor (base := params.base)
      candidate sourceError transformedError selected hunit) :
    fixedErrorDifferenceSide params candidate sourceError
        (reconstructFixedErrorDifferenceFromCompletable params hcapacity hbase candidate
          sourceError transformedError selected hunit omitted) =
      transformedError := by
  exact ((fixedErrorDifferenceFiberEquivCompletableOmitted params hcapacity hbase candidate
    sourceError transformedError selected hunit).symm omitted).property

/-- Reconstruct a native retained-fiber difference from its independent family of valid row
choices. -/
noncomputable def reconstructFixedErrorDifferenceFromRows
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (rows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
      CompletableOmittedDigitRow (base := params.base)
        candidate sourceError transformedError selected hunit row) :
    RingGSWCiphertext q (degree + 1) ringRank params.levels :=
  reconstructFixedErrorDifferenceFromCompletable params hcapacity hbase candidate
    sourceError transformedError selected hunit
      ((completableOmittedDigitTensorEquivRows (base := params.base) candidate sourceError
        transformedError selected hunit).symm rows)

theorem reconstructFixedErrorDifferenceFromRows_side
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (rows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
      CompletableOmittedDigitRow (base := params.base)
        candidate sourceError transformedError selected hunit row) :
    fixedErrorDifferenceSide params candidate sourceError
        (reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate sourceError
          transformedError selected hunit rows) =
      transformedError := by
  exact reconstructFixedErrorDifferenceFromCompletable_side params hcapacity hbase candidate
    sourceError transformedError selected hunit _

/-- The native ring digits reconstructed from a row family are exactly its row-local ring
digits. -/
theorem differenceEntryDigits_reconstructFixedErrorDifferenceFromRows
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (rows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
      CompletableOmittedDigitRow (base := params.base)
        candidate sourceError transformedError selected hunit row)
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (column : DifferenceDigitColumn ringRank params.levels) :
    differenceEntryDigits params
        (reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate sourceError
          transformedError selected hunit rows) row column.1 column.2 =
      reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
        (rows row) column := by
  rw [← digitTensorRingDigits_differenceDigitCoefficientVector params]
  unfold reconstructFixedErrorDifferenceFromRows
  rw [differenceDigitCoefficientVector_reconstructFixedErrorDifferenceFromCompletable]
  simpa [completableOmittedDigitTensorEquivRows] using
    (digitTensorRingDigits_reconstructedCompleteDigitTensor_row candidate sourceError
      transformedError selected hunit
      ((completableOmittedDigitTensorEquivRows (base := params.base) candidate sourceError
        transformedError selected hunit).symm rows) row column)

/-- The native row-kernel cardinality is exactly the generic constrained-fiber cardinality of
the independent valid reconstructed rows. -/
theorem differenceRowKernelCard_reconstructFixedErrorDifferenceFromRows
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (rows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
      CompletableOmittedDigitRow (base := params.base)
        candidate sourceError transformedError selected hunit row) :
    differenceRowKernelCard params candidate
        (reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate sourceError
          transformedError selected hunit rows) =
      FormalProof4FHE.FiniteRowKernelMoment.constrainedFiberCard
        (fun row : Fin (TGSW.rowCount ringRank params.levels) =>
          CompletableOmittedDigitRow (base := params.base)
            candidate sourceError transformedError selected hunit row)
        (ReconstructedRowAccepts candidate sourceError transformedError selected hunit)
        rows := by
  classical
  unfold differenceRowKernelCard
    FormalProof4FHE.FiniteRowKernelMoment.constrainedFiberCard
  let equivalence :
      {value : Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1) //
        rowOperator candidate
            (differenceEntryDigits params
              (reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate
                sourceError transformedError selected hunit rows)) value = 0} ≃
      {value : Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1) //
        ∀ row, ReconstructedRowAccepts candidate sourceError transformedError selected hunit
          row (rows row) value} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun value => by
      constructor
      · intro hvalue row
        have hrow := congrFun hvalue row
        unfold rowOperator at hrow
        unfold ReconstructedRowAccepts reconstructedRowOperatorEntry
        simpa only [Pi.zero_apply, Equiv.refl_apply,
          differenceEntryDigits_reconstructFixedErrorDifferenceFromRows] using hrow
      · intro hvalue
        funext row
        have hrow := hvalue row
        unfold ReconstructedRowAccepts reconstructedRowOperatorEntry at hrow
        unfold rowOperator
        simpa only [Pi.zero_apply, Equiv.refl_apply,
          differenceEntryDigits_reconstructFixedErrorDifferenceFromRows] using hrow)
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  exact Nat.card_congr equivalence

/-- Number of valid reconstructed choices for one matrix row that annihilate an entire finite
tuple of proposed kernel vectors. -/
noncomputable def reconstructedSimultaneousRowChoiceCard
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (moment : ℕ) (row : Fin (TGSW.rowCount ringRank params.levels))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) : ℕ :=
  FormalProof4FHE.FiniteRowKernelMoment.simultaneousRowChoiceCard
    (fun row : Fin (TGSW.rowCount ringRank params.levels) =>
      CompletableOmittedDigitRow (base := params.base)
        candidate sourceError transformedError selected hunit row)
    (ReconstructedRowAccepts candidate sourceError transformedError selected hunit)
    moment row values

@[simp]
theorem reconstructedSimultaneousRowChoiceCard_zero
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (moment : ℕ) (row : Fin (TGSW.rowCount ringRank params.levels)) :
    reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
        selected hunit moment row 0 =
      Fintype.card
        (CompletableOmittedDigitRow (base := params.base)
          candidate sourceError transformedError selected hunit row) := by
  classical
  unfold reconstructedSimultaneousRowChoiceCard
    FormalProof4FHE.FiniteRowKernelMoment.simultaneousRowChoiceCard
  simp [ReconstructedRowAccepts, reconstructedRowOperatorEntry, signedValue]

/-- **Exact TFHE row-kernel moment normal form.**  Summing the `ringRank`-th power of the native
kernel cardinality over the complete conditioned retained fiber is exactly a sum over
`ringRank` proposed kernel vectors of a product of simultaneous one-row acceptance counts. -/
theorem sum_differenceRowKernelCard_reconstructFromRows_pow_eq_simultaneousRowProduct
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    (∑ rows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
        CompletableOmittedDigitRow (base := params.base)
          candidate sourceError transformedError selected hunit row,
      differenceRowKernelCard params candidate
          (reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate sourceError
            transformedError selected hunit rows) ^ ringRank) =
      ∑ values : Fin ringRank →
          (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
        ∏ row : Fin (TGSW.rowCount ringRank params.levels),
          reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
            selected hunit ringRank row values := by
  simpa only [differenceRowKernelCard_reconstructFixedErrorDifferenceFromRows,
    reconstructedSimultaneousRowChoiceCard] using
    (FormalProof4FHE.FiniteRowKernelMoment.sum_constrainedFiberCard_pow_eq_sum_prod_simultaneousRowChoiceCard
        (fun row : Fin (TGSW.rowCount ringRank params.levels) =>
          CompletableOmittedDigitRow (base := params.base)
            candidate sourceError transformedError selected hunit row)
        (ReconstructedRowAccepts candidate sourceError transformedError selected hunit)
        ringRank)

/-- Exact retained-fiber cardinality in the explicit remaining-digit normal form. -/
theorem fixedErrorDifferenceFiberCard_eq_card_completableOmitted
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDifferenceFiberCard params candidate sourceError transformedError =
      Fintype.card
        (CompletableOmittedDigitTensor (base := params.base)
          candidate sourceError transformedError selected hunit) := by
  unfold fixedErrorDifferenceFiberCard FormalProof4FHE.ConditionalCollision.sideFiberCard
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr
    (fixedErrorDifferenceFiberEquivCompletableOmitted params hcapacity hbase candidate
      sourceError transformedError selected hunit)

/-- Exact product formula for the native retained-fiber cardinality. -/
theorem fixedErrorDifferenceFiberCard_eq_prod_completableRows
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDifferenceFiberCard params candidate sourceError transformedError =
      ∏ row : Fin (TGSW.rowCount ringRank params.levels),
        Fintype.card
          (CompletableOmittedDigitRow (base := params.base)
            candidate sourceError transformedError selected hunit row) := by
  rw [fixedErrorDifferenceFiberCard_eq_card_completableOmitted params hcapacity hbase
    candidate sourceError transformedError selected hunit]
  exact card_completableOmittedDigitTensor_eq_prod_rows candidate sourceError transformedError
    selected hunit

/-- Valid omitted-column tensors: precisely the range of the native retained-fiber projection. -/
abbrev FixedErrorDifferenceOmittedRange
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels) :=
  Set.range
    (fixedErrorDifferenceFiberProjection params candidate sourceError
      transformedError selected)

/-- At exact capacity, a unit selected source-error entry identifies the native retained fiber
exactly with the valid omitted-column tensors. -/
noncomputable def fixedErrorDifferenceFiberEquivOmittedRange
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    FixedErrorDifferenceFiber params candidate sourceError transformedError ≃
      FixedErrorDifferenceOmittedRange params candidate sourceError
        transformedError selected :=
  Equiv.ofInjective
    (fixedErrorDifferenceFiberProjection params candidate sourceError
      transformedError selected)
    (fixedErrorDifferenceFiberProjection_injective params hcapacity hbase candidate
      sourceError transformedError selected hunit)

/-- Reconstruct the unique native difference ciphertext represented by a valid omitted-column
tensor. -/
noncomputable def reconstructFixedErrorDifference
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : FixedErrorDifferenceOmittedRange params candidate sourceError
      transformedError selected) :
    RingGSWCiphertext q (degree + 1) ringRank params.levels :=
  ((fixedErrorDifferenceFiberEquivOmittedRange params hcapacity hbase candidate
    sourceError transformedError selected hunit).symm omitted).1

/-- Reconstruction stays in the requested retained transformed-error fiber. -/
theorem reconstructFixedErrorDifference_side
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : FixedErrorDifferenceOmittedRange params candidate sourceError
      transformedError selected) :
    fixedErrorDifferenceSide params candidate sourceError
        (reconstructFixedErrorDifference params hcapacity hbase candidate sourceError
          transformedError selected hunit omitted) =
      transformedError := by
  exact ((fixedErrorDifferenceFiberEquivOmittedRange params hcapacity hbase candidate
    sourceError transformedError selected hunit).symm omitted).property

/-- Reconstructing and projecting returns the original valid omitted-column tensor. -/
theorem fixedErrorDifferenceFiberProjection_reconstruct
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (omitted : FixedErrorDifferenceOmittedRange params candidate sourceError
      transformedError selected) :
    fixedErrorDifferenceFiberProjection params candidate sourceError transformedError selected
        ⟨reconstructFixedErrorDifference params hcapacity hbase candidate sourceError
            transformedError selected hunit omitted,
          reconstructFixedErrorDifference_side params hcapacity hbase candidate sourceError
            transformedError selected hunit omitted⟩ =
      omitted.1 := by
  exact Equiv.apply_ofInjective_symm
    (fixedErrorDifferenceFiberProjection_injective params hcapacity hbase candidate
      sourceError transformedError selected hunit) omitted

/-- Reindex an indicator sum by the corresponding finite predicate subtype. -/
private theorem sum_ite_eq_sum_subtype
    {Input Value : Type} [Fintype Input] [AddCommMonoid Value]
    (predicate : Input → Prop) [DecidablePred predicate]
    (weight : Input → Value) :
    (∑ input : Input, if predicate input then weight input else 0) =
      ∑ input : {input : Input // predicate input}, weight input.1 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter predicate) (by simp) weight

/-- An indicator sum over all native differences is exactly the corresponding sum over the
retained-fiber subtype. -/
theorem fixedErrorDifferenceKernelSum_eq_fiberSum
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    (∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
        if fixedErrorDifferenceSide params candidate sourceError difference =
            transformedError then
          differenceSelfKernelFactor params candidate difference
        else 0) =
      ∑ difference : FixedErrorDifferenceFiber params candidate sourceError transformedError,
        differenceSelfKernelFactor params candidate difference.1 := by
  classical
  exact sum_ite_eq_sum_subtype
    (fun difference : RingGSWCiphertext q (degree + 1) ringRank params.levels =>
      fixedErrorDifferenceSide params candidate sourceError difference = transformedError)
    (differenceSelfKernelFactor params candidate)

/-- **Exact weighted unit-row normal form.**  The retained self-kernel sum is a sum over valid
assignments of the remaining `m - 1` coefficient-digit columns, with the selected column uniquely
reconstructed. -/
theorem fixedErrorDifferenceKernelSum_eq_omittedRangeSum
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    (∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
        if fixedErrorDifferenceSide params candidate sourceError difference =
            transformedError then
          differenceSelfKernelFactor params candidate difference
        else 0) =
      ∑ omitted : FixedErrorDifferenceOmittedRange params candidate sourceError
          transformedError selected,
        differenceSelfKernelFactor params candidate
          (reconstructFixedErrorDifference params hcapacity hbase candidate sourceError
            transformedError selected hunit omitted) := by
  rw [fixedErrorDifferenceKernelSum_eq_fiberSum]
  apply Fintype.sum_equiv
    (fixedErrorDifferenceFiberEquivOmittedRange params hcapacity hbase candidate
      sourceError transformedError selected hunit)
  intro difference
  simp [reconstructFixedErrorDifference]

/-- **Explicit weighted unit-row normal form.**  The retained self-kernel sum is indexed by all
remaining small digit assignments satisfying the concrete reconstructed-polynomial validity
predicate, with no opaque image subtype. -/
theorem fixedErrorDifferenceKernelSum_eq_completableOmittedSum
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    (∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
        if fixedErrorDifferenceSide params candidate sourceError difference =
            transformedError then
          differenceSelfKernelFactor params candidate difference
        else 0) =
      ∑ omitted : CompletableOmittedDigitTensor (base := params.base)
          candidate sourceError transformedError selected hunit,
        differenceSelfKernelFactor params candidate
          (reconstructFixedErrorDifferenceFromCompletable params hcapacity hbase candidate
            sourceError transformedError selected hunit omitted) := by
  rw [fixedErrorDifferenceKernelSum_eq_fiberSum]
  apply Fintype.sum_equiv
    (fixedErrorDifferenceFiberEquivCompletableOmitted params hcapacity hbase candidate
      sourceError transformedError selected hunit)
  intro difference
  simp [reconstructFixedErrorDifferenceFromCompletable]

/-- The retained self-kernel sum is indexed by the exact dependent product of independent valid
row choices. -/
theorem fixedErrorDifferenceKernelSum_eq_rowProductSum
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    (∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
        if fixedErrorDifferenceSide params candidate sourceError difference =
            transformedError then
          differenceSelfKernelFactor params candidate difference
        else 0) =
      ∑ rows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
          CompletableOmittedDigitRow (base := params.base)
            candidate sourceError transformedError selected hunit row,
        differenceSelfKernelFactor params candidate
          (reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate sourceError
            transformedError selected hunit rows) := by
  rw [fixedErrorDifferenceKernelSum_eq_completableOmittedSum params hcapacity hbase
    candidate sourceError transformedError selected hunit]
  apply Fintype.sum_equiv
    (completableOmittedDigitTensorEquivRows (base := params.base) candidate sourceError
      transformedError selected hunit)
  intro omitted
  rfl

/-- **Fully row-factorized self-kernel normal form.**  The exact native retained-fiber sum is the
simultaneous row-acceptance moment minus one baseline contribution for every valid row family. -/
theorem fixedErrorDifferenceKernelSum_eq_simultaneousRowMoment_sub_card
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    (∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
        if fixedErrorDifferenceSide params candidate sourceError difference =
            transformedError then
          differenceSelfKernelFactor params candidate difference
        else 0) =
      ((∑ values : Fin ringRank →
          (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
        ∏ row : Fin (TGSW.rowCount ringRank params.levels),
          reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
            selected hunit ringRank row values : ℕ) : ℝ) -
      ((∏ row : Fin (TGSW.rowCount ringRank params.levels),
          Fintype.card
            (CompletableOmittedDigitRow (base := params.base)
              candidate sourceError transformedError selected hunit row) : ℕ) : ℝ) := by
  rw [fixedErrorDifferenceKernelSum_eq_rowProductSum params hcapacity hbase candidate
    sourceError transformedError selected hunit]
  simp only [differenceSelfKernelFactor, Finset.sum_sub_distrib]
  simp only [← Nat.cast_pow]
  rw [← Nat.cast_sum]
  rw [sum_differenceRowKernelCard_reconstructFromRows_pow_eq_simultaneousRowProduct
    params hcapacity hbase candidate sourceError transformedError selected hunit]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_univ, Fintype.card_pi]

/-- Removing one summand from a finite real sum, written as an off-point indicator sum. -/
private theorem sum_sub_apply_eq_sum_ite_ne
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (weight : Index → ℝ) (distinguished : Index) :
    (∑ index, weight index) - weight distinguished =
      ∑ index, if index ≠ distinguished then weight index else 0 := by
  have hdecompose := Finset.sum_erase_add Finset.univ weight
    (Finset.mem_univ distinguished)
  calc
    (∑ index, weight index) - weight distinguished =
        ∑ index ∈ Finset.univ.erase distinguished, weight index := by
      rw [← hdecompose]
      abel
    _ = ∑ index, if index ≠ distinguished then weight index else 0 := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext index
        simp [eq_comm]
      · intros
        rfl

/-- **Off-zero self-kernel normal form.**  The zero tuple contributes exactly the baseline and
cancels.  Thus the complete retained self-collision excess is a manifestly nonnegative sum over
only nonzero tuples of proposed kernel vectors. -/
theorem fixedErrorDifferenceKernelSum_eq_nonzeroSimultaneousRowMoment
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    (∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
        if fixedErrorDifferenceSide params candidate sourceError difference =
            transformedError then
          differenceSelfKernelFactor params candidate difference
        else 0) =
      ∑ values : Fin ringRank →
          (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
        if values ≠ 0 then
          ∏ row : Fin (TGSW.rowCount ringRank params.levels),
            (reconstructedSimultaneousRowChoiceCard params candidate sourceError
              transformedError selected hunit ringRank row values : ℝ)
        else 0 := by
  rw [fixedErrorDifferenceKernelSum_eq_simultaneousRowMoment_sub_card params hcapacity
    hbase candidate sourceError transformedError selected hunit]
  push_cast
  simpa using
    (sum_sub_apply_eq_sum_ite_ne
      (fun values : Fin ringRank →
          (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)) =>
        ∏ row : Fin (TGSW.rowCount ringRank params.levels),
          (reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
            selected hunit ringRank row values : ℝ)) 0)

/-- The native distinct-pair cokernel sum is exactly a double sum over the retained-fiber
subtype; only unequal pairs contribute. -/
theorem fixedErrorDiagonalDistinctPairCokernelExcess_eq_fiberPairSum
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalDistinctPairCokernelExcess
        params candidate sourceError transformedError =
      ∑ leftDifference :
          FixedErrorDifferenceFiber params candidate sourceError transformedError,
        ∑ rightDifference :
            FixedErrorDifferenceFiber params candidate sourceError transformedError,
          if leftDifference.1 ≠ rightDifference.1 then
            (differencePairRowCokernelFactor params candidate
                leftDifference.1 rightDifference.1) ^ ringRank - 1
          else 0 := by
  classical
  unfold fixedErrorDiagonalDistinctPairCokernelExcess
  let retained := fun difference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels =>
    fixedErrorDifferenceSide params candidate sourceError difference = transformedError
  let weight := fun leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels =>
    if leftDifference ≠ rightDifference then
      (differencePairRowCokernelFactor params candidate
          leftDifference rightDifference) ^ ringRank - 1
    else 0
  calc
    (∑ leftDifference :
        RingGSWCiphertext q (degree + 1) ringRank params.levels,
      ∑ rightDifference :
          RingGSWCiphertext q (degree + 1) ringRank params.levels,
        if retained leftDifference ∧ retained rightDifference ∧
            leftDifference ≠ rightDifference then
          (differencePairRowCokernelFactor params candidate
              leftDifference rightDifference) ^ ringRank - 1
        else 0) =
        ∑ leftDifference :
            RingGSWCiphertext q (degree + 1) ringRank params.levels,
          if retained leftDifference then
            ∑ rightDifference :
                RingGSWCiphertext q (degree + 1) ringRank params.levels,
              if retained rightDifference then
                weight leftDifference rightDifference
              else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro leftDifference _
      by_cases hleft : retained leftDifference
      · simp only [hleft, true_and, if_true]
        apply Finset.sum_congr rfl
        intro rightDifference _
        by_cases hright : retained rightDifference <;>
          by_cases hne : leftDifference ≠ rightDifference <;>
          simp [hright, hne, weight]
      · simp [hleft]
    _ = ∑ leftDifference :
          {difference : RingGSWCiphertext q (degree + 1) ringRank params.levels //
            retained difference},
        ∑ rightDifference :
            RingGSWCiphertext q (degree + 1) ringRank params.levels,
          if retained rightDifference then
            weight leftDifference.1 rightDifference
          else 0 := by
      exact sum_ite_eq_sum_subtype retained
        (fun leftDifference =>
          ∑ rightDifference :
              RingGSWCiphertext q (degree + 1) ringRank params.levels,
            if retained rightDifference then
              weight leftDifference rightDifference
            else 0)
    _ = ∑ leftDifference :
          {difference : RingGSWCiphertext q (degree + 1) ringRank params.levels //
            retained difference},
        ∑ rightDifference :
            {difference : RingGSWCiphertext q (degree + 1) ringRank params.levels //
              retained difference},
          weight leftDifference.1 rightDifference.1 := by
      apply Finset.sum_congr rfl
      intro leftDifference _
      exact sum_ite_eq_sum_subtype retained (weight leftDifference.1)
    _ = ∑ leftDifference :
          FixedErrorDifferenceFiber params candidate sourceError transformedError,
        ∑ rightDifference :
            FixedErrorDifferenceFiber params candidate sourceError transformedError,
          if leftDifference.1 ≠ rightDifference.1 then
            (differencePairRowCokernelFactor params candidate
                leftDifference.1 rightDifference.1) ^ ringRank - 1
          else 0 := by
      rfl

/-- **Exact paired weighted unit-row normal form.**  The retained distinct-pair native cokernel
sum is a double sum over valid assignments of the remaining digit columns, with both selected
columns reconstructed uniquely. -/
theorem fixedErrorDiagonalDistinctPairCokernelExcess_eq_omittedRangePairSum
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDiagonalDistinctPairCokernelExcess
        params candidate sourceError transformedError =
      ∑ leftOmitted : FixedErrorDifferenceOmittedRange params candidate sourceError
          transformedError selected,
        ∑ rightOmitted : FixedErrorDifferenceOmittedRange params candidate sourceError
            transformedError selected,
          if reconstructFixedErrorDifference params hcapacity hbase candidate sourceError
              transformedError selected hunit leftOmitted ≠
            reconstructFixedErrorDifference params hcapacity hbase candidate sourceError
              transformedError selected hunit rightOmitted then
            (differencePairRowCokernelFactor params candidate
                (reconstructFixedErrorDifference params hcapacity hbase candidate sourceError
                  transformedError selected hunit leftOmitted)
                (reconstructFixedErrorDifference params hcapacity hbase candidate sourceError
                  transformedError selected hunit rightOmitted)) ^ ringRank - 1
          else 0 := by
  rw [fixedErrorDiagonalDistinctPairCokernelExcess_eq_fiberPairSum]
  let equivalence := fixedErrorDifferenceFiberEquivOmittedRange params hcapacity hbase
    candidate sourceError transformedError selected hunit
  apply Fintype.sum_equiv equivalence
  intro leftDifference
  apply Fintype.sum_equiv equivalence
  intro rightDifference
  simp [equivalence, reconstructFixedErrorDifference]

/-- **Explicit paired weighted unit-row normal form.**  The retained distinct-pair cokernel sum
is a double sum over the concrete reconstructed-polynomial validity subtype of the remaining
small digit assignments. -/
theorem fixedErrorDiagonalDistinctPairCokernelExcess_eq_completableOmittedPairSum
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDiagonalDistinctPairCokernelExcess
        params candidate sourceError transformedError =
      ∑ leftOmitted : CompletableOmittedDigitTensor (base := params.base)
          candidate sourceError transformedError selected hunit,
        ∑ rightOmitted : CompletableOmittedDigitTensor (base := params.base)
            candidate sourceError transformedError selected hunit,
          if reconstructFixedErrorDifferenceFromCompletable params hcapacity hbase candidate
              sourceError transformedError selected hunit leftOmitted ≠
            reconstructFixedErrorDifferenceFromCompletable params hcapacity hbase candidate
              sourceError transformedError selected hunit rightOmitted then
            (differencePairRowCokernelFactor params candidate
                (reconstructFixedErrorDifferenceFromCompletable params hcapacity hbase candidate
                  sourceError transformedError selected hunit leftOmitted)
                (reconstructFixedErrorDifferenceFromCompletable params hcapacity hbase candidate
                  sourceError transformedError selected hunit rightOmitted)) ^ ringRank - 1
          else 0 := by
  rw [fixedErrorDiagonalDistinctPairCokernelExcess_eq_fiberPairSum]
  let equivalence := fixedErrorDifferenceFiberEquivCompletableOmitted params hcapacity hbase
    candidate sourceError transformedError selected hunit
  apply Fintype.sum_equiv equivalence
  intro leftDifference
  apply Fintype.sum_equiv equivalence
  intro rightDifference
  simp [equivalence, reconstructFixedErrorDifferenceFromCompletable]

/-- The distinct-pair cokernel sum is an exact double sum over two independent products of
row-validity choices. -/
theorem fixedErrorDiagonalDistinctPairCokernelExcess_eq_rowProductPairSum
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDiagonalDistinctPairCokernelExcess
        params candidate sourceError transformedError =
      ∑ leftRows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
          CompletableOmittedDigitRow (base := params.base)
            candidate sourceError transformedError selected hunit row,
        ∑ rightRows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
            CompletableOmittedDigitRow (base := params.base)
              candidate sourceError transformedError selected hunit row,
          if reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate
                sourceError transformedError selected hunit leftRows ≠
              reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate
                sourceError transformedError selected hunit rightRows then
            (differencePairRowCokernelFactor params candidate
                (reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate
                  sourceError transformedError selected hunit leftRows)
                (reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate
                  sourceError transformedError selected hunit rightRows)) ^ ringRank - 1
          else 0 := by
  rw [fixedErrorDiagonalDistinctPairCokernelExcess_eq_completableOmittedPairSum
    params hcapacity hbase candidate sourceError transformedError selected hunit]
  let equivalence := completableOmittedDigitTensorEquivRows (base := params.base) candidate
    sourceError transformedError selected hunit
  apply Fintype.sum_equiv equivalence
  intro leftOmitted
  apply Fintype.sum_equiv equivalence
  intro rightOmitted
  rfl

/-! ## Exact certificate reformulation -/

/-- Self-kernel weight over the explicit valid remaining-digit assignments. -/
noncomputable def completableOmittedSelfKernelSum
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) : ℝ :=
  ∑ omitted : CompletableOmittedDigitTensor (base := params.base)
      candidate sourceError transformedError selected hunit,
    differenceSelfKernelFactor params candidate
      (reconstructFixedErrorDifferenceFromCompletable params hcapacity hbase candidate
        sourceError transformedError selected hunit omitted)

/-- Distinct-pair native cokernel weight over two valid remaining-digit assignments. -/
noncomputable def completableOmittedDistinctCokernelSum
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) : ℝ :=
  ∑ leftOmitted : CompletableOmittedDigitTensor (base := params.base)
      candidate sourceError transformedError selected hunit,
    ∑ rightOmitted : CompletableOmittedDigitTensor (base := params.base)
        candidate sourceError transformedError selected hunit,
      if reconstructFixedErrorDifferenceFromCompletable params hcapacity hbase candidate
          sourceError transformedError selected hunit leftOmitted ≠
        reconstructFixedErrorDifferenceFromCompletable params hcapacity hbase candidate
          sourceError transformedError selected hunit rightOmitted then
        (differencePairRowCokernelFactor params candidate
            (reconstructFixedErrorDifferenceFromCompletable params hcapacity hbase candidate
              sourceError transformedError selected hunit leftOmitted)
            (reconstructFixedErrorDifferenceFromCompletable params hcapacity hbase candidate
              sourceError transformedError selected hunit rightOmitted)) ^ ringRank - 1
      else 0

/-- Explicit remaining-digit form of the conditional self-kernel average certificate. -/
def CompletableOmittedKernelAverageBound
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (kernelAverageBound : ℝ) : Prop :=
  ∀ transformedError : DiagonalErrorVector q degree ringRank params.levels,
    completableOmittedSelfKernelSum params hcapacity hbase candidate sourceError
        transformedError selected hunit ≤
      (Fintype.card
          (CompletableOmittedDigitTensor (base := params.base)
            candidate sourceError transformedError selected hunit) : ℝ) *
        kernelAverageBound

/-- Explicit remaining-digit form of the conditional distinct-pair cokernel certificate. -/
def CompletableOmittedDistinctCokernelAverageBound
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (collisionAverageBound : ℝ) : Prop :=
  ∀ transformedError : DiagonalErrorVector q degree ringRank params.levels,
    completableOmittedDistinctCokernelSum params hcapacity hbase candidate sourceError
        transformedError selected hunit ≤
      (Fintype.card
          (CompletableOmittedDigitTensor (base := params.base)
            candidate sourceError transformedError selected hunit) : ℝ) *
        collisionAverageBound

/-- The old retained-fiber self certificate and the explicit reconstructed-digit certificate are
logically equivalent, not merely related by a relaxation. -/
theorem fixedErrorDifferenceFiberKernelAverageBound_iff_completableOmitted
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (kernelAverageBound : ℝ) :
    fixedErrorDifferenceFiberKernelAverageBound
        params candidate sourceError kernelAverageBound ↔
      CompletableOmittedKernelAverageBound params hcapacity hbase candidate sourceError
        selected hunit kernelAverageBound := by
  constructor
  · intro hbound transformedError
    unfold completableOmittedSelfKernelSum
    rw [← fixedErrorDifferenceKernelSum_eq_completableOmittedSum params hcapacity hbase
      candidate sourceError transformedError selected hunit]
    rw [← fixedErrorDifferenceFiberCard_eq_card_completableOmitted params hcapacity hbase
      candidate sourceError transformedError selected hunit]
    exact hbound transformedError
  · intro hbound transformedError
    rw [fixedErrorDifferenceKernelSum_eq_completableOmittedSum params hcapacity hbase
      candidate sourceError transformedError selected hunit]
    rw [fixedErrorDifferenceFiberCard_eq_card_completableOmitted params hcapacity hbase
      candidate sourceError transformedError selected hunit]
    exact hbound transformedError

/-- The old retained-fiber distinct cokernel certificate and the explicit paired
reconstructed-digit certificate are logically equivalent. -/
theorem fixedErrorDifferenceFiberDistinctCokernelAverageBound_iff_completableOmitted
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (collisionAverageBound : ℝ) :
    fixedErrorDifferenceFiberDistinctCokernelAverageBound
        params candidate sourceError collisionAverageBound ↔
      CompletableOmittedDistinctCokernelAverageBound params hcapacity hbase candidate
        sourceError selected hunit collisionAverageBound := by
  constructor
  · intro hbound transformedError
    unfold completableOmittedDistinctCokernelSum
    rw [← fixedErrorDiagonalDistinctPairCokernelExcess_eq_completableOmittedPairSum
      params hcapacity hbase candidate sourceError transformedError selected hunit]
    rw [← fixedErrorDifferenceFiberCard_eq_card_completableOmitted params hcapacity hbase
      candidate sourceError transformedError selected hunit]
    exact hbound transformedError
  · intro hbound transformedError
    rw [fixedErrorDiagonalDistinctPairCokernelExcess_eq_completableOmittedPairSum
      params hcapacity hbase candidate sourceError transformedError selected hunit]
    rw [fixedErrorDifferenceFiberCard_eq_card_completableOmitted params hcapacity hbase
      candidate sourceError transformedError selected hunit]
    exact hbound transformedError

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
