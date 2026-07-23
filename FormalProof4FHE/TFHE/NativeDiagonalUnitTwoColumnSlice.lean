/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDiagonalUnitRowWeightedNormalForm

/-!
# Two-Column Slices of Conditioned Native TFHE Rows

One unit source-error column reconstructs the selected digit polynomial from the retained-error
equation.  A proposed kernel vector supplies a second linear equation.  If the corresponding
`2 × 2` minor in the selected and one pivot column is a unit, the two equations jointly determine
both digit columns.  Hence accepting valid rows inject into the tensor with both columns omitted.

This is the algebraic rank event underlying a nontrivial simultaneous-row acceptance estimate.
It remains valid over the native coefficient ring and does not replace it by a residue field.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-! ## The retained equation and its second kernel equation -/

/-- Row-local form of the selected-column reconstruction identity. -/
theorem reconstructedSelectedDigitPolynomialRow_mul_signedValue
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (omitted : DifferenceDigitRowWithoutColumn base degree ringRank levels selected) :
    reconstructedSelectedDigitPolynomialRow candidate sourceError transformedError selected
        hunit row omitted *
        signedValue candidate (sourceError (finProdFinEquiv selected)) =
      transformedError row - sourceError row -
        omittedDigitRowWeightedSum candidate sourceError selected omitted := by
  unfold reconstructedSelectedDigitPolynomialRow
  rw [← selectedSignedSourceUnit_spec candidate sourceError selected hunit]
  rw [mul_assoc, Units.inv_mul, mul_one]

/-- Every reconstructed valid row satisfies its retained transformed-error equation exactly. -/
theorem reconstructedRowRingDigit_retainedEquation
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (omitted : CompletableOmittedDigitRow (base := base)
      candidate sourceError transformedError selected hunit row) :
    sourceError row +
        ∑ column : DifferenceDigitColumn ringRank levels,
          reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
              omitted column *
            signedValue candidate (sourceError (finProdFinEquiv column)) =
      transformedError row := by
  rw [Fintype.sum_eq_add_sum_subtype_ne]
  rw [reconstructedRowRingDigit_selected]
  have homitted :
      (∑ column : {column : DifferenceDigitColumn ringRank levels // column ≠ selected},
        reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
              omitted column.1 *
            signedValue candidate (sourceError (finProdFinEquiv column.1))) =
        omittedDigitRowWeightedSum candidate sourceError selected omitted.1 := by
    unfold omittedDigitRowWeightedSum
    apply Finset.sum_congr rfl
    intro column _
    rw [reconstructedRowRingDigit_other]
  rw [homitted, reconstructedSelectedDigitPolynomialRow_mul_signedValue]
  ring

/-- Applying any reconstructed row operator to the retained source-error row returns the fixed
transformed-error coordinate, independently of the valid omitted digits. -/
theorem reconstructedRowOperatorEntry_sourceError
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (omitted : CompletableOmittedDigitRow (base := base)
      candidate sourceError transformedError selected hunit row) :
    reconstructedRowOperatorEntry candidate sourceError transformedError selected hunit row
        omitted sourceError = transformedError row := by
  unfold reconstructedRowOperatorEntry
  exact reconstructedRowRingDigit_retainedEquation candidate sourceError transformedError
    selected hunit row omitted

/-- The native `2 × 2` minor formed by the retained source error and one proposed kernel
vector in the selected and pivot columns. -/
def retainedKernelColumnMinor
    {q degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError value :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected pivot : DifferenceDigitColumn ringRank levels) : RLWE.Rq q (degree + 1) :=
    signedValue candidate (sourceError (finProdFinEquiv selected)) *
      signedValue candidate (value (finProdFinEquiv pivot)) -
    signedValue candidate (sourceError (finProdFinEquiv pivot)) *
      signedValue candidate (value (finProdFinEquiv selected))

@[simp]
theorem retainedKernelColumnMinor_self
    {q degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError value :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels) :
    retainedKernelColumnMinor candidate sourceError value selected selected = 0 := by
  unfold retainedKernelColumnMinor
  ring

@[simp]
theorem retainedKernelColumnMinor_sourceError
    {q degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected pivot : DifferenceDigitColumn ringRank levels) :
    retainedKernelColumnMinor candidate sourceError sourceError selected pivot = 0 := by
  unfold retainedKernelColumnMinor
  ring

/-- Eliminating the reconstructed selected digit with the retained-error equation rewrites every
row-operator value as a fixed offset plus a sum weighted by the selected/column minors.  This is
the exact phase seen by the row-local Fourier coefficient: cancellation can only come from these
minors (the selected-column minor itself is zero). -/
theorem reconstructedRowOperatorEntry_eq_retainedOffset_add_minorSum
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
    reconstructedRowOperatorEntry candidate sourceError transformedError selected hunit row
        omitted value =
      value row +
        (transformedError row - sourceError row) *
          (↑((selectedSignedSourceUnit candidate sourceError selected hunit)⁻¹) :
            RLWE.Rq q (degree + 1)) *
          signedValue candidate (value (finProdFinEquiv selected)) +
        ∑ column : DifferenceDigitColumn ringRank levels,
          reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
              omitted column *
            (retainedKernelColumnMinor candidate sourceError value selected column *
              (↑((selectedSignedSourceUnit candidate sourceError selected hunit)⁻¹) :
                RLWE.Rq q (degree + 1))) := by
  classical
  let selectedInv : RLWE.Rq q (degree + 1) :=
    ↑((selectedSignedSourceUnit candidate sourceError selected hunit)⁻¹)
  let sourceValue := fun column : DifferenceDigitColumn ringRank levels =>
    signedValue candidate (sourceError (finProdFinEquiv column))
  let testValue := fun column : DifferenceDigitColumn ringRank levels =>
    signedValue candidate (value (finProdFinEquiv column))
  let digit := fun column : DifferenceDigitColumn ringRank levels =>
    reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
      omitted column
  have hinv : sourceValue selected * selectedInv = 1 := by
    dsimp only [sourceValue, selectedInv]
    rw [← selectedSignedSourceUnit_spec candidate sourceError selected hunit]
    simp
  have hcolumn (column : DifferenceDigitColumn ringRank levels) :
      testValue column =
        sourceValue column * selectedInv * testValue selected +
          retainedKernelColumnMinor candidate sourceError value selected column * selectedInv := by
    unfold retainedKernelColumnMinor
    dsimp only [sourceValue, testValue]
    calc
      signedValue candidate (value (finProdFinEquiv column)) =
          (signedValue candidate (sourceError (finProdFinEquiv selected)) * selectedInv) *
            signedValue candidate (value (finProdFinEquiv column)) := by
        rw [hinv, one_mul]
      _ =
          signedValue candidate (sourceError (finProdFinEquiv column)) * selectedInv *
              signedValue candidate (value (finProdFinEquiv selected)) +
            (signedValue candidate (sourceError (finProdFinEquiv selected)) *
                signedValue candidate (value (finProdFinEquiv column)) -
              signedValue candidate (sourceError (finProdFinEquiv column)) *
                signedValue candidate (value (finProdFinEquiv selected))) * selectedInv := by
        ring
  have hfactor :
      (∑ column : DifferenceDigitColumn ringRank levels,
          digit column * (sourceValue column * selectedInv * testValue selected)) =
        (∑ column : DifferenceDigitColumn ringRank levels,
            digit column * sourceValue column) * selectedInv * testValue selected := by
    calc
      (∑ column : DifferenceDigitColumn ringRank levels,
          digit column * (sourceValue column * selectedInv * testValue selected)) =
          ∑ column : DifferenceDigitColumn ringRank levels,
            (digit column * sourceValue column * selectedInv) * testValue selected := by
        apply Finset.sum_congr rfl
        intro column _
        ring
      _ = (∑ column : DifferenceDigitColumn ringRank levels,
          digit column * sourceValue column * selectedInv) * testValue selected := by
        rw [Finset.sum_mul]
      _ = (∑ column : DifferenceDigitColumn ringRank levels,
          digit column * sourceValue column) * selectedInv * testValue selected := by
        congr 1
        rw [Finset.sum_mul]
  have hsourceSum :
      (∑ column : DifferenceDigitColumn ringRank levels,
          digit column * sourceValue column) = transformedError row - sourceError row := by
    have hretained := reconstructedRowRingDigit_retainedEquation candidate sourceError
      transformedError selected hunit row omitted
    dsimp only [digit, sourceValue]
    linear_combination hretained
  unfold reconstructedRowOperatorEntry
  change value row + ∑ column, digit column * testValue column = _
  calc
    value row + ∑ column, digit column * testValue column =
        value row + ∑ column,
          digit column *
            (sourceValue column * selectedInv * testValue selected +
              retainedKernelColumnMinor candidate sourceError value selected column *
                selectedInv) := by
      apply congrArg (fun sum => value row + sum)
      apply Finset.sum_congr rfl
      intro column _
      rw [hcolumn]
    _ = value row +
          (∑ column, digit column * sourceValue column) * selectedInv * testValue selected +
          ∑ column, digit column *
            (retainedKernelColumnMinor candidate sourceError value selected column *
              selectedInv) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, hfactor]
      ring
    _ = value row +
          (transformedError row - sourceError row) * selectedInv * testValue selected +
          ∑ column, digit column *
            (retainedKernelColumnMinor candidate sourceError value selected column *
              selectedInv) := by
      rw [hsourceSum]
    _ = _ := rfl

/-- The explicit offset-plus-minors phase obtained after eliminating the selected digit. -/
noncomputable def reconstructedRowRetainedOffsetMinorPhase
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
    (transformedError row - sourceError row) *
      (↑((selectedSignedSourceUnit candidate sourceError selected hunit)⁻¹) :
        RLWE.Rq q (degree + 1)) *
      signedValue candidate (value (finProdFinEquiv selected)) +
    ∑ column : DifferenceDigitColumn ringRank levels,
      reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
          omitted column *
        (retainedKernelColumnMinor candidate sourceError value selected column *
          (↑((selectedSignedSourceUnit candidate sourceError selected hunit)⁻¹) :
            RLWE.Rq q (degree + 1)))

/-- The digit-independent part of the selected-column-eliminated row phase. -/
noncomputable def reconstructedRowRetainedOffset
    {q degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (value : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1)) :
    RLWE.Rq q (degree + 1) :=
  value row +
    (transformedError row - sourceError row) *
      (↑((selectedSignedSourceUnit candidate sourceError selected hunit)⁻¹) :
        RLWE.Rq q (degree + 1)) *
      signedValue candidate (value (finProdFinEquiv selected))

/-- The variable part of the selected-column-eliminated row phase.  Every digit occurs only
through a selected/column minor. -/
noncomputable def reconstructedRowMinorPhase
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
  ∑ column : DifferenceDigitColumn ringRank levels,
    reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
        omitted column *
      (retainedKernelColumnMinor candidate sourceError value selected column *
        (↑((selectedSignedSourceUnit candidate sourceError selected hunit)⁻¹) :
          RLWE.Rq q (degree + 1)))

/-- The zero selected minor drops out, leaving only explicit small digit polynomials in the
minor phase. -/
theorem reconstructedRowMinorPhase_eq_omittedSum
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
    reconstructedRowMinorPhase candidate sourceError transformedError selected hunit row
        omitted value =
      ∑ column : {column : DifferenceDigitColumn ringRank levels // column ≠ selected},
        coefficientDigitPolynomial q (fun coefficient => omitted.1 column coefficient) *
          (retainedKernelColumnMinor candidate sourceError value selected column.1 *
            (↑((selectedSignedSourceUnit candidate sourceError selected hunit)⁻¹) :
              RLWE.Rq q (degree + 1))) := by
  classical
  unfold reconstructedRowMinorPhase
  rw [Fintype.sum_eq_add_sum_subtype_ne _ selected]
  simp only [retainedKernelColumnMinor_self, zero_mul, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro column _
  rw [reconstructedRowRingDigit_other]

/-- The source-error test row is proportional to itself, so every minor-weighted variable phase
vanishes. -/
@[simp]
theorem reconstructedRowMinorPhase_sourceError
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (omitted : CompletableOmittedDigitRow (base := base)
      candidate sourceError transformedError selected hunit row) :
    reconstructedRowMinorPhase candidate sourceError transformedError selected hunit row
        omitted sourceError = 0 := by
  unfold reconstructedRowMinorPhase
  simp

@[simp]
theorem reconstructedRowRetainedOffsetMinorPhase_eq
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
    reconstructedRowRetainedOffsetMinorPhase candidate sourceError transformedError selected
        hunit row omitted value =
      reconstructedRowRetainedOffset candidate sourceError transformedError selected hunit row
          value +
        reconstructedRowMinorPhase candidate sourceError transformedError selected hunit row
          omitted value := rfl

theorem reconstructedRowOperatorEntry_eq_retainedOffsetMinorPhase
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
    reconstructedRowOperatorEntry candidate sourceError transformedError selected hunit row
        omitted value =
      reconstructedRowRetainedOffsetMinorPhase candidate sourceError transformedError selected
        hunit row omitted value := by
  rw [reconstructedRowOperatorEntry_eq_retainedOffset_add_minorSum]
  rfl

/-- Equality of all explicit omitted digits except one pivot column. -/
def EqualOffOmittedPivot
    {base degree ringRank levels : ℕ}
    (selected pivot : DifferenceDigitColumn ringRank levels)
    (left right : DifferenceDigitRowWithoutColumn base degree ringRank levels selected) : Prop :=
  ∀ column : {column : DifferenceDigitColumn ringRank levels // column ≠ selected},
    column.1 ≠ pivot → ∀ coefficient,
      left column coefficient = right column coefficient

/-- Separate two distinguished summands from a finite sum. -/
private theorem sum_eq_selected_add_pivot_add_rest
    {Index Value : Type} [Fintype Index] [DecidableEq Index] [AddCommMonoid Value]
    (selected pivot : Index) (hpivot : pivot ≠ selected) (term : Index → Value) :
    (∑ index, term index) =
      term selected + term pivot +
        ∑ index ∈ (Finset.univ.erase selected).erase pivot, term index := by
  have hpivotMem : pivot ∈ Finset.univ.erase selected := by simp [hpivot]
  calc
    (∑ index, term index) =
        (∑ index ∈ Finset.univ.erase selected, term index) + term selected :=
      (Finset.sum_erase_add Finset.univ term (Finset.mem_univ selected)).symm
    _ = ((∑ index ∈ (Finset.univ.erase selected).erase pivot, term index) +
          term pivot) + term selected := by
      rw [Finset.sum_erase_add (Finset.univ.erase selected) term hpivotMem]
    _ = term selected + term pivot +
        ∑ index ∈ (Finset.univ.erase selected).erase pivot, term index := by
      ac_rfl

/-! ## Unit-minor injectivity -/

/-- Two valid reconstructed rows that agree away from the pivot and annihilate the same vector
are equal whenever the selected/pivot retained-kernel minor is a unit. -/
theorem completableOmittedDigitRow_eq_of_equalOffPivot_of_accepts_of_isUnitMinor
    {q base degree ringRank levels : ℕ} [NeZero q]
    (hbase : base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected pivot : DifferenceDigitColumn ringRank levels)
    (hpivot : pivot ≠ selected)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (value : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (hminor : IsUnit (retainedKernelColumnMinor candidate sourceError value selected pivot))
    (left right : CompletableOmittedDigitRow (base := base)
      candidate sourceError transformedError selected hunit row)
    (hoff : EqualOffOmittedPivot selected pivot left.1 right.1)
    (hleft : ReconstructedRowAccepts candidate sourceError transformedError selected hunit row
      left value)
    (hright : ReconstructedRowAccepts candidate sourceError transformedError selected hunit row
      right value) :
    left = right := by
  classical
  let leftDigit := fun column : DifferenceDigitColumn ringRank levels =>
    reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
      left column
  let rightDigit := fun column : DifferenceDigitColumn ringRank levels =>
    reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
      right column
  let sourceValue := fun column : DifferenceDigitColumn ringRank levels =>
    signedValue candidate (sourceError (finProdFinEquiv column))
  let kernelValue := fun column : DifferenceDigitColumn ringRank levels =>
    signedValue candidate (value (finProdFinEquiv column))
  have hother (column : DifferenceDigitColumn ringRank levels)
      (hselected : column ≠ selected) (hpivotColumn : column ≠ pivot) :
      leftDigit column = rightDigit column := by
    unfold leftDigit rightDigit
    rw [reconstructedRowRingDigit_other candidate sourceError transformedError selected hunit row
      left column hselected]
    rw [reconstructedRowRingDigit_other candidate sourceError transformedError selected hunit row
      right column hselected]
    apply congrArg (coefficientDigitPolynomial q)
    funext coefficient
    exact hoff ⟨column, hselected⟩ hpivotColumn coefficient
  have hrest (coefficient : DifferenceDigitColumn ringRank levels → RLWE.Rq q (degree + 1)) :
      (∑ column ∈ (Finset.univ.erase selected).erase pivot,
          leftDigit column * coefficient column) =
        ∑ column ∈ (Finset.univ.erase selected).erase pivot,
          rightDigit column * coefficient column := by
    apply Finset.sum_congr rfl
    intro column hcolumn
    have hselected : column ≠ selected := by
      exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hcolumn)).1
    have hpivotColumn : column ≠ pivot := (Finset.mem_erase.mp hcolumn).1
    rw [hother column hselected hpivotColumn]
  have hsourceLeft := reconstructedRowRingDigit_retainedEquation candidate sourceError
    transformedError selected hunit row left
  have hsourceRight := reconstructedRowRingDigit_retainedEquation candidate sourceError
    transformedError selected hunit row right
  have hsourceSum :
      (∑ column, leftDigit column * sourceValue column) =
        ∑ column, rightDigit column * sourceValue column := by
    dsimp only [leftDigit, rightDigit, sourceValue]
    linear_combination hsourceLeft - hsourceRight
  have hkernelSum :
      (∑ column, leftDigit column * kernelValue column) =
        ∑ column, rightDigit column * kernelValue column := by
    unfold ReconstructedRowAccepts reconstructedRowOperatorEntry at hleft hright
    dsimp only [leftDigit, rightDigit, kernelValue]
    linear_combination hleft - hright
  rw [sum_eq_selected_add_pivot_add_rest selected pivot hpivot] at hsourceSum
  rw [sum_eq_selected_add_pivot_add_rest selected pivot hpivot
    (fun column => rightDigit column * sourceValue column)] at hsourceSum
  rw [sum_eq_selected_add_pivot_add_rest selected pivot hpivot] at hkernelSum
  rw [sum_eq_selected_add_pivot_add_rest selected pivot hpivot
    (fun column => rightDigit column * kernelValue column)] at hkernelSum
  rw [hrest sourceValue] at hsourceSum
  rw [hrest kernelValue] at hkernelSum
  have hsourceTwo :
      (leftDigit selected - rightDigit selected) * sourceValue selected +
          (leftDigit pivot - rightDigit pivot) * sourceValue pivot = 0 := by
    linear_combination hsourceSum
  have hkernelTwo :
      (leftDigit selected - rightDigit selected) * kernelValue selected +
          (leftDigit pivot - rightDigit pivot) * kernelValue pivot = 0 := by
    linear_combination hkernelSum
  have hselectedMinor :
      (leftDigit selected - rightDigit selected) *
          retainedKernelColumnMinor candidate sourceError value selected pivot = 0 := by
    unfold retainedKernelColumnMinor
    dsimp only [sourceValue, kernelValue] at hsourceTwo hkernelTwo ⊢
    linear_combination hsourceTwo *
        signedValue candidate (value (finProdFinEquiv pivot)) -
      hkernelTwo * signedValue candidate (sourceError (finProdFinEquiv pivot))
  have hpivotMinor :
      (leftDigit pivot - rightDigit pivot) *
          retainedKernelColumnMinor candidate sourceError value selected pivot = 0 := by
    unfold retainedKernelColumnMinor
    dsimp only [sourceValue, kernelValue] at hsourceTwo hkernelTwo ⊢
    linear_combination hkernelTwo *
        signedValue candidate (sourceError (finProdFinEquiv selected)) -
      hsourceTwo * signedValue candidate (value (finProdFinEquiv selected))
  have hselectedDigit : leftDigit selected = rightDigit selected := by
    rw [← sub_eq_zero]
    apply hminor.mul_left_inj.mp
    simpa using hselectedMinor
  have hpivotDigit : leftDigit pivot = rightDigit pivot := by
    rw [← sub_eq_zero]
    apply hminor.mul_left_inj.mp
    simpa using hpivotMinor
  have hpivotPolynomial :
      coefficientDigitPolynomial q (fun coefficient => left.1 ⟨pivot, hpivot⟩ coefficient) =
        coefficientDigitPolynomial q (fun coefficient => right.1 ⟨pivot, hpivot⟩ coefficient) := by
    simpa only [leftDigit, rightDigit,
      reconstructedRowRingDigit_other candidate sourceError transformedError selected hunit row
        left pivot hpivot,
      reconstructedRowRingDigit_other candidate sourceError transformedError selected hunit row
        right pivot hpivot] using hpivotDigit
  have hpivotDigits :
      (fun coefficient => left.1 ⟨pivot, hpivot⟩ coefficient) =
        fun coefficient => right.1 ⟨pivot, hpivot⟩ coefficient :=
    coefficientDigitPolynomial_injective hbase hpivotPolynomial
  apply Subtype.ext
  funext column coefficient
  by_cases hcolumn : column.1 = pivot
  · have hcolumnSubtype : column = ⟨pivot, hpivot⟩ := Subtype.ext hcolumn
    subst column
    exact congrFun hpivotDigits coefficient
  · exact hoff column hcolumn coefficient

/-! ## Finite two-column projection -/

/-- Exact cardinality of a coefficient-digit row with one column omitted. -/
theorem card_differenceDigitRowWithoutColumn
    {base degree ringRank levels : ℕ}
    (selected : DifferenceDigitColumn ringRank levels) :
    Fintype.card
        (DifferenceDigitRowWithoutColumn base degree ringRank levels selected) =
      base ^ ((TGSW.rowCount ringRank levels - 1) * (degree + 1)) := by
  change Fintype.card
      ({column : DifferenceDigitColumn ringRank levels // column ≠ selected} →
        Fin (degree + 1) → Fin base) = _
  rw [Fintype.card_fun, Fintype.card_fun, card_differenceDigitColumn_ne selected]
  simp only [Fintype.card_fin]
  rw [← pow_mul]
  congr 1
  ac_rfl

/-- The valid reconstructed rows form a subtype of the complete one-column-omitted digit row. -/
theorem card_completableOmittedDigitRow_le_pow
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels)) :
    Fintype.card
        (CompletableOmittedDigitRow (base := base)
          candidate sourceError transformedError selected hunit row) ≤
      base ^ ((TGSW.rowCount ringRank levels - 1) * (degree + 1)) := by
  calc
    Fintype.card
        (CompletableOmittedDigitRow (base := base)
          candidate sourceError transformedError selected hunit row) ≤
        Fintype.card
          (DifferenceDigitRowWithoutColumn base degree ringRank levels selected) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = base ^ ((TGSW.rowCount ringRank levels - 1) * (degree + 1)) :=
      card_differenceDigitRowWithoutColumn selected

/-- One coefficient-digit row with both the selected and pivot matrix columns omitted. -/
abbrev DifferenceDigitRowWithoutSelectedAndPivot
    (base degree ringRank levels : ℕ)
    (selected pivot : DifferenceDigitColumn ringRank levels) :=
  {column : DifferenceDigitColumn ringRank levels //
      column ≠ selected ∧ column ≠ pivot} →
    Fin (degree + 1) → Fin base

/-- Forget the pivot from a row that already omits the selected column. -/
def digitRowWithoutSelectedAndPivot
    {base degree ringRank levels : ℕ}
    (selected pivot : DifferenceDigitColumn ringRank levels)
    (omitted : DifferenceDigitRowWithoutColumn base degree ringRank levels selected) :
    DifferenceDigitRowWithoutSelectedAndPivot base degree ringRank levels selected pivot :=
  fun column coefficient => omitted ⟨column.1, column.property.1⟩ coefficient

/-- Omitting two distinct columns leaves exactly `rowCount - 2` matrix columns. -/
theorem card_differenceDigitColumn_ne_ne
    {ringRank levels : ℕ}
    (selected pivot : DifferenceDigitColumn ringRank levels)
    (hpivot : pivot ≠ selected) :
    Fintype.card
        {column : DifferenceDigitColumn ringRank levels //
          column ≠ selected ∧ column ≠ pivot} =
      TGSW.rowCount ringRank levels - 2 := by
  classical
  rw [Fintype.card_subtype]
  have hfilter :
      Finset.univ.filter (fun column : DifferenceDigitColumn ringRank levels =>
        column ≠ selected ∧ column ≠ pivot) =
        (Finset.univ.erase selected).erase pivot := by
    ext column
    simp [and_comm]
  rw [hfilter]
  rw [Finset.card_erase_of_mem (by simp [hpivot])]
  rw [Finset.card_erase_of_mem (by simp)]
  simp [DifferenceDigitColumn, TGSW.rowCount]
  omega

/-- Exact cardinality of the coefficient-digit row with two distinct columns omitted. -/
theorem card_differenceDigitRowWithoutSelectedAndPivot
    {base degree ringRank levels : ℕ}
    (selected pivot : DifferenceDigitColumn ringRank levels)
    (hpivot : pivot ≠ selected) :
    Fintype.card
        (DifferenceDigitRowWithoutSelectedAndPivot base degree ringRank levels
          selected pivot) =
      base ^ ((TGSW.rowCount ringRank levels - 2) * (degree + 1)) := by
  change Fintype.card
      ({column : DifferenceDigitColumn ringRank levels //
          column ≠ selected ∧ column ≠ pivot} →
        Fin (degree + 1) → Fin base) = _
  rw [Fintype.card_fun, Fintype.card_fun,
    card_differenceDigitColumn_ne_ne selected pivot hpivot]
  simp only [Fintype.card_fin]
  rw [← pow_mul]
  congr 1
  ac_rfl

/-- Valid reconstructed rows that annihilate one proposed kernel vector. -/
abbrev AcceptingCompletableOmittedDigitRow
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (value : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1)) :=
  {omitted : CompletableOmittedDigitRow (base := base)
      candidate sourceError transformedError selected hunit row //
    ReconstructedRowAccepts candidate sourceError transformedError selected hunit row
      omitted value}

noncomputable instance instFintypeAcceptingCompletableOmittedDigitRow
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (value : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1)) :
    Fintype (AcceptingCompletableOmittedDigitRow (base := base)
      candidate sourceError transformedError selected hunit row value) :=
  Fintype.ofFinite _

/-- Project an accepting valid row away from both distinguished columns. -/
def acceptingCompletableOmittedDigitRowProjection
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected pivot : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (value : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1)) :
    AcceptingCompletableOmittedDigitRow (base := base)
        candidate sourceError transformedError selected hunit row value →
      DifferenceDigitRowWithoutSelectedAndPivot base degree ringRank levels selected pivot :=
  fun omitted => digitRowWithoutSelectedAndPivot selected pivot omitted.1.1

/-- A unit selected/pivot minor makes the two-column projection injective on accepting valid
rows. -/
theorem acceptingCompletableOmittedDigitRowProjection_injective
    {q base degree ringRank levels : ℕ} [NeZero q]
    (hbase : base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected pivot : DifferenceDigitColumn ringRank levels)
    (hpivot : pivot ≠ selected)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (value : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (hminor : IsUnit (retainedKernelColumnMinor candidate sourceError value selected pivot)) :
    Function.Injective
      (acceptingCompletableOmittedDigitRowProjection (base := base) candidate sourceError
        transformedError selected pivot hunit row value) := by
  intro left right heq
  apply Subtype.ext
  apply completableOmittedDigitRow_eq_of_equalOffPivot_of_accepts_of_isUnitMinor hbase
    candidate sourceError transformedError selected pivot hpivot hunit row value hminor
  · intro column hpivotColumn coefficient
    let reduced : {column : DifferenceDigitColumn ringRank levels //
        column ≠ selected ∧ column ≠ pivot} :=
      ⟨column.1, column.property, hpivotColumn⟩
    exact congrFun (congrFun heq reduced) coefficient
  · exact left.property
  · exact right.property

/-- One unit minor removes a second complete digit-polynomial column from the accepting-row
count. -/
theorem card_acceptingCompletableOmittedDigitRow_le_pow_of_isUnitMinor
    {q base degree ringRank levels : ℕ} [NeZero q]
    (hbase : base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected pivot : DifferenceDigitColumn ringRank levels)
    (hpivot : pivot ≠ selected)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (value : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (hminor : IsUnit (retainedKernelColumnMinor candidate sourceError value selected pivot)) :
    Fintype.card
        (AcceptingCompletableOmittedDigitRow (base := base)
          candidate sourceError transformedError selected hunit row value) ≤
      base ^ ((TGSW.rowCount ringRank levels - 2) * (degree + 1)) := by
  calc
    Fintype.card
        (AcceptingCompletableOmittedDigitRow (base := base)
          candidate sourceError transformedError selected hunit row value) ≤
        Fintype.card
          (DifferenceDigitRowWithoutSelectedAndPivot base degree ringRank levels
            selected pivot) :=
      Fintype.card_le_of_injective
        (acceptingCompletableOmittedDigitRowProjection (base := base) candidate sourceError
          transformedError selected pivot hunit row value)
        (acceptingCompletableOmittedDigitRowProjection_injective hbase candidate sourceError
          transformedError selected pivot hpivot hunit row value hminor)
    _ = base ^ ((TGSW.rowCount ringRank levels - 2) * (degree + 1)) :=
      card_differenceDigitRowWithoutSelectedAndPivot selected pivot hpivot

/-- If any vector in a simultaneous tuple exposes a unit selected/pivot minor, the entire
simultaneous accepting-row count has the same two-column bound. -/
theorem reconstructedSimultaneousRowChoiceCard_le_pow_of_exists_isUnitMinor
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (moment : ℕ) (row : Fin (TGSW.rowCount ringRank params.levels))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)))
    (hexists : ∃ index : Fin moment, ∃ pivot : DifferenceDigitColumn ringRank params.levels,
      pivot ≠ selected ∧
        IsUnit (retainedKernelColumnMinor candidate sourceError (values index)
          selected pivot)) :
    reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
        selected hunit moment row values ≤
      params.base ^ ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1)) := by
  classical
  obtain ⟨index, pivot, hpivot, hminor⟩ := hexists
  unfold reconstructedSimultaneousRowChoiceCard
    FormalProof4FHE.FiniteRowKernelMoment.simultaneousRowChoiceCard
  let forget :
      {choice : CompletableOmittedDigitRow (base := params.base)
          candidate sourceError transformedError selected hunit row //
        ∀ tupleIndex, ReconstructedRowAccepts candidate sourceError transformedError selected
          hunit row choice (values tupleIndex)} →
        AcceptingCompletableOmittedDigitRow (base := params.base)
          candidate sourceError transformedError selected hunit row (values index) :=
    fun choice => ⟨choice.1, choice.property index⟩
  have hforget : Function.Injective forget := by
    intro left right heq
    apply Subtype.ext
    exact congrArg (fun accepted => accepted.1) heq
  calc
    Fintype.card
        {choice : CompletableOmittedDigitRow (base := params.base)
            candidate sourceError transformedError selected hunit row //
          ∀ tupleIndex, ReconstructedRowAccepts candidate sourceError transformedError selected
            hunit row choice (values tupleIndex)} ≤
        Fintype.card
          (AcceptingCompletableOmittedDigitRow (base := params.base)
            candidate sourceError transformedError selected hunit row (values index)) :=
      Fintype.card_le_of_injective forget hforget
    _ ≤ params.base ^ ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1)) :=
      card_acceptingCompletableOmittedDigitRow_le_pow_of_isUnitMinor hbase candidate
        sourceError transformedError selected pivot hpivot hunit row (values index) hminor

/-- Without a second unit minor, simultaneous acceptance is still bounded by the complete valid
one-column-omitted row space. -/
theorem reconstructedSimultaneousRowChoiceCard_le_pow
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (moment : ℕ) (row : Fin (TGSW.rowCount ringRank params.levels))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) :
    reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
        selected hunit moment row values ≤
      params.base ^ ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1)) := by
  classical
  unfold reconstructedSimultaneousRowChoiceCard
    FormalProof4FHE.FiniteRowKernelMoment.simultaneousRowChoiceCard
  let forget :
      {choice : CompletableOmittedDigitRow (base := params.base)
          candidate sourceError transformedError selected hunit row //
        ∀ tupleIndex, ReconstructedRowAccepts candidate sourceError transformedError selected
          hunit row choice (values tupleIndex)} →
        CompletableOmittedDigitRow (base := params.base)
          candidate sourceError transformedError selected hunit row :=
    fun choice => choice.1
  have hforget : Function.Injective forget := by
    intro left right heq
    exact Subtype.ext heq
  calc
    Fintype.card
        {choice : CompletableOmittedDigitRow (base := params.base)
            candidate sourceError transformedError selected hunit row //
          ∀ tupleIndex, ReconstructedRowAccepts candidate sourceError transformedError selected
            hunit row choice (values tupleIndex)} ≤
        Fintype.card
          (CompletableOmittedDigitRow (base := params.base)
            candidate sourceError transformedError selected hunit row) :=
      Fintype.card_le_of_injective forget hforget
    _ ≤ params.base ^
        ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1)) :=
      card_completableOmittedDigitRow_le_pow candidate sourceError transformedError selected
        hunit row

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
