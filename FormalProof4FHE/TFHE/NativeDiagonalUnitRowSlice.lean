/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDifferenceDigitUniformity
import FormalProof4FHE.TFHE.NativeDiagonalPairCollisionNormalForm

/-!
# Unit-Row Slices of the Native Selected Diagonal

At exact gadget capacity a native difference ciphertext is equivalent to its complete tensor of
base digits.  If one coordinate of the retained source-error vector is a unit, then after every
other digit column is fixed, the transformed error determines the remaining digit polynomial in
each matrix row uniquely.

This is an injective-slice statement, not a claim that the distinguished digit polynomial is
uniform over the whole coefficient ring.  That distinction is essential for the conditioned
selected-diagonal analysis.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- Finite coefficient-digit tensor exposed by an exact-capacity native difference ciphertext. -/
abbrev DifferenceDigitTensor (base degree ringRank levels : ℕ) :=
  Fin (TGSW.rowCount ringRank levels) →
    Fin (ringRank + 1) → Fin (degree + 1) → Fin levels → Fin base

/-- One column of the selected-diagonal row matrix, before flattening. -/
abbrev DifferenceDigitColumn (ringRank levels : ℕ) :=
  Fin (ringRank + 1) × Fin levels

/-- Cast one coefficient-digit vector to the corresponding small-coefficient ring element. -/
def coefficientDigitPolynomial (q : ℕ) {base degree : ℕ}
    (digits : Fin (degree + 1) → Fin base) : RLWE.Rq q (degree + 1) :=
  LatticeCrypto.Poly.ofPi fun coefficient ↦ ((digits coefficient).val : ZMod q)

@[simp]
theorem coefficientDigitPolynomial_coefficient (q : ℕ) {base degree : ℕ}
    (digits : Fin (degree + 1) → Fin base) (coefficient : Fin (degree + 1)) :
    LatticeCrypto.Poly.toPi (coefficientDigitPolynomial q digits) coefficient =
      ((digits coefficient).val : ZMod q) := by
  simp [coefficientDigitPolynomial]

/-- Casting digits below the coefficient modulus is injective coefficientwise. -/
theorem coefficientDigitPolynomial_injective {q base degree : ℕ} [NeZero q]
    (hbase : base ≤ q) :
    Function.Injective
      (coefficientDigitPolynomial q :
        (Fin (degree + 1) → Fin base) → RLWE.Rq q (degree + 1)) := by
  intro left right heq
  funext coefficient
  apply Fin.ext
  have hcoefficient := congrArg
    (fun value ↦ LatticeCrypto.Poly.toPi value coefficient) heq
  simp only [coefficientDigitPolynomial_coefficient] at hcoefficient
  have hval := congrArg ZMod.val hcoefficient
  have hleft : (left coefficient).val < q :=
    (left coefficient).isLt.trans_le hbase
  have hright : (right coefficient).val < q :=
    (right coefficient).isLt.trans_le hbase
  simpa [ZMod.val_natCast_of_lt hleft, ZMod.val_natCast_of_lt hright] using hval

/-- Interpret every coefficient-digit column as the ring digit used by the row operator. -/
def digitTensorRingDigits {q base degree ringRank levels : ℕ}
    (digits : DifferenceDigitTensor base degree ringRank levels) :
    Fin (TGSW.rowCount ringRank levels) →
      Fin (ringRank + 1) → Fin levels → RLWE.Rq q (degree + 1) :=
  fun row block level ↦
    coefficientDigitPolynomial q (fun coefficient ↦ digits row block coefficient level)

@[simp]
theorem digitTensorRingDigits_coefficient {q base degree ringRank levels : ℕ}
    (digits : DifferenceDigitTensor base degree ringRank levels)
    (row : Fin (TGSW.rowCount ringRank levels))
    (block : Fin (ringRank + 1)) (level : Fin levels)
    (coefficient : Fin (degree + 1)) :
    LatticeCrypto.Poly.toPi
        (digitTensorRingDigits (q := q) digits row block level) coefficient =
      ((digits row block coefficient level).val : ZMod q) := by
  simp [digitTensorRingDigits]

/-- The transformed retained error computed directly from a coefficient-digit tensor. -/
def digitTensorFixedErrorSide {q base degree ringRank levels : ℕ}
    [NeZero q] (candidate : Bool)
    (sourceError : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (digits : DifferenceDigitTensor base degree ringRank levels) :
    Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1) :=
  rowOperator candidate (digitTensorRingDigits digits) sourceError

/-- Equality outside one matrix column, expressed on the complete coefficient-digit tensor. -/
def EqualOffDigitColumn {base degree ringRank levels : ℕ}
    (selected : DifferenceDigitColumn ringRank levels)
    (left right : DifferenceDigitTensor base degree ringRank levels) : Prop :=
  ∀ row block coefficient level,
    (block, level) ≠ selected →
      left row block coefficient level = right row block coefficient level

/-- A unit source-error coordinate makes the transformed-error slice injective in the omitted
digit column.  Equivalently, equal off-column digits and equal transformed errors force equality
of the complete digit tensors. -/
theorem digitTensor_eq_of_equalOffColumn_of_fixedError_eq_of_isUnit
    {q base degree ringRank levels : ℕ} [NeZero q]
    (hbase : base ≤ q) (candidate : Bool)
    (sourceError : Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    {left right : DifferenceDigitTensor base degree ringRank levels}
    (hoff : EqualOffDigitColumn selected left right)
    (hside : digitTensorFixedErrorSide candidate sourceError left =
      digitTensorFixedErrorSide candidate sourceError right) :
    left = right := by
  funext row block coefficient level
  by_cases hselected : (block, level) = selected
  · have hotherDigit (other : DifferenceDigitColumn ringRank levels)
        (hother : other ≠ selected) :
        digitTensorRingDigits (q := q) left row other.1 other.2 =
          digitTensorRingDigits (q := q) right row other.1 other.2 := by
      unfold digitTensorRingDigits coefficientDigitPolynomial
      congr 1
      funext otherCoefficient
      exact congrArg (fun digit : Fin base ↦ ((digit.val : ZMod q)))
        (hoff row other.1 otherCoefficient other.2 hother)
    have hsums :
        (∑ index : DifferenceDigitColumn ringRank levels,
          digitTensorRingDigits (q := q) left row index.1 index.2 *
            signedValue candidate (sourceError (finProdFinEquiv index))) =
        ∑ index : DifferenceDigitColumn ringRank levels,
          digitTensorRingDigits (q := q) right row index.1 index.2 *
            signedValue candidate (sourceError (finProdFinEquiv index)) := by
      have hrow := congrFun hside row
      simp only [digitTensorFixedErrorSide, rowOperator] at hrow
      exact add_left_cancel hrow
    let leftTerm := fun index : DifferenceDigitColumn ringRank levels ↦
      digitTensorRingDigits (q := q) left row index.1 index.2 *
        signedValue candidate (sourceError (finProdFinEquiv index))
    let rightTerm := fun index : DifferenceDigitColumn ringRank levels ↦
      digitTensorRingDigits (q := q) right row index.1 index.2 *
        signedValue candidate (sourceError (finProdFinEquiv index))
    have hrest :
        (∑ index ∈ Finset.univ.erase selected, leftTerm index) =
          ∑ index ∈ Finset.univ.erase selected, rightTerm index := by
      apply Finset.sum_congr rfl
      intro index hindex
      have hne : index ≠ selected := (Finset.mem_erase.mp hindex).1
      simp only [leftTerm, rightTerm]
      rw [hotherDigit index hne]
    have hleftDecompose :
        (∑ index ∈ Finset.univ.erase selected, leftTerm index) + leftTerm selected =
          ∑ index, leftTerm index :=
      Finset.sum_erase_add Finset.univ leftTerm (Finset.mem_univ selected)
    have hrightDecompose :
        (∑ index ∈ Finset.univ.erase selected, rightTerm index) + rightTerm selected =
          ∑ index, rightTerm index :=
      Finset.sum_erase_add Finset.univ rightTerm (Finset.mem_univ selected)
    have hterms : leftTerm selected = rightTerm selected := by
      have hfull : (∑ index, leftTerm index) = ∑ index, rightTerm index := by
        simpa only [leftTerm, rightTerm] using hsums
      rw [← hleftDecompose, ← hrightDecompose, hrest] at hfull
      exact add_left_cancel hfull
    have hsignedUnit :
        IsUnit (signedValue candidate (sourceError (finProdFinEquiv selected))) := by
      cases candidate
      · simpa using hunit
      · simpa using hunit.neg
    have hpolynomial :
        digitTensorRingDigits (q := q) left row selected.1 selected.2 =
          digitTensorRingDigits (q := q) right row selected.1 selected.2 := by
      exact hsignedUnit.mul_left_inj.mp (by
        simpa only [leftTerm, rightTerm] using hterms)
    have hcoefficients := coefficientDigitPolynomial_injective
      (degree := degree) hbase hpolynomial
    have hselectedBlock : block = selected.1 := by
      exact congrArg Prod.fst hselected
    have hselectedLevel : level = selected.2 := by
      exact congrArg Prod.snd hselected
    subst block
    subst level
    exact congrFun hcoefficients coefficient
  · exact hoff row block coefficient level hselected

/-! ## Finite conditioned-fiber embedding -/

/-- A complete digit tensor with one matrix column omitted. -/
abbrev DifferenceDigitTensorWithoutColumn
    (base degree ringRank levels : ℕ)
    (selected : DifferenceDigitColumn ringRank levels) :=
  Fin (TGSW.rowCount ringRank levels) →
    {column : DifferenceDigitColumn ringRank levels // column ≠ selected} →
      Fin (degree + 1) → Fin base

/-- Forget the distinguished matrix column of a complete coefficient-digit tensor. -/
def digitTensorWithoutColumn {base degree ringRank levels : ℕ}
    (selected : DifferenceDigitColumn ringRank levels)
    (digits : DifferenceDigitTensor base degree ringRank levels) :
    DifferenceDigitTensorWithoutColumn base degree ringRank levels selected :=
  fun row column coefficient ↦
    digits row column.1.1 coefficient column.1.2

/-- Omitting one column removes exactly one of the `rowCount` flattened columns. -/
theorem card_differenceDigitColumn_ne
    {ringRank levels : ℕ} (selected : DifferenceDigitColumn ringRank levels) :
    Fintype.card
        {column : DifferenceDigitColumn ringRank levels // column ≠ selected} =
      TGSW.rowCount ringRank levels - 1 := by
  rw [Fintype.card_subtype_compl]
  simp [DifferenceDigitColumn, TGSW.rowCount]

/-- Exact cardinality of the coefficient-digit tensor with one column omitted. -/
theorem card_differenceDigitTensorWithoutColumn
    {base degree ringRank levels : ℕ}
    (selected : DifferenceDigitColumn ringRank levels) :
    Fintype.card
        (DifferenceDigitTensorWithoutColumn base degree ringRank levels selected) =
      base ^ (TGSW.rowCount ringRank levels *
        (TGSW.rowCount ringRank levels - 1) * (degree + 1)) := by
  change Fintype.card
      (Fin (TGSW.rowCount ringRank levels) →
        {column : DifferenceDigitColumn ringRank levels // column ≠ selected} →
          Fin (degree + 1) → Fin base) = _
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
    card_differenceDigitColumn_ne]
  simp only [Fintype.card_fin]
  rw [← pow_mul, ← pow_mul]
  congr 1
  simp only [TGSW.rowCount]
  ac_rfl

/-- Equality after omitting a column implies coefficientwise equality off that column. -/
theorem equalOffDigitColumn_of_digitTensorWithoutColumn_eq
    {base degree ringRank levels : ℕ}
    (selected : DifferenceDigitColumn ringRank levels)
    {left right : DifferenceDigitTensor base degree ringRank levels}
    (heq : digitTensorWithoutColumn selected left =
      digitTensorWithoutColumn selected right) :
    EqualOffDigitColumn selected left right := by
  intro row block coefficient level hne
  have hvalue := congrArg
    (fun digits ↦ digits row ⟨(block, level), hne⟩ coefficient) heq
  simpa only [digitTensorWithoutColumn] using hvalue

/-- One transformed-error fiber of the finite coefficient-digit tensor. -/
abbrev DigitTensorFixedErrorFiber {q base degree ringRank levels : ℕ}
    [NeZero q] (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1)) :=
  {digits : DifferenceDigitTensor base degree ringRank levels //
    digitTensorFixedErrorSide candidate sourceError digits = transformedError}

/-- Project a conditioned digit tensor to all columns except the distinguished one. -/
def digitTensorFixedErrorFiberProjection
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels) :
    DigitTensorFixedErrorFiber (base := base) candidate sourceError transformedError →
      DifferenceDigitTensorWithoutColumn base degree ringRank levels selected :=
  fun digits ↦ digitTensorWithoutColumn selected digits.1

/-- On a unit source-error row, omitting one digit column remains injective inside every
transformed-error fiber. -/
theorem digitTensorFixedErrorFiberProjection_injective
    {q base degree ringRank levels : ℕ} [NeZero q]
    (hbase : base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    Function.Injective
      (digitTensorFixedErrorFiberProjection (base := base)
        candidate sourceError transformedError selected) := by
  intro left right heq
  apply Subtype.ext
  apply digitTensor_eq_of_equalOffColumn_of_fixedError_eq_of_isUnit
      hbase candidate sourceError selected hunit
  · exact equalOffDigitColumn_of_digitTensorWithoutColumn_eq selected heq
  · exact left.property.trans right.property.symm

/-- Every transformed-error fiber has at most as many elements as the tensor with one digit
column removed. -/
theorem card_digitTensorFixedErrorFiber_le_withoutColumn
    {q base degree ringRank levels : ℕ} [NeZero q]
    (hbase : base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    Fintype.card (DigitTensorFixedErrorFiber (base := base)
        candidate sourceError transformedError) ≤
      Fintype.card
        (DifferenceDigitTensorWithoutColumn base degree ringRank levels selected) := by
  exact Fintype.card_le_of_injective
    (digitTensorFixedErrorFiberProjection (base := base)
      candidate sourceError transformedError selected)
    (digitTensorFixedErrorFiberProjection_injective (base := base)
      hbase candidate sourceError transformedError selected hunit)

/-! ## Transfer to native ciphertext fibers -/

/-- Casting the full coefficient-digit vector of a native difference ciphertext reconstructs
exactly the ring digits used by its row operator. -/
theorem digitTensorRingDigits_differenceDigitCoefficientVector
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    digitTensorRingDigits (q := q)
        (differenceDigitCoefficientVector params difference) =
      differenceEntryDigits params difference := by
  funext row block level
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  calc
    LatticeCrypto.Poly.toPi
        (digitTensorRingDigits (q := q)
          (differenceDigitCoefficientVector params difference) row block level)
          coefficient =
        ((differenceDigitCoefficientVector params difference
          row block coefficient level).val : ZMod q) := by
      simp [digitTensorRingDigits, coefficientDigitPolynomial]
    _ = LatticeCrypto.Poly.toPi
        (differenceEntryDigits params difference row block level) coefficient :=
      differenceDigitCoefficientVector_cast params difference row block coefficient level

/-- The digit-tensor and native-ciphertext presentations compute the same retained error. -/
theorem digitTensorFixedErrorSide_differenceDigitCoefficientVector
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    digitTensorFixedErrorSide candidate sourceError
        (differenceDigitCoefficientVector params difference) =
      fixedErrorDifferenceSide params candidate sourceError difference := by
  unfold digitTensorFixedErrorSide fixedErrorDifferenceSide
  rw [digitTensorRingDigits_differenceDigitCoefficientVector]

/-- Native difference ciphertexts in one retained transformed-error fiber. -/
abbrev FixedErrorDifferenceFiber
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :=
  {difference : RingGSWCiphertext q (degree + 1) ringRank params.levels //
    fixedErrorDifferenceSide params candidate sourceError difference = transformedError}

/-- Digitize a native ciphertext in one retained fiber and omit the distinguished column. -/
def fixedErrorDifferenceFiberProjection
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels) :
    FixedErrorDifferenceFiber params candidate sourceError transformedError →
      DifferenceDigitTensorWithoutColumn
        params.base degree ringRank params.levels selected :=
  fun difference ↦ digitTensorWithoutColumn selected
    (differenceDigitCoefficientVector params difference.1)

/-- At exact gadget capacity, the omitted-column projection is injective on every native
retained-error fiber whenever the selected source-error entry is a unit. -/
theorem fixedErrorDifferenceFiberProjection_injective
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    Function.Injective
      (fixedErrorDifferenceFiberProjection params candidate sourceError
        transformedError selected) := by
  intro left right heq
  apply Subtype.ext
  apply (differenceDigitCoefficientVector_bijective
    (degree := degree) (ringRank := ringRank) params hcapacity).1
  apply digitTensor_eq_of_equalOffColumn_of_fixedError_eq_of_isUnit
      hbase candidate sourceError selected hunit
  · exact equalOffDigitColumn_of_digitTensorWithoutColumn_eq selected heq
  · rw [digitTensorFixedErrorSide_differenceDigitCoefficientVector,
      digitTensorFixedErrorSide_differenceDigitCoefficientVector]
    exact left.property.trans right.property.symm

/-- Concrete unit-row bound for the native retained-error fiber cardinality. -/
theorem fixedErrorDifferenceFiberCard_le_withoutColumn
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDifferenceFiberCard params candidate sourceError transformedError ≤
      Fintype.card
        (DifferenceDigitTensorWithoutColumn
          params.base degree ringRank params.levels selected) := by
  unfold fixedErrorDifferenceFiberCard FormalProof4FHE.ConditionalCollision.sideFiberCard
  rw [← Fintype.card_subtype]
  exact Fintype.card_le_of_injective
    (fixedErrorDifferenceFiberProjection params candidate sourceError
      transformedError selected)
    (fixedErrorDifferenceFiberProjection_injective params hcapacity hbase candidate
      sourceError transformedError selected hunit)

/-- Closed-form version of the unit-row native retained-fiber bound.  Relative to the complete
IID digit tensor, fixing the transformed error removes at least one full digit-polynomial column
per matrix row. -/
theorem fixedErrorDifferenceFiberCard_le_pow_of_isUnit
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDifferenceFiberCard params candidate sourceError transformedError ≤
      params.base ^ (TGSW.rowCount ringRank params.levels *
        (TGSW.rowCount ringRank params.levels - 1) * (degree + 1)) := by
  calc
    fixedErrorDifferenceFiberCard params candidate sourceError transformedError ≤
        Fintype.card
          (DifferenceDigitTensorWithoutColumn
            params.base degree ringRank params.levels selected) :=
      fixedErrorDifferenceFiberCard_le_withoutColumn params hcapacity hbase candidate
        sourceError transformedError selected hunit
    _ = params.base ^ (TGSW.rowCount ringRank params.levels *
          (TGSW.rowCount ringRank params.levels - 1) * (degree + 1)) :=
      card_differenceDigitTensorWithoutColumn selected

/-- An existential unit source-error row supplies one distinguished column whose omission bounds
every retained transformed-error fiber. -/
theorem exists_unitColumn_fixedErrorDifferenceFiberCard_le_pow
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (hunit : ∃ row, IsUnit (sourceError row)) :
    ∃ selected : DifferenceDigitColumn ringRank params.levels,
      IsUnit (sourceError (finProdFinEquiv selected)) ∧
      ∀ transformedError : DiagonalErrorVector q degree ringRank params.levels,
        fixedErrorDifferenceFiberCard params candidate sourceError transformedError ≤
          params.base ^ (TGSW.rowCount ringRank params.levels *
            (TGSW.rowCount ringRank params.levels - 1) * (degree + 1)) := by
  obtain ⟨row, hrow⟩ := hunit
  let selected : DifferenceDigitColumn ringRank params.levels :=
    finProdFinEquiv.symm row
  have hselected : finProdFinEquiv selected = row := by
    exact finProdFinEquiv.apply_symm_apply row
  refine ⟨selected, ?_, ?_⟩
  · simpa only [hselected] using hrow
  · intro transformedError
    exact fixedErrorDifferenceFiberCard_le_pow_of_isUnit params hcapacity hbase candidate
      sourceError transformedError selected (by simpa only [hselected] using hrow)

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
