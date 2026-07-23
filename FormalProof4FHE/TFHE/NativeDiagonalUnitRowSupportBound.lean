/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteCenteredSupport
import FormalProof4FHE.TFHE.NativeDiagonalUnitRowNormalizedBound
import FormalProof4FHE.TFHE.SharpRotationNoise

/-!
# Centered-Support Bounds for Native TFHE Retained Rows

Every nonempty retained row fiber has a witness made from genuine small base digits.  When the
source-error rows are centered-bounded, the retained equation therefore confines the row target
to an explicit centered coefficient box.  This module converts that deterministic fact into a
cardinality bound for the complete nonempty row-fiber support and then into a denominator-
preserving normalized-moment bound.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing
attribute [local instance] Classical.propDecidable

/-- Deterministic centered-norm envelope for a retained transformed-error row. -/
def reconstructedRowTransformedErrorNormBound
    {q : ℕ} (params : Gadget.Base.Parameters q)
    (degree ringRank sourceErrorBound : ℕ) : ℕ :=
  sourceErrorBound +
    TGSW.rowCount ringRank params.levels *
      ((degree + 1) * ((params.base - 1) * sourceErrorBound))

/-- Every coefficient digit polynomial is centered-bounded by the top base digit. -/
theorem cInfNorm_coefficientDigitPolynomial_le
    {q base degree : ℕ} [NeZero q]
    (digits : Fin (degree + 1) → Fin base) :
    LatticeCrypto.cInfNorm (coefficientDigitPolynomial q digits) ≤ base - 1 := by
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro coefficient
  change (LatticeCrypto.centeredRepr
      (LatticeCrypto.Poly.toPi (coefficientDigitPolynomial q digits) coefficient)).natAbs ≤
    base - 1
  rw [coefficientDigitPolynomial_coefficient]
  calc
    (LatticeCrypto.centeredRepr ((digits coefficient).val : ZMod q)).natAbs ≤
        (digits coefficient).val :=
      NoiseBounds.centeredRepr_natCast_natAbs_le _
    _ ≤ base - 1 := by
      have := (digits coefficient).isLt
      omega

/-- Candidate-dependent signing preserves centered coefficient infinity norm. -/
@[simp]
theorem cInfNorm_signedValue
    {q degree : ℕ} [NeZero q] (candidate : Bool)
    (value : RLWE.Rq q (degree + 1)) :
    LatticeCrypto.cInfNorm
        (@signedValue (RLWE.Rq q (degree + 1)) NoiseBounds.positiveRqRing candidate value) =
      LatticeCrypto.cInfNorm value := by
  cases candidate
  · rfl
  · exact LatticeCrypto.cInfNorm_neg value

/-- Every column of a valid reconstructed row is still represented by genuine small digits,
including the selected column reconstructed through the retained equation. -/
theorem cInfNorm_reconstructedRowRingDigit_le
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (choice : CompletableOmittedDigitRow (base := base)
      candidate sourceError transformedError selected hunit row)
    (column : DifferenceDigitColumn ringRank levels) :
    LatticeCrypto.cInfNorm
        (reconstructedRowRingDigit candidate sourceError transformedError selected hunit row
          choice column) ≤
      base - 1 := by
  classical
  by_cases hcolumn : column = selected
  · subst column
    rw [reconstructedRowRingDigit_selected]
    obtain ⟨selectedDigits, hselected⟩ := choice.property
    rw [← hselected]
    exact cInfNorm_coefficientDigitPolynomial_le selectedDigits
  · rw [reconstructedRowRingDigit_other candidate sourceError transformedError selected hunit
      row choice column hcolumn]
    exact cInfNorm_coefficientDigitPolynomial_le _

/-- A witness in a row fiber forces its transformed-error target into the explicit centered
envelope. -/
theorem cInfNorm_target_le_of_reconstructedRowChoice
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (sourceErrorBound : ℕ)
    (hsource : ∀ sourceRow, LatticeCrypto.cInfNorm (sourceError sourceRow) ≤ sourceErrorBound)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (target : RLWE.Rq q (degree + 1))
    (choice : CompletableOmittedDigitRowAt (base := params.base) candidate sourceError selected
      hunit row target) :
    LatticeCrypto.cInfNorm target ≤
      reconstructedRowTransformedErrorNormBound params degree ringRank sourceErrorBound := by
  letI : CommRing (RLWE.Rq q (degree + 1)) := NoiseBounds.positiveRqCommRing
  have hequation := reconstructedRowRingDigit_retainedEquation candidate sourceError
    (constantTransformedError target) selected hunit row choice
  change sourceError row +
      ∑ column : DifferenceDigitColumn ringRank params.levels,
        reconstructedRowRingDigit candidate sourceError (constantTransformedError target)
            selected hunit row choice column *
          signedValue candidate (sourceError (finProdFinEquiv column)) = target at hequation
  rw [← hequation]
  refine (NoiseBounds.cInfNorm_add_le _ _).trans (Nat.add_le_add (hsource row) ?_)
  calc
    LatticeCrypto.cInfNorm
        (@Finset.sum (DifferenceDigitColumn ringRank params.levels)
          (RLWE.Rq q (degree + 1)) NoiseBounds.positiveRqRing.toAddCommMonoid Finset.univ
          (fun column ↦
            reconstructedRowRingDigit candidate sourceError (constantTransformedError target)
                selected hunit row choice column *
              signedValue candidate (sourceError (finProdFinEquiv column)))) ≤
        ∑ column : DifferenceDigitColumn ringRank params.levels,
          LatticeCrypto.cInfNorm
            (reconstructedRowRingDigit candidate sourceError (constantTransformedError target)
                selected hunit row choice column *
              signedValue candidate (sourceError (finProdFinEquiv column))) := by
      simpa using NoiseBounds.cInfNorm_finset_sum_le
        (fun column : DifferenceDigitColumn ringRank params.levels ↦
          reconstructedRowRingDigit candidate sourceError (constantTransformedError target)
              selected hunit row choice column *
            signedValue candidate (sourceError (finProdFinEquiv column)))
        Finset.univ
    _ ≤ ∑ _column : DifferenceDigitColumn ringRank params.levels,
        (degree + 1) * ((params.base - 1) * sourceErrorBound) := by
      apply Finset.sum_le_sum
      intro column _
      exact (SharpRotationNoise.cInfNorm_mul_le_linear
        (reconstructedRowRingDigit candidate sourceError (constantTransformedError target)
          selected hunit row choice column)
        (signedValue candidate (sourceError (finProdFinEquiv column)))).trans
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul
            (cInfNorm_reconstructedRowRingDigit_le candidate sourceError
              (constantTransformedError target) selected hunit row choice column)
            (by simpa using hsource (finProdFinEquiv column))))
    _ = TGSW.rowCount ringRank params.levels *
        ((degree + 1) * ((params.base - 1) * sourceErrorBound)) := by
      simp [TGSW.rowCount, Fintype.card_prod]

/-! ## Nonempty row-fiber support -/

/-- A nonzero row-fiber cardinality supplies an actual valid reconstructed row, so its target
inherits the deterministic centered envelope. -/
theorem cInfNorm_target_le_of_reconstructedRowFiberCardAt_ne_zero
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (sourceErrorBound : ℕ)
    (hsource : ∀ sourceRow, LatticeCrypto.cInfNorm (sourceError sourceRow) ≤ sourceErrorBound)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (target : RLWE.Rq q (degree + 1))
    (hfiber : reconstructedRowFiberCardAt (base := params.base) candidate sourceError selected
      hunit row target ≠ 0) :
    LatticeCrypto.cInfNorm target ≤
      reconstructedRowTransformedErrorNormBound params degree ringRank sourceErrorBound := by
  have hpositive : 0 < Fintype.card
      (CompletableOmittedDigitRowAt (base := params.base) candidate sourceError selected hunit row
        target) := by
    simpa [reconstructedRowFiberCardAt] using Nat.pos_of_ne_zero hfiber
  obtain ⟨choice⟩ := Fintype.card_pos_iff.mp hpositive
  exact cInfNorm_target_le_of_reconstructedRowChoice params candidate sourceError
    sourceErrorBound hsource selected hunit row target choice

/-- Reachable targets are precisely targets indexing nonempty retained row fibers. -/
abbrev ReconstructedRowReachableTargetAt
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels)) :=
  {target : RLWE.Rq q (degree + 1) //
    reconstructedRowFiberCardAt (base := params.base) candidate sourceError selected hunit row
      target ≠ 0}

/-- Forgetting reachability while retaining the proved norm bound maps the row support into the
finite centered polynomial box. -/
def reconstructedRowReachableTargetToBoundedPolynomial
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (sourceErrorBound : ℕ)
    (hsource : ∀ sourceRow, LatticeCrypto.cInfNorm (sourceError sourceRow) ≤ sourceErrorBound)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    ReconstructedRowReachableTargetAt params candidate sourceError selected hunit row →
      FormalProof4FHE.FiniteCenteredSupport.BoundedPolynomial q (degree + 1)
        (reconstructedRowTransformedErrorNormBound params degree ringRank sourceErrorBound) :=
  fun target ↦ ⟨target.1,
    cInfNorm_target_le_of_reconstructedRowFiberCardAt_ne_zero params candidate sourceError
      sourceErrorBound hsource selected hunit row target.1 target.2⟩

theorem reconstructedRowReachableTargetToBoundedPolynomial_injective
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (sourceErrorBound : ℕ)
    (hsource : ∀ sourceRow, LatticeCrypto.cInfNorm (sourceError sourceRow) ≤ sourceErrorBound)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    Function.Injective
      (reconstructedRowReachableTargetToBoundedPolynomial params candidate sourceError
        sourceErrorBound hsource selected hunit row) := by
  intro left right heq
  apply Subtype.ext
  exact congrArg
    (fun value : FormalProof4FHE.FiniteCenteredSupport.BoundedPolynomial q (degree + 1)
      (reconstructedRowTransformedErrorNormBound params degree ringRank sourceErrorBound) ↦
        value.1)
    heq

/-- Number of transformed-error targets supporting a nonempty retained row fiber. -/
noncomputable def reconstructedRowNonemptyFiberCountAt
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels)) : ℕ :=
  (Finset.univ.filter fun target : RLWE.Rq q (degree + 1) ↦
    reconstructedRowFiberCardAt (base := params.base) candidate sourceError selected hunit row
      target ≠ 0).card

/-- The complete reachable row-target support fits into the explicit centered box. -/
theorem reconstructedRowNonemptyFiberCountAt_le_centeredSupport
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (sourceErrorBound : ℕ)
    (hsource : ∀ sourceRow, LatticeCrypto.cInfNorm (sourceError sourceRow) ≤ sourceErrorBound)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    reconstructedRowNonemptyFiberCountAt params candidate sourceError selected hunit row ≤
      (2 * reconstructedRowTransformedErrorNormBound params degree ringRank sourceErrorBound + 1) ^
        (degree + 1) := by
  classical
  let bound := reconstructedRowTransformedErrorNormBound params degree ringRank sourceErrorBound
  calc
    reconstructedRowNonemptyFiberCountAt params candidate sourceError selected hunit row =
        Fintype.card
          (ReconstructedRowReachableTargetAt params candidate sourceError selected hunit row) := by
      unfold reconstructedRowNonemptyFiberCountAt ReconstructedRowReachableTargetAt
      exact (Fintype.card_subtype _).symm
    _ ≤ Fintype.card
        (FormalProof4FHE.FiniteCenteredSupport.BoundedPolynomial q (degree + 1) bound) :=
      Fintype.card_le_of_injective
        (reconstructedRowReachableTargetToBoundedPolynomial params candidate sourceError
          sourceErrorBound hsource selected hunit row)
        (reconstructedRowReachableTargetToBoundedPolynomial_injective params candidate sourceError
          sourceErrorBound hsource selected hunit row)
    _ ≤ (2 * bound + 1) ^ (degree + 1) :=
      FormalProof4FHE.FiniteCenteredSupport.card_boundedPolynomial_le q (degree + 1) bound

/-! ## Row-normalized moment consequences -/

/-- Named cardinality of the centered box containing every reachable row target. -/
def reconstructedRowCenteredSupportCard
    {q : ℕ} (params : Gadget.Base.Parameters q)
    (degree ringRank sourceErrorBound : ℕ) : ℕ :=
  (2 * reconstructedRowTransformedErrorNormBound params degree ringRank sourceErrorBound + 1) ^
    (degree + 1)

/-- A row's normalized simultaneous-acceptance mass cannot exceed the number of its nonempty
fibers.  This uses the exact fiber denominator and the inclusion of accepting rows into valid
rows. -/
theorem reconstructedRowNormalizedMomentSumAt_le_nonemptyFiberCountAt
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) :
    reconstructedRowNormalizedMomentSumAt params candidate sourceError selected hunit row values ≤
      (reconstructedRowNonemptyFiberCountAt params candidate sourceError selected hunit row : ℝ) := by
  unfold reconstructedRowNormalizedMomentSumAt reconstructedRowNonemptyFiberCountAt
  exact FormalProof4FHE.FiniteNormalizedRowMoment.sum_normalizedRatio_le_nonemptyFiberCount
    (fun target : RLWE.Rq q (degree + 1) ↦
      reconstructedRowFiberCardAt (base := params.base) candidate sourceError selected hunit row
        target)
    (fun target : RLWE.Rq q (degree + 1) ↦
      reconstructedSimultaneousRowChoiceCardAt (base := params.base) candidate sourceError selected
        hunit row target values)
    (fun target ↦ reconstructedSimultaneousRowChoiceCardAt_le_fiberCardAt params candidate
      sourceError selected hunit row target values)

/-- Pointwise centered-support bound for every row-normalized simultaneous-acceptance sum. -/
theorem reconstructedRowNormalizedMomentSumAt_le_centeredSupport
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (sourceErrorBound : ℕ)
    (hsource : ∀ sourceRow, LatticeCrypto.cInfNorm (sourceError sourceRow) ≤ sourceErrorBound)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) :
    reconstructedRowNormalizedMomentSumAt params candidate sourceError selected hunit row values ≤
      (reconstructedRowCenteredSupportCard params degree ringRank sourceErrorBound : ℝ) := by
  calc
    reconstructedRowNormalizedMomentSumAt params candidate sourceError selected hunit row values ≤
        (reconstructedRowNonemptyFiberCountAt params candidate sourceError selected hunit row : ℝ) :=
      reconstructedRowNormalizedMomentSumAt_le_nonemptyFiberCountAt params candidate sourceError
        selected hunit row values
    _ ≤ (reconstructedRowCenteredSupportCard params degree ringRank sourceErrorBound : ℝ) := by
      exact_mod_cast reconstructedRowNonemptyFiberCountAt_le_centeredSupport params candidate
        sourceError sourceErrorBound hsource selected hunit row

/-- The product over all native TGSW rows pays one centered-support factor per row. -/
theorem reconstructedRowNormalizedMomentProduct_le_centeredSupportPow
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (sourceErrorBound : ℕ)
    (hsource : ∀ sourceRow, LatticeCrypto.cInfNorm (sourceError sourceRow) ≤ sourceErrorBound)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) :
    (∏ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedRowNormalizedMomentSumAt params candidate sourceError selected hunit row
          values) ≤
      (reconstructedRowCenteredSupportCard params degree ringRank sourceErrorBound : ℝ) ^
        TGSW.rowCount ringRank params.levels := by
  calc
    (∏ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedRowNormalizedMomentSumAt params candidate sourceError selected hunit row
          values) ≤
        ∏ _row : Fin (TGSW.rowCount ringRank params.levels),
          (reconstructedRowCenteredSupportCard params degree ringRank sourceErrorBound : ℝ) := by
      apply Finset.prod_le_prod
      · intro row _
        exact reconstructedRowNormalizedMomentSumAt_nonneg params candidate sourceError selected
          hunit row values
      · intro row _
        exact reconstructedRowNormalizedMomentSumAt_le_centeredSupport params candidate sourceError
          sourceErrorBound hsource selected hunit row values
    _ = (reconstructedRowCenteredSupportCard params degree ringRank sourceErrorBound : ℝ) ^
        TGSW.rowCount ringRank params.levels := by
      simp

/-- Closed centered-support upper bound for the complete denominator-preserving retained-fiber
moment. -/
noncomputable def fixedErrorDifferenceCenteredSupportMomentBound
    {q : ℕ} [NeZero q]
    (moment : ℕ) (params : Gadget.Base.Parameters q)
    (degree ringRank sourceErrorBound : ℕ) : ℝ :=
  (Fintype.card
      (Fin moment →
        (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) : ℝ) *
    (reconstructedRowCenteredSupportCard params degree ringRank sourceErrorBound : ℝ) ^
      TGSW.rowCount ringRank params.levels

/-- **Centered-support native moment theorem.**  Under a deterministic source-error support
bound, the complete retained-fiber moment is bounded without any inverse-fiber lower bound,
parity split, or field assumption. -/
theorem fixedErrorDifferenceNormalizedRowMomentSum_le_centeredSupportMomentBound
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (sourceErrorBound : ℕ)
    (hsource : ∀ sourceRow, LatticeCrypto.cInfNorm (sourceError sourceRow) ≤ sourceErrorBound)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDifferenceNormalizedRowMomentSum moment params candidate sourceError selected hunit ≤
      fixedErrorDifferenceCenteredSupportMomentBound moment params degree ringRank
        sourceErrorBound := by
  rw [fixedErrorDifferenceNormalizedRowMomentSum_eq_sum_prod_rows params hcapacity hbase
    candidate sourceError selected hunit]
  unfold fixedErrorDifferenceCenteredSupportMomentBound
  calc
    (∑ values : Fin moment →
        (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
      ∏ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedRowNormalizedMomentSumAt params candidate sourceError selected hunit row
          values) ≤
        ∑ _values : Fin moment →
            (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
          (reconstructedRowCenteredSupportCard params degree ringRank sourceErrorBound : ℝ) ^
            TGSW.rowCount ringRank params.levels := by
      apply Finset.sum_le_sum
      intro values _
      exact reconstructedRowNormalizedMomentProduct_le_centeredSupportPow params candidate
        sourceError sourceErrorBound hsource selected hunit values
    _ = (Fintype.card
          (Fin moment →
            (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) : ℝ) *
        (reconstructedRowCenteredSupportCard params degree ringRank sourceErrorBound : ℝ) ^
          TGSW.rowCount ringRank params.levels := by
      simp [nsmul_eq_mul]

/-- The centered-support moment controls the actual equal-difference self-collision slice while
retaining both the nonempty-fiber baseline and the full ciphertext-space denominator. -/
theorem fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_centeredSupportMomentBound
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (sourceErrorBound : ℕ)
    (hsource : ∀ sourceRow, LatticeCrypto.cInfNorm (sourceError sourceRow) ≤ sourceErrorBound)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess params candidate sourceError ≤
      (fixedErrorDifferenceCenteredSupportMomentBound ringRank params degree ringRank
          sourceErrorBound -
        (fixedErrorDifferenceNonemptyFiberCount params candidate sourceError : ℝ)) /
      (Fintype.card
        (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) := by
  rw [fixedErrorDiagonalNormalizedSelfPairCollisionExcess_eq_normalizedRowMoment_sub_nonempty
    params hcapacity hbase candidate sourceError selected hunit]
  apply div_le_div_of_nonneg_right
  · exact sub_le_sub_right
      (fixedErrorDifferenceNormalizedRowMomentSum_le_centeredSupportMomentBound params hcapacity
        hbase candidate sourceError sourceErrorBound hsource selected hunit)
      (fixedErrorDifferenceNonemptyFiberCount params candidate sourceError : ℝ)
  · positivity

/-- Baseline-free corollary convenient for closed-form asymptotic estimates. -/
theorem fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_centeredSupportMomentRatio
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (sourceErrorBound : ℕ)
    (hsource : ∀ sourceRow, LatticeCrypto.cInfNorm (sourceError sourceRow) ≤ sourceErrorBound)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess params candidate sourceError ≤
      fixedErrorDifferenceCenteredSupportMomentBound ringRank params degree ringRank
          sourceErrorBound /
        (Fintype.card
          (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) := by
  exact (fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_centeredSupportMomentBound
    params hcapacity hbase candidate sourceError sourceErrorBound hsource selected hunit).trans
      (div_le_div_of_nonneg_right
        (sub_le_self _ (by positivity :
          (0 : ℝ) ≤ fixedErrorDifferenceNonemptyFiberCount params candidate sourceError))
        (by positivity))

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
