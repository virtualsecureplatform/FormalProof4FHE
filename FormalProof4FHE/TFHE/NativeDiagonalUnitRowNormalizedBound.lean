/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDiagonalUnitRowNormalizedMoment

/-!
# Capped Native TFHE Row-Normalized Moment Bounds

The two-column slice gives an absolute simultaneous-acceptance count.  This module combines that
count with the exact valid-row fiber cardinality: every normalized row weight is bounded by the
minimum of one and the absolute count divided by its actual fiber size.  The resulting good/bad
bound therefore preserves the conditioned transformed-error denominators.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing
attribute [local instance] Classical.propDecidable

/-! ## One-row capped ratios -/

/-- Simultaneously accepting rows form a subtype of the complete valid row fiber. -/
theorem reconstructedSimultaneousRowChoiceCardAt_le_fiberCardAt
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (target : RLWE.Rq q (degree + 1))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) :
    reconstructedSimultaneousRowChoiceCardAt (base := params.base) candidate sourceError selected
        hunit row target values ≤
      reconstructedRowFiberCardAt (base := params.base) candidate sourceError selected hunit row
        target := by
  classical
  unfold reconstructedSimultaneousRowChoiceCardAt reconstructedRowFiberCardAt
  let forget :
      {choice : CompletableOmittedDigitRowAt (base := params.base) candidate sourceError selected
          hunit row target //
        ∀ index, ReconstructedRowAccepts candidate sourceError
          (constantTransformedError target) selected hunit row choice (values index)} →
        CompletableOmittedDigitRowAt (base := params.base) candidate sourceError selected hunit row
          target :=
    fun choice ↦ choice.1
  exact Fintype.card_le_of_injective forget fun left right heq ↦ Subtype.ext heq

/-- Sum over one row's transformed-error coordinate of the capped external count divided by the
actual valid-row fiber cardinality. -/
noncomputable def reconstructedRowCappedAcceptanceSumAt
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (externalBound : ℕ) : ℝ :=
  ∑ target : RLWE.Rq q (degree + 1),
    min 1
      (FormalProof4FHE.FiniteNormalizedRowMoment.normalizedRatio
        (reconstructedRowFiberCardAt (base := params.base) candidate sourceError selected hunit row
          target)
        externalBound)

/-- Number of nonempty row fibers whose valid-row cardinality lies below a chosen threshold. -/
def reconstructedRowNonemptySmallFiberCountAt
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (threshold : ℕ) : ℕ :=
  FormalProof4FHE.FiniteNormalizedRowMoment.nonemptySmallFiberCount
    (fun target : RLWE.Rq q (degree + 1) ↦
      reconstructedRowFiberCardAt (base := params.base) candidate sourceError selected hunit row
        target)
    threshold

/-- Threshold form of the row inverse-fiber profile.  Only genuinely small nonempty fibers pay
one; every other target pays the explicit external-count-to-threshold ratio. -/
theorem reconstructedRowCappedAcceptanceSumAt_le_smallFiberCount_add
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (externalBound threshold : ℕ) (hthreshold : 0 < threshold) :
    reconstructedRowCappedAcceptanceSumAt params candidate sourceError selected hunit row
        externalBound ≤
      (reconstructedRowNonemptySmallFiberCountAt params candidate sourceError selected hunit row
          threshold : ℝ) +
        (Fintype.card (RLWE.Rq q (degree + 1)) : ℝ) *
          ((externalBound : ℝ) / (threshold : ℝ)) := by
  exact
    FormalProof4FHE.FiniteNormalizedRowMoment.sum_min_one_normalizedRatio_le_smallFiberCount_add
      (fun target : RLWE.Rq q (degree + 1) ↦
        reconstructedRowFiberCardAt (base := params.base) candidate sourceError selected hunit row
          target)
      externalBound threshold hthreshold

theorem reconstructedRowNormalizedMomentSumAt_nonneg
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) :
    0 ≤ reconstructedRowNormalizedMomentSumAt params candidate sourceError selected hunit row
      values := by
  unfold reconstructedRowNormalizedMomentSumAt
  apply Finset.sum_nonneg
  intro target _
  exact FormalProof4FHE.FiniteNormalizedRowMoment.normalizedRatio_nonneg _ _

theorem reconstructedRowCappedAcceptanceSumAt_nonneg
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (externalBound : ℕ) :
    0 ≤ reconstructedRowCappedAcceptanceSumAt params candidate sourceError selected hunit row
      externalBound := by
  unfold reconstructedRowCappedAcceptanceSumAt
  apply Finset.sum_nonneg
  intro target _
  exact le_min (by norm_num)
    (FormalProof4FHE.FiniteNormalizedRowMoment.normalizedRatio_nonneg _ _)

/-- Any uniform absolute acceptance bound yields a fiber-sensitive capped bound after summing
over the row's transformed-error coordinate. -/
theorem reconstructedRowNormalizedMomentSumAt_le_capped
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)))
    (externalBound : ℕ)
    (hexternal : ∀ target,
      reconstructedSimultaneousRowChoiceCardAt (base := params.base) candidate sourceError
        selected hunit row target values ≤ externalBound) :
    reconstructedRowNormalizedMomentSumAt params candidate sourceError selected hunit row values ≤
      reconstructedRowCappedAcceptanceSumAt params candidate sourceError selected hunit row
        externalBound := by
  unfold reconstructedRowNormalizedMomentSumAt reconstructedRowCappedAcceptanceSumAt
  apply Finset.sum_le_sum
  intro target _
  exact FormalProof4FHE.FiniteNormalizedRowMoment.normalizedRatio_le_min_one
    (reconstructedSimultaneousRowChoiceCardAt_le_fiberCardAt params candidate sourceError selected
      hunit row target values)
    (hexternal target)

/-! ## Two-column and one-column specializations -/

theorem reconstructedSimultaneousRowChoiceCardAt_le_twoColumnPow_of_exists_isUnitMinor
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)))
    (hexists : ∃ index : Fin moment, ∃ pivot : DifferenceDigitColumn ringRank params.levels,
      pivot ≠ selected ∧
        IsUnit (retainedKernelColumnMinor candidate sourceError (values index)
          selected pivot))
    (target : RLWE.Rq q (degree + 1)) :
    reconstructedSimultaneousRowChoiceCardAt (base := params.base) candidate sourceError selected
        hunit row target values ≤
      params.base ^ ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1)) := by
  calc
    reconstructedSimultaneousRowChoiceCardAt (base := params.base) candidate sourceError selected
        hunit row target values =
      reconstructedSimultaneousRowChoiceCard params candidate sourceError
        (constantTransformedError target) selected hunit moment row values := by
          simpa only [constantTransformedError] using
            reconstructedSimultaneousRowChoiceCardAt_eq params candidate sourceError
            (constantTransformedError target) selected hunit row values
    _ ≤ _ := reconstructedSimultaneousRowChoiceCard_le_pow_of_exists_isUnitMinor params hbase
      candidate sourceError (constantTransformedError target) selected hunit moment row values
      hexists

theorem reconstructedSimultaneousRowChoiceCardAt_le_oneColumnPow
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)))
    (target : RLWE.Rq q (degree + 1)) :
    reconstructedSimultaneousRowChoiceCardAt (base := params.base) candidate sourceError selected
        hunit row target values ≤
      params.base ^ ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1)) := by
  calc
    reconstructedSimultaneousRowChoiceCardAt (base := params.base) candidate sourceError selected
        hunit row target values =
      reconstructedSimultaneousRowChoiceCard params candidate sourceError
        (constantTransformedError target) selected hunit moment row values := by
          simpa only [constantTransformedError] using
            reconstructedSimultaneousRowChoiceCardAt_eq params candidate sourceError
            (constantTransformedError target) selected hunit row values
    _ ≤ _ := reconstructedSimultaneousRowChoiceCard_le_pow params candidate sourceError
      (constantTransformedError target) selected hunit moment row values

/-- Outside the parity-dependent tuple event, every row-local normalized sum pays the
two-column capped profile. -/
theorem reconstructedRowNormalizedMomentSumAt_le_twoColumnCapped_of_not_dependent
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (hbase : params.base ≤ q)
    (heven : 2 ∣ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (localParity : IsLocalHom (rqParityEval heven (Nat.succ_pos degree)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)))
    (hnotDependent : ¬ RetainedParityDependentTuple heven sourceError values) :
    reconstructedRowNormalizedMomentSumAt params candidate sourceError selected hunit row values ≤
      reconstructedRowCappedAcceptanceSumAt params candidate sourceError selected hunit row
        (params.base ^ ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1))) := by
  have hexists :
      ∃ index : Fin moment, ∃ pivot : DifferenceDigitColumn ringRank params.levels,
        pivot ≠ selected ∧
          IsUnit (retainedKernelColumnMinor candidate sourceError (values index)
            selected pivot) := by
    by_contra hnone
    exact hnotDependent
      ((no_exists_isUnitMinor_tuple_iff_parityDependentTuple heven candidate sourceError
        selected hunit localParity values).mp hnone)
  apply reconstructedRowNormalizedMomentSumAt_le_capped params candidate sourceError selected
    hunit row values
  intro target
  exact reconstructedSimultaneousRowChoiceCardAt_le_twoColumnPow_of_exists_isUnitMinor params
    hbase candidate sourceError selected hunit row values hexists target

/-- Every tuple, including the parity-dependent event, pays the one-column capped profile. -/
theorem reconstructedRowNormalizedMomentSumAt_le_oneColumnCapped
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) :
    reconstructedRowNormalizedMomentSumAt params candidate sourceError selected hunit row values ≤
      reconstructedRowCappedAcceptanceSumAt params candidate sourceError selected hunit row
        (params.base ^ ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1))) := by
  apply reconstructedRowNormalizedMomentSumAt_le_capped params candidate sourceError selected
    hunit row values
  intro target
  exact reconstructedSimultaneousRowChoiceCardAt_le_oneColumnPow params candidate sourceError
    selected hunit row values target

/-! ## Product and complete-moment bounds -/

/-- Product over rows of a common capped external acceptance profile. -/
noncomputable def reconstructedRowCappedAcceptanceProduct
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (externalBound : ℕ) : ℝ :=
  ∏ row : Fin (TGSW.rowCount ringRank params.levels),
    reconstructedRowCappedAcceptanceSumAt params candidate sourceError selected hunit row
      externalBound

theorem reconstructedRowCappedAcceptanceProduct_nonneg
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (externalBound : ℕ) :
    0 ≤ reconstructedRowCappedAcceptanceProduct params candidate sourceError selected hunit
      externalBound := by
  unfold reconstructedRowCappedAcceptanceProduct
  apply Finset.prod_nonneg
  intro row _
  exact reconstructedRowCappedAcceptanceSumAt_nonneg params candidate sourceError selected hunit
    row externalBound

/-- Product of rowwise threshold bounds for one common external acceptance count. -/
noncomputable def reconstructedRowThresholdAcceptanceProduct
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (externalBound : ℕ)
  (threshold : Fin (TGSW.rowCount ringRank params.levels) → ℕ) : ℝ :=
  ∏ row : Fin (TGSW.rowCount ringRank params.levels),
    ((reconstructedRowNonemptySmallFiberCountAt params candidate sourceError selected hunit row
          (threshold row) : ℝ) +
        (Fintype.card (RLWE.Rq q (degree + 1)) : ℝ) *
          ((externalBound : ℝ) / (threshold row : ℝ)))

theorem reconstructedRowThresholdAcceptanceProduct_nonneg
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (externalBound : ℕ)
    (threshold : Fin (TGSW.rowCount ringRank params.levels) → ℕ) :
    0 ≤ reconstructedRowThresholdAcceptanceProduct params candidate sourceError selected hunit
      externalBound threshold := by
  unfold reconstructedRowThresholdAcceptanceProduct
  apply Finset.prod_nonneg
  intro row _
  positivity

/-- Rowwise positive thresholds turn the capped inverse-fiber product into a small-fiber tail
product plus explicit external-count-to-threshold ratios. -/
theorem reconstructedRowCappedAcceptanceProduct_le_threshold
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (externalBound : ℕ)
    (threshold : Fin (TGSW.rowCount ringRank params.levels) → ℕ)
    (hthreshold : ∀ row, 0 < threshold row) :
    reconstructedRowCappedAcceptanceProduct params candidate sourceError selected hunit
        externalBound ≤
      reconstructedRowThresholdAcceptanceProduct params candidate sourceError selected hunit
        externalBound threshold := by
  unfold reconstructedRowCappedAcceptanceProduct reconstructedRowThresholdAcceptanceProduct
  apply Finset.prod_le_prod
  · intro row _
    exact reconstructedRowCappedAcceptanceSumAt_nonneg params candidate sourceError selected hunit
      row externalBound
  · intro row _
    exact reconstructedRowCappedAcceptanceSumAt_le_smallFiberCount_add params candidate sourceError
      selected hunit row externalBound (threshold row) (hthreshold row)

theorem reconstructedRowNormalizedMomentProduct_le_twoColumnCapped_of_not_dependent
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (hbase : params.base ≤ q)
    (heven : 2 ∣ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (localParity : IsLocalHom (rqParityEval heven (Nat.succ_pos degree)))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)))
    (hnotDependent : ¬ RetainedParityDependentTuple heven sourceError values) :
    (∏ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedRowNormalizedMomentSumAt params candidate sourceError selected hunit row
          values) ≤
      reconstructedRowCappedAcceptanceProduct params candidate sourceError selected hunit
        (params.base ^ ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1))) := by
  unfold reconstructedRowCappedAcceptanceProduct
  apply Finset.prod_le_prod
  · intro row _
    exact reconstructedRowNormalizedMomentSumAt_nonneg params candidate sourceError selected hunit
      row values
  · intro row _
    exact reconstructedRowNormalizedMomentSumAt_le_twoColumnCapped_of_not_dependent params hbase
      heven candidate sourceError selected hunit localParity row values hnotDependent

theorem reconstructedRowNormalizedMomentProduct_le_oneColumnCapped
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) :
    (∏ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedRowNormalizedMomentSumAt params candidate sourceError selected hunit row
          values) ≤
      reconstructedRowCappedAcceptanceProduct params candidate sourceError selected hunit
        (params.base ^ ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1))) := by
  unfold reconstructedRowCappedAcceptanceProduct
  apply Finset.prod_le_prod
  · intro row _
    exact reconstructedRowNormalizedMomentSumAt_nonneg params candidate sourceError selected hunit
      row values
  · intro row _
    exact reconstructedRowNormalizedMomentSumAt_le_oneColumnCapped params candidate sourceError
      selected hunit row values

/-- Real-valued good/bad summation with a separately counted bad set. -/
private theorem sum_le_card_mul_add_filter_card_mul_real
    {Index : Type} [Fintype Index]
    (predicate : Index → Prop) [DecidablePred predicate]
    (weight : Index → ℝ) (goodBound badBound : ℝ)
    (hgoodNonneg : 0 ≤ goodBound)
    (hgood : ∀ index, ¬ predicate index → weight index ≤ goodBound)
    (hbad : ∀ index, predicate index → weight index ≤ badBound) :
    (∑ index, weight index) ≤
      (Fintype.card Index : ℝ) * goodBound +
        ((Finset.univ.filter predicate).card : ℝ) * badBound := by
  classical
  calc
    (∑ index, weight index) ≤
        (∑ index, (goodBound + if predicate index then badBound else 0)) := by
      apply Finset.sum_le_sum
      intro index _
      by_cases hpredicate : predicate index
      · simp only [hpredicate, if_true]
        exact (hbad index hpredicate).trans (le_add_of_nonneg_left hgoodNonneg)
      · simp only [hpredicate, if_false, add_zero]
        exact hgood index hpredicate
    _ = (Fintype.card Index : ℝ) * goodBound +
        ((Finset.univ.filter predicate).card : ℝ) * badBound := by
      rw [Finset.sum_add_distrib]
      simp [nsmul_eq_mul]

/-- **Denominator-preserving good/bad native moment bound.**  Good tuples pay the two-column
capped inverse-fiber profile; only the exactly identified binary-dependent tuples additionally
pay the one-column profile. -/
theorem fixedErrorDifferenceNormalizedRowMomentSum_le_twoColumnCapped_add_bad
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (heven : 2 ∣ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (localParity : IsLocalHom (rqParityEval heven (Nat.succ_pos degree))) :
    fixedErrorDifferenceNormalizedRowMomentSum moment params candidate sourceError selected hunit ≤
      (Fintype.card
          (Fin moment →
            (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) : ℝ) *
        reconstructedRowCappedAcceptanceProduct params candidate sourceError selected hunit
          (params.base ^ ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1))) +
      ((Finset.univ.filter fun values : Fin moment →
          (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)) ↦
        RetainedParityDependentTuple heven sourceError values).card : ℝ) *
        reconstructedRowCappedAcceptanceProduct params candidate sourceError selected hunit
          (params.base ^ ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1))) := by
  rw [fixedErrorDifferenceNormalizedRowMomentSum_eq_sum_prod_rows params hcapacity hbase
    candidate sourceError selected hunit]
  apply sum_le_card_mul_add_filter_card_mul_real
    (RetainedParityDependentTuple heven sourceError)
  · exact reconstructedRowCappedAcceptanceProduct_nonneg params candidate sourceError selected
      hunit _
  · intro values hnotDependent
    exact reconstructedRowNormalizedMomentProduct_le_twoColumnCapped_of_not_dependent params hbase
      heven candidate sourceError selected hunit localParity values hnotDependent
  · intro values _hdependent
    exact reconstructedRowNormalizedMomentProduct_le_oneColumnCapped params candidate sourceError
      selected hunit values

/-- The denominator-preserving bound with the bad tuple cardinality factored as a power of the
single-value parity-line count. -/
theorem fixedErrorDifferenceNormalizedRowMomentSum_le_twoColumnCapped_add_bad_pow
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (heven : 2 ∣ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (localParity : IsLocalHom (rqParityEval heven (Nat.succ_pos degree))) :
    fixedErrorDifferenceNormalizedRowMomentSum moment params candidate sourceError selected hunit ≤
      (Fintype.card
          (Fin moment →
            (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) : ℝ) *
        reconstructedRowCappedAcceptanceProduct params candidate sourceError selected hunit
          (params.base ^ ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1))) +
      ((Finset.univ.filter fun value :
          Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1) ↦
        RetainedParityDependent heven sourceError value).card ^ moment : ℝ) *
        reconstructedRowCappedAcceptanceProduct params candidate sourceError selected hunit
          (params.base ^ ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1))) := by
  rw [← Nat.cast_pow]
  rw [← card_retainedParityDependentTuple_eq_pow heven sourceError]
  exact fixedErrorDifferenceNormalizedRowMomentSum_le_twoColumnCapped_add_bad params hcapacity
    hbase heven candidate sourceError selected hunit localParity

/-- Named finite bound appearing on the right of the denominator-preserving good/bad theorem. -/
noncomputable def fixedErrorDifferenceTwoColumnCappedMomentBound
    {q degree ringRank : ℕ} [NeZero q]
    (moment : ℕ) (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (heven : 2 ∣ q) : ℝ :=
  (Fintype.card
      (Fin moment →
        (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) : ℝ) *
    reconstructedRowCappedAcceptanceProduct params candidate sourceError selected hunit
      (params.base ^ ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1))) +
  ((Finset.univ.filter fun value :
      Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1) ↦
    RetainedParityDependent heven sourceError value).card : ℝ) ^ moment *
    reconstructedRowCappedAcceptanceProduct params candidate sourceError selected hunit
      (params.base ^ ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1)))

/-- Thresholded version of the two-column good/bad moment bound.  The two threshold functions may
be tuned independently for good and parity-dependent tuples. -/
noncomputable def fixedErrorDifferenceTwoColumnThresholdMomentBound
    {q degree ringRank : ℕ} [NeZero q]
    (moment : ℕ) (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (heven : 2 ∣ q)
    (goodThreshold badThreshold :
      Fin (TGSW.rowCount ringRank params.levels) → ℕ) : ℝ :=
  (Fintype.card
      (Fin moment →
        (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) : ℝ) *
    reconstructedRowThresholdAcceptanceProduct params candidate sourceError selected hunit
      (params.base ^ ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1)))
      goodThreshold +
  ((Finset.univ.filter fun value :
      Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1) ↦
    RetainedParityDependent heven sourceError value).card : ℝ) ^ moment *
    reconstructedRowThresholdAcceptanceProduct params candidate sourceError selected hunit
      (params.base ^ ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1)))
      badThreshold

/-- Positive row thresholds dominate the exact capped good/bad moment bound. -/
theorem fixedErrorDifferenceTwoColumnCappedMomentBound_le_threshold
    {q degree ringRank : ℕ} [NeZero q]
    (moment : ℕ) (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (heven : 2 ∣ q)
    (goodThreshold badThreshold :
      Fin (TGSW.rowCount ringRank params.levels) → ℕ)
    (hgoodThreshold : ∀ row, 0 < goodThreshold row)
    (hbadThreshold : ∀ row, 0 < badThreshold row) :
    fixedErrorDifferenceTwoColumnCappedMomentBound moment params candidate sourceError selected
        hunit heven ≤
      fixedErrorDifferenceTwoColumnThresholdMomentBound moment params candidate sourceError
        selected hunit heven goodThreshold badThreshold := by
  unfold fixedErrorDifferenceTwoColumnCappedMomentBound
    fixedErrorDifferenceTwoColumnThresholdMomentBound
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left
    · exact reconstructedRowCappedAcceptanceProduct_le_threshold params candidate sourceError
        selected hunit _ goodThreshold hgoodThreshold
    · positivity
  · apply mul_le_mul_of_nonneg_left
    · exact reconstructedRowCappedAcceptanceProduct_le_threshold params candidate sourceError
        selected hunit _ badThreshold hbadThreshold
    · positivity

theorem fixedErrorDifferenceNormalizedRowMomentSum_le_twoColumnCappedMomentBound
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (heven : 2 ∣ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (localParity : IsLocalHom (rqParityEval heven (Nat.succ_pos degree))) :
    fixedErrorDifferenceNormalizedRowMomentSum moment params candidate sourceError selected hunit ≤
      fixedErrorDifferenceTwoColumnCappedMomentBound moment params candidate sourceError selected
        hunit heven := by
  unfold fixedErrorDifferenceTwoColumnCappedMomentBound
  exact fixedErrorDifferenceNormalizedRowMomentSum_le_twoColumnCapped_add_bad_pow params hcapacity
    hbase heven candidate sourceError selected hunit localParity

/-- Complete thresholded denominator-preserving moment estimate. -/
theorem fixedErrorDifferenceNormalizedRowMomentSum_le_twoColumnThresholdMomentBound
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (heven : 2 ∣ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (localParity : IsLocalHom (rqParityEval heven (Nat.succ_pos degree)))
    (goodThreshold badThreshold :
      Fin (TGSW.rowCount ringRank params.levels) → ℕ)
    (hgoodThreshold : ∀ row, 0 < goodThreshold row)
    (hbadThreshold : ∀ row, 0 < badThreshold row) :
    fixedErrorDifferenceNormalizedRowMomentSum moment params candidate sourceError selected hunit ≤
      fixedErrorDifferenceTwoColumnThresholdMomentBound moment params candidate sourceError
        selected hunit heven goodThreshold badThreshold := by
  exact
    (fixedErrorDifferenceNormalizedRowMomentSum_le_twoColumnCappedMomentBound params hcapacity
      hbase heven candidate sourceError selected hunit localParity).trans
      (fixedErrorDifferenceTwoColumnCappedMomentBound_le_threshold moment params candidate
        sourceError selected hunit heven goodThreshold badThreshold hgoodThreshold hbadThreshold)

/-- The capped inverse-fiber profile controls the actual native equal-difference collision slice,
with the nonempty-fiber baseline and the full ciphertext denominator both retained. -/
theorem fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_twoColumnCappedMomentBound
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (heven : 2 ∣ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (localParity : IsLocalHom (rqParityEval heven (Nat.succ_pos degree))) :
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess params candidate sourceError ≤
      (fixedErrorDifferenceTwoColumnCappedMomentBound ringRank params candidate sourceError
          selected hunit heven -
        (fixedErrorDifferenceNonemptyFiberCount params candidate sourceError : ℝ)) /
      (Fintype.card
        (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) := by
  rw [fixedErrorDiagonalNormalizedSelfPairCollisionExcess_eq_normalizedRowMoment_sub_nonempty
    params hcapacity hbase candidate sourceError selected hunit]
  apply div_le_div_of_nonneg_right
  · exact sub_le_sub_right
      (fixedErrorDifferenceNormalizedRowMomentSum_le_twoColumnCappedMomentBound params hcapacity
        hbase heven candidate sourceError selected hunit localParity)
      (fixedErrorDifferenceNonemptyFiberCount params candidate sourceError : ℝ)
  · positivity

/-- Thresholded small-fiber-tail bound for the actual native equal-difference collision slice. -/
theorem fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_twoColumnThresholdMomentBound
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (heven : 2 ∣ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (localParity : IsLocalHom (rqParityEval heven (Nat.succ_pos degree)))
    (goodThreshold badThreshold :
      Fin (TGSW.rowCount ringRank params.levels) → ℕ)
    (hgoodThreshold : ∀ row, 0 < goodThreshold row)
    (hbadThreshold : ∀ row, 0 < badThreshold row) :
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess params candidate sourceError ≤
      (fixedErrorDifferenceTwoColumnThresholdMomentBound ringRank params candidate sourceError
          selected hunit heven goodThreshold badThreshold -
        (fixedErrorDifferenceNonemptyFiberCount params candidate sourceError : ℝ)) /
      (Fintype.card
        (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) := by
  rw [fixedErrorDiagonalNormalizedSelfPairCollisionExcess_eq_normalizedRowMoment_sub_nonempty
    params hcapacity hbase candidate sourceError selected hunit]
  apply div_le_div_of_nonneg_right
  · exact sub_le_sub_right
      (fixedErrorDifferenceNormalizedRowMomentSum_le_twoColumnThresholdMomentBound params hcapacity
        hbase heven candidate sourceError selected hunit localParity goodThreshold badThreshold
        hgoodThreshold hbadThreshold)
      (fixedErrorDifferenceNonemptyFiberCount params candidate sourceError : ℝ)
  · positivity

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
