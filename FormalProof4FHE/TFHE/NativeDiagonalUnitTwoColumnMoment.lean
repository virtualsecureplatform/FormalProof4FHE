/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDiagonalUnitTwoColumnParity

/-!
# Good/Bad Moment Bound from Native Two-Column Slices

The simultaneous row-kernel moment splits into two classes.  Outside the binary-dependent tuple
event, one retained two-column minor is a unit and every row loses two complete digit-polynomial
columns.  On the dependent event, the unconditional one-column bound applies.  The bad tuple
cardinality is the exact binary-line count proved in the preceding module.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- A finite sum is bounded by a uniform good bound plus a separately counted bad bound.  The
bad summands are allowed to pay both terms; this slightly redundant form avoids subtraction and
is convenient over natural cardinalities. -/
private theorem sum_le_card_mul_add_filter_card_mul
    {Index : Type} [Fintype Index]
    (predicate : Index → Prop) [DecidablePred predicate]
    (weight : Index → ℕ) (goodBound badBound : ℕ)
    (hgood : ∀ index, ¬ predicate index → weight index ≤ goodBound)
    (hbad : ∀ index, predicate index → weight index ≤ badBound) :
    (∑ index, weight index) ≤
      Fintype.card Index * goodBound +
        (Finset.univ.filter predicate).card * badBound := by
  classical
  calc
    (∑ index, weight index) ≤
        ∑ index, (goodBound + if predicate index then badBound else 0) := by
      apply Finset.sum_le_sum
      intro index _
      by_cases hpredicate : predicate index
      · simp only [hpredicate, if_true]
        exact le_trans (hbad index hpredicate) (Nat.le_add_left badBound goodBound)
      · simp only [hpredicate, if_false, add_zero]
        exact hgood index hpredicate
    _ = Fintype.card Index * goodBound +
        (Finset.univ.filter predicate).card * badBound := by
      rw [Finset.sum_add_distrib]
      simp [Nat.mul_comm]

/-- Outside the binary-dependent event, one tuple value supplies a unit retained minor, so the
product over all reconstructed rows pays the two-column bound in every row. -/
theorem reconstructedSimultaneousRowChoiceProduct_le_twoColumnPow_of_not_dependent
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (hbase : params.base ≤ q)
    (heven : 2 ∣ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (localParity : IsLocalHom (rqParityEval heven (Nat.succ_pos degree)))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)))
    (hnotDependent : ¬ RetainedParityDependentTuple heven sourceError values) :
    (∏ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
          selected hunit moment row values) ≤
      (params.base ^
        ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1))) ^
          TGSW.rowCount ringRank params.levels := by
  have hexists :
      ∃ index : Fin moment, ∃ pivot : DifferenceDigitColumn ringRank params.levels,
        pivot ≠ selected ∧
          IsUnit (retainedKernelColumnMinor candidate sourceError (values index)
            selected pivot) := by
    by_contra hnone
    exact hnotDependent
      ((no_exists_isUnitMinor_tuple_iff_parityDependentTuple heven candidate sourceError
        selected hunit localParity values).mp hnone)
  calc
    (∏ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
          selected hunit moment row values) ≤
        ∏ _row : Fin (TGSW.rowCount ringRank params.levels),
          params.base ^
            ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1)) := by
      apply Finset.prod_le_prod
      · intro row _
        exact Nat.zero_le _
      · intro row _
        exact reconstructedSimultaneousRowChoiceCard_le_pow_of_exists_isUnitMinor params hbase
          candidate sourceError transformedError selected hunit moment row values hexists
    _ = (params.base ^
        ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1))) ^
          TGSW.rowCount ringRank params.levels := by simp

/-- On every tuple, including the dependent event, the product over rows is bounded by the
one-column-omitted digit space. -/
theorem reconstructedSimultaneousRowChoiceProduct_le_oneColumnPow
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) :
    (∏ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
          selected hunit moment row values) ≤
      (params.base ^
        ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1))) ^
          TGSW.rowCount ringRank params.levels := by
  calc
    (∏ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
          selected hunit moment row values) ≤
        ∏ _row : Fin (TGSW.rowCount ringRank params.levels),
          params.base ^
            ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1)) := by
      apply Finset.prod_le_prod
      · intro row _
        exact Nat.zero_le _
      · intro row _
        exact reconstructedSimultaneousRowChoiceCard_le_pow params candidate sourceError
          transformedError selected hunit moment row values
    _ = (params.base ^
        ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1))) ^
          TGSW.rowCount ringRank params.levels := by simp

/-- **Quantitative native simultaneous-row moment bound.**  All tuples pay the two-column bound;
only the exactly counted binary-dependent tuples additionally pay the one-column bound. -/
theorem sum_reconstructedSimultaneousRowChoiceProduct_le_good_add_bad
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (hbase : params.base ≤ q)
    (heven : 2 ∣ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (localParity : IsLocalHom (rqParityEval heven (Nat.succ_pos degree))) :
    (∑ values : Fin moment →
        (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
      ∏ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
          selected hunit moment row values) ≤
      Fintype.card
          (Fin moment →
            (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) *
        (params.base ^
          ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1))) ^
            TGSW.rowCount ringRank params.levels +
      (Finset.univ.filter fun values : Fin moment →
          (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)) ↦
        RetainedParityDependentTuple heven sourceError values).card *
        (params.base ^
          ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1))) ^
            TGSW.rowCount ringRank params.levels := by
  classical
  apply sum_le_card_mul_add_filter_card_mul
    (RetainedParityDependentTuple heven sourceError)
  · intro values hnotDependent
    exact reconstructedSimultaneousRowChoiceProduct_le_twoColumnPow_of_not_dependent
      params hbase heven candidate sourceError transformedError selected hunit localParity values
      hnotDependent
  · intro values _hdependent
    exact reconstructedSimultaneousRowChoiceProduct_le_oneColumnPow params candidate sourceError
      transformedError selected hunit values

/-- The preceding moment bound with the bad-tuple count factored as the `moment`-th power of the
single-value binary-line count. -/
theorem sum_reconstructedSimultaneousRowChoiceProduct_le_good_add_bad_pow
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (hbase : params.base ≤ q)
    (heven : 2 ∣ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (localParity : IsLocalHom (rqParityEval heven (Nat.succ_pos degree))) :
    (∑ values : Fin moment →
        (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
      ∏ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
          selected hunit moment row values) ≤
      Fintype.card
          (Fin moment →
            (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) *
        (params.base ^
          ((TGSW.rowCount ringRank params.levels - 2) * (degree + 1))) ^
            TGSW.rowCount ringRank params.levels +
      ((Finset.univ.filter fun value :
          Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1) ↦
        RetainedParityDependent heven sourceError value).card ^ moment) *
        (params.base ^
          ((TGSW.rowCount ringRank params.levels - 1) * (degree + 1))) ^
            TGSW.rowCount ringRank params.levels := by
  rw [← card_retainedParityDependentTuple_eq_pow heven sourceError]
  exact sum_reconstructedSimultaneousRowChoiceProduct_le_good_add_bad params hbase heven
    candidate sourceError transformedError selected hunit localParity

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
