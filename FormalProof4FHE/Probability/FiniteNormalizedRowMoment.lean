/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Exact Factorization of Finite Normalized Row Moments

Conditioned collision expressions divide a row-product numerator by a row-product fiber
cardinality.  Replacing every nonempty denominator by one destroys the cancellation needed in
the TFHE retained-fiber problem.  This file proves the elementary exact alternative: define the
zero-fiber ratio to be zero, distribute the quotient across rows, and then exchange the finite
sum over target vectors with the row product.
-/

open scoped BigOperators

namespace FormalProof4FHE.FiniteNormalizedRowMoment

noncomputable section

/-- A totalized finite-cardinality ratio. -/
def normalizedRatio (fiberCard acceptingCard : ℕ) : ℝ :=
  if fiberCard = 0 then 0 else (acceptingCard : ℝ) / (fiberCard : ℝ)

theorem normalizedRatio_nonneg (fiberCard acceptingCard : ℕ) :
    0 ≤ normalizedRatio fiberCard acceptingCard := by
  by_cases hzero : fiberCard = 0
  · simp [normalizedRatio, hzero]
  · rw [normalizedRatio, if_neg hzero]
    exact div_nonneg (show (0 : ℝ) ≤ (acceptingCard : ℝ) by positivity)
      (show (0 : ℝ) ≤ (fiberCard : ℝ) by positivity)

/-- Increasing the accepting count can only increase a totalized ratio with the same fiber. -/
theorem normalizedRatio_mono_right
    {fiberCard leftCard rightCard : ℕ} (hle : leftCard ≤ rightCard) :
    normalizedRatio fiberCard leftCard ≤ normalizedRatio fiberCard rightCard := by
  by_cases hzero : fiberCard = 0
  · simp [normalizedRatio, hzero]
  · simp only [normalizedRatio, hzero, if_false]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (Nat.cast_nonneg fiberCard)

/-- A subtype count normalized by its ambient nonempty fiber is at most one. -/
theorem normalizedRatio_le_one_of_le_fiber
    {fiberCard acceptingCard : ℕ} (hle : acceptingCard ≤ fiberCard) :
    normalizedRatio fiberCard acceptingCard ≤ 1 := by
  by_cases hzero : fiberCard = 0
  · simp [normalizedRatio, hzero]
  · simp only [normalizedRatio, hzero, if_false]
    have hFiberPos : (0 : ℝ) < (fiberCard : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    exact (div_le_one hFiberPos).2 (by exact_mod_cast hle)

/-- If an accepting count is bounded both by its fiber and by an external count, its normalized
weight is bounded by the smaller of one and the external normalized count. -/
theorem normalizedRatio_le_min_one
    {fiberCard acceptingCard externalBound : ℕ}
    (hfiber : acceptingCard ≤ fiberCard) (hexternal : acceptingCard ≤ externalBound) :
    normalizedRatio fiberCard acceptingCard ≤
      min 1 (normalizedRatio fiberCard externalBound) := by
  exact le_min (normalizedRatio_le_one_of_le_fiber hfiber)
    (normalizedRatio_mono_right hexternal)

/-- Number of genuinely small nonempty fibers below a supplied threshold.  Empty fibers are
excluded because their totalized normalized weight is exactly zero. -/
def nonemptySmallFiberCount
    {Target : Type} [Fintype Target]
    (fiberCard : Target → ℕ) (threshold : ℕ) : ℕ :=
  (Finset.univ.filter fun target ↦
    fiberCard target ≠ 0 ∧ fiberCard target < threshold).card

/-- A capped inverse-fiber sum is controlled by the number of nonempty fibers below a threshold
plus the external count divided by that threshold on every target. -/
theorem sum_min_one_normalizedRatio_le_smallFiberCount_add
    {Target : Type} [Fintype Target]
    (fiberCard : Target → ℕ) (externalBound threshold : ℕ)
    (hthreshold : 0 < threshold) :
    (∑ target, min 1 (normalizedRatio (fiberCard target) externalBound)) ≤
      (nonemptySmallFiberCount fiberCard threshold : ℝ) +
        (Fintype.card Target : ℝ) *
          ((externalBound : ℝ) / (threshold : ℝ)) := by
  classical
  have hThresholdReal : (0 : ℝ) < (threshold : ℝ) := by exact_mod_cast hthreshold
  have hRatioNonneg :
      (0 : ℝ) ≤ (externalBound : ℝ) / (threshold : ℝ) := by positivity
  calc
    (∑ target, min 1 (normalizedRatio (fiberCard target) externalBound)) ≤
        ∑ target,
          (((externalBound : ℝ) / (threshold : ℝ)) +
            if fiberCard target ≠ 0 ∧ fiberCard target < threshold then 1 else 0) := by
      apply Finset.sum_le_sum
      intro target _
      by_cases hzero : fiberCard target = 0
      · simp [normalizedRatio, hzero, hRatioNonneg]
      · by_cases hsmall : fiberCard target < threshold
        · simp only [hzero, ne_eq, not_false_eq_true, hsmall, and_self, if_true]
          exact (min_le_left _ _).trans (le_add_of_nonneg_left hRatioNonneg)
        · have hlarge : threshold ≤ fiberCard target := Nat.le_of_not_gt hsmall
          simp only [hzero, ne_eq, not_false_eq_true, hsmall, and_false, if_false, add_zero]
          apply (min_le_right _ _).trans
          rw [normalizedRatio, if_neg hzero]
          exact div_le_div_of_nonneg_left (by positivity) hThresholdReal
            (by exact_mod_cast hlarge)
    _ = (nonemptySmallFiberCount fiberCard threshold : ℝ) +
        (Fintype.card Target : ℝ) *
          ((externalBound : ℝ) / (threshold : ℝ)) := by
      unfold nonemptySmallFiberCount
      rw [Finset.sum_add_distrib]
      simp [nsmul_eq_mul, add_comm]

/-- Subtracting the fiber itself in the numerator subtracts exactly one on every nonempty
fiber, while the totalized zero-fiber convention remains unchanged. -/
theorem normalizedDifferenceRatio_eq_sub_nonemptyIndicator
    (fiberCard acceptingCard : ℕ) :
    (if fiberCard = 0 then 0
      else ((acceptingCard : ℝ) - (fiberCard : ℝ)) / (fiberCard : ℝ)) =
      normalizedRatio fiberCard acceptingCard -
        if fiberCard = 0 then 0 else 1 := by
  by_cases hzero : fiberCard = 0
  · simp [hzero, normalizedRatio]
  · simp [hzero, normalizedRatio, sub_div]

/-- Summing the real-valued nonempty-fiber indicator gives the cardinality of the nonempty
support. -/
theorem sum_nonemptyIndicator_eq_card_filter
    {Index : Type} [Fintype Index]
    (fiberCard : Index → ℕ) :
    (∑ index, if fiberCard index = 0 then (0 : ℝ) else 1) =
      ((Finset.univ.filter fun index ↦ fiberCard index ≠ 0).card : ℝ) := by
  classical
  calc
    (∑ index, if fiberCard index = 0 then (0 : ℝ) else 1) =
        ∑ index, if fiberCard index ≠ 0 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro index _
      by_cases hzero : fiberCard index = 0 <;> simp [hzero]
    _ = ((Finset.univ.filter fun index ↦ fiberCard index ≠ 0).card : ℝ) := by
      simpa using
        (Finset.sum_boole (R := ℝ) (fun index ↦ fiberCard index ≠ 0)
          (Finset.univ : Finset Index))

/-- A capped normalized row weight can charge at most one for every target in the nonempty
fiber support.  Empty fibers contribute exactly zero under the totalized quotient convention. -/
theorem sum_min_one_normalizedRatio_le_nonemptyFiberCount
    {Target : Type} [Fintype Target]
    (fiberCard : Target → ℕ) (externalBound : ℕ) :
    (∑ target, min 1 (normalizedRatio (fiberCard target) externalBound)) ≤
      ((Finset.univ.filter fun target ↦ fiberCard target ≠ 0).card : ℝ) := by
  classical
  rw [← sum_nonemptyIndicator_eq_card_filter fiberCard]
  apply Finset.sum_le_sum
  intro target _
  by_cases hzero : fiberCard target = 0
  · simp [normalizedRatio, hzero]
  · simp [hzero]

/-- If every accepting carrier injects into its ambient fiber, the sum of its normalized
weights is bounded by the cardinality of the nonempty fiber support. -/
theorem sum_normalizedRatio_le_nonemptyFiberCount
    {Target : Type} [Fintype Target]
    (fiberCard acceptingCard : Target → ℕ)
    (haccepting : ∀ target, acceptingCard target ≤ fiberCard target) :
    (∑ target, normalizedRatio (fiberCard target) (acceptingCard target)) ≤
      ((Finset.univ.filter fun target ↦ fiberCard target ≠ 0).card : ℝ) := by
  classical
  rw [← sum_nonemptyIndicator_eq_card_filter fiberCard]
  apply Finset.sum_le_sum
  intro target _
  by_cases hzero : fiberCard target = 0
  · simp [normalizedRatio, hzero]
  · simpa [hzero] using
      normalizedRatio_le_one_of_le_fiber (haccepting target)

/-- A totalized quotient of two row products. -/
def normalizedProduct
    {Row : Type} [Fintype Row]
    (fiberCard acceptingCard : Row → ℕ) : ℝ :=
  if (∏ row, fiberCard row) = 0 then 0
  else ((∏ row, acceptingCard row : ℕ) : ℝ) /
    ((∏ row, fiberCard row : ℕ) : ℝ)

/-- A totalized quotient of row products is exactly the product of the totalized rowwise
quotients. -/
theorem normalizedProduct_eq_prod_normalizedRatio
    {Row : Type} [Fintype Row] [DecidableEq Row]
    (fiberCard acceptingCard : Row → ℕ) :
    normalizedProduct fiberCard acceptingCard =
      ∏ row, normalizedRatio (fiberCard row) (acceptingCard row) := by
  classical
  by_cases hzero : ∃ row, fiberCard row = 0
  · obtain ⟨row, hrow⟩ := hzero
    have hproduct : (∏ row, fiberCard row) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ row) hrow
    rw [normalizedProduct, if_pos hproduct]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ row)
    simp [normalizedRatio, hrow]
  · have hnonzero : ∀ row, fiberCard row ≠ 0 := by
      intro row hrow
      exact hzero ⟨row, hrow⟩
    have hproduct : (∏ row, fiberCard row) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun row _ ↦ hnonzero row
    rw [normalizedProduct, if_neg hproduct]
    push_cast
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro row _
    simp [normalizedRatio, hnonzero row]

/-- Expanding a summed numerator commutes with totalized normalization by a row-product fiber
cardinality. -/
theorem normalizedRatio_sum_prod_eq_sum_normalizedProduct
    {Row Tuple : Type} [Fintype Row] [DecidableEq Row] [Fintype Tuple]
    (fiberCard : Row → ℕ) (acceptingCard : Tuple → Row → ℕ) :
    normalizedRatio
        (∏ row, fiberCard row)
        (∑ tuple, ∏ row, acceptingCard tuple row) =
      ∑ tuple, normalizedProduct fiberCard (acceptingCard tuple) := by
  classical
  by_cases hproduct : (∏ row, fiberCard row) = 0
  · simp [normalizedRatio, normalizedProduct, hproduct]
  · rw [normalizedRatio, if_neg hproduct]
    simp_rw [normalizedProduct, if_neg hproduct]
    push_cast
    rw [Finset.sum_div]

/-- Summing a product of independent row weights over a dependent product of target types factors
as the product of the rowwise sums. -/
theorem sum_pi_prod_eq_prod_sum
    {Row : Type} [Fintype Row] [DecidableEq Row]
    (Target : Row → Type) [(row : Row) → Fintype (Target row)]
    (weight : (row : Row) → Target row → ℝ) :
    (∑ targets : (row : Row) → Target row,
        ∏ row, weight row (targets row)) =
      ∏ row, ∑ target : Target row, weight row target := by
  exact (Fintype.prod_sum weight).symm

/-- **Exact denominator-preserving row factorization.**  For each coupled tuple, sum the
normalized product over every target vector.  This equals a product of one-coordinate normalized
sums, after which the outer tuple sum remains. -/
theorem sum_normalizedProduct_eq_sum_prod_rowNormalizedSums
    {Row Tuple : Type} [Fintype Row] [DecidableEq Row] [Fintype Tuple]
    (Target : Row → Type) [(row : Row) → Fintype (Target row)]
    (fiberCard acceptingCard : (row : Row) → Target row → Tuple → ℕ) :
    (∑ targets : (row : Row) → Target row,
        ∑ tuple : Tuple,
          normalizedProduct
            (fun row ↦ fiberCard row (targets row) tuple)
            (fun row ↦ acceptingCard row (targets row) tuple)) =
      ∑ tuple : Tuple,
        ∏ row : Row,
          ∑ target : Target row,
            normalizedRatio
              (fiberCard row target tuple)
              (acceptingCard row target tuple) := by
  classical
  simp_rw [normalizedProduct_eq_prod_normalizedRatio]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tuple _
  exact sum_pi_prod_eq_prod_sum Target
    (fun row target ↦ normalizedRatio
      (fiberCard row target tuple) (acceptingCard row target tuple))

/-- Variant where the fiber cardinality is independent of the coupled tuple. -/
theorem sum_normalizedProduct_eq_sum_prod_rowNormalizedSums_constFiber
    {Row Tuple : Type} [Fintype Row] [DecidableEq Row] [Fintype Tuple]
    (Target : Row → Type) [(row : Row) → Fintype (Target row)]
    (fiberCard : (row : Row) → Target row → ℕ)
    (acceptingCard : (row : Row) → Target row → Tuple → ℕ) :
    (∑ targets : (row : Row) → Target row,
        ∑ tuple : Tuple,
          normalizedProduct
            (fun row ↦ fiberCard row (targets row))
            (fun row ↦ acceptingCard row (targets row) tuple)) =
      ∑ tuple : Tuple,
        ∏ row : Row,
          ∑ target : Target row,
            normalizedRatio
              (fiberCard row target)
              (acceptingCard row target tuple) := by
  exact sum_normalizedProduct_eq_sum_prod_rowNormalizedSums Target
    (fun row target _tuple ↦ fiberCard row target) acceptingCard

end

end FormalProof4FHE.FiniteNormalizedRowMoment
