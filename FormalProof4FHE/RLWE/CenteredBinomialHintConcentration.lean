/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.WeightedSquare
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Sum

/-!
# Scalar Concentration of Centered-Binomial Difference Hints

For a uniform binary secret and an additive hint `H = S - Z`, let `p` and `q` be the two
translated scalar noise masses on their common union of supports.  The exact order-two density
cost is

`sum_h (p(h)^2 + q(h)^2) / (p(h) + q(h))`.

This file proves that it is exactly one plus half the triangular discrimination between the
adjacent translates.  Consequently, the centered-binomial adjacent-shift identity

`Delta(p,q) = 2 / (2 eta + 1)`

implies scalar cost `1 + 1 / (2 eta + 1)`, IID degree-`n` cost equal to its `n`-th power, and the
exponential relaxation `exp(n / (2 eta + 1))`.

The theorem is phrased for finite mass tables so that the remaining identification of the
literal bit-pair sampler with the fair binomial coefficients is isolated from the cryptographic
game reduction.
-/

open scoped BigOperators
open OracleComp

namespace FormalProof4FHE.RLWE.CenteredBinomialHintConcentration

noncomputable section

/-- Triangular discrimination of two finite mass tables. -/
def triangularDiscrimination
    {Output : Type} [Fintype Output] (left right : Output → ℝ) : ℝ :=
  ∑ output, (left output - right output) ^ 2 / (left output + right output)

/-- Scalar order-two density cost for a uniform binary hidden value. -/
def binaryHintDensityCost
    {Output : Type} [Fintype Output] (left right : Output → ℝ) : ℝ :=
  ∑ output, (left output ^ 2 + right output ^ 2) /
    (left output + right output)

/-- Pointwise polarization behind the binary hint calculation. -/
theorem binary_density_pointwise
    (left right : ℝ) (hleft : 0 ≤ left) (hright : 0 ≤ right) :
    (left ^ 2 + right ^ 2) / (left + right) =
      (left + right) / 2 + (left - right) ^ 2 / (2 * (left + right)) := by
  by_cases hsum : left + right = 0
  · have hleftZero : left = 0 := by nlinarith
    have hrightZero : right = 0 := by nlinarith
    simp [hleftZero, hrightZero]
  · field_simp
    ring

/-- **Exact binary scalar loss.**  It is one plus half the adjacent triangular
discrimination. -/
theorem binaryHintDensityCost_eq_one_add_half_triangular
    {Output : Type} [Fintype Output]
    (left right : Output → ℝ)
    (hleft : ∀ output, 0 ≤ left output)
    (hright : ∀ output, 0 ≤ right output)
    (hsumLeft : ∑ output, left output = 1)
    (hsumRight : ∑ output, right output = 1) :
    binaryHintDensityCost left right =
      1 + triangularDiscrimination left right / 2 := by
  classical
  unfold binaryHintDensityCost triangularDiscrimination
  calc
    (∑ output,
        (left output ^ 2 + right output ^ 2) /
          (left output + right output)) =
      ∑ output,
        ((left output + right output) / 2 +
          (left output - right output) ^ 2 /
            (2 * (left output + right output))) := by
      apply Finset.sum_congr rfl
      intro output _
      exact binary_density_pointwise
        (left output) (right output) (hleft output) (hright output)
    _ = (∑ output : Output, (left output + right output)) / 2 +
        (∑ output : Output,
          (left output - right output) ^ 2 /
            (left output + right output)) / 2 := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_div]
      · rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro output _
        rw [div_mul_eq_div_div_swap]
    _ = 1 +
        (∑ output : Output,
          (left output - right output) ^ 2 /
            (left output + right output)) / 2 := by
      rw [Finset.sum_add_distrib, hsumLeft, hsumRight]
      ring

/-! ## Uniform ternary secrets -/

/-- Scalar order-two density cost for a uniform ternary hidden value. -/
def ternaryHintDensityCost
    {Output : Type} [Fintype Output]
    (left middle right : Output → ℝ) : ℝ :=
  ∑ output, (left output ^ 2 + middle output ^ 2 + right output ^ 2) /
    (left output + middle output + right output)

/-- A three-point density cost is bounded by its mass baseline plus the two adjacent
triangular-discrimination terms. -/
theorem ternary_density_pointwise_le
    (left middle right : ℝ)
    (hleft : 0 ≤ left) (hmiddle : 0 ≤ middle) (hright : 0 ≤ right) :
    (left ^ 2 + middle ^ 2 + right ^ 2) / (left + middle + right) ≤
      (left + middle + right) / 3 +
        (left - middle) ^ 2 / (left + middle) +
        (middle - right) ^ 2 / (middle + right) := by
  by_cases hlm : left + middle = 0
  · have hleftZero : left = 0 := by nlinarith
    have hmiddleZero : middle = 0 := by nlinarith
    subst left
    subst middle
    norm_num
    have hthird : 0 ≤ right / 3 := div_nonneg hright (by norm_num)
    linarith
  · by_cases hmr : middle + right = 0
    · have hmiddleZero : middle = 0 := by nlinarith
      have hrightZero : right = 0 := by nlinarith
      subst middle
      subst right
      norm_num
      have hthird : 0 ≤ left / 3 := div_nonneg hleft (by norm_num)
      linarith
    · have hlmPos : 0 < left + middle :=
        lt_of_le_of_ne (add_nonneg hleft hmiddle) (Ne.symm hlm)
      have hmrPos : 0 < middle + right :=
        lt_of_le_of_ne (add_nonneg hmiddle hright) (Ne.symm hmr)
      have hsumPos : 0 < left + middle + right := by nlinarith
      have hpolarization :
          (left ^ 2 + middle ^ 2 + right ^ 2) / (left + middle + right) =
            (left + middle + right) / 3 +
              ((left - middle) ^ 2 + (left - right) ^ 2 +
                (middle - right) ^ 2) / (3 * (left + middle + right)) := by
        field_simp
        ring
      rw [hpolarization]
      have hlongDifference :
          (left - middle) ^ 2 + (left - right) ^ 2 + (middle - right) ^ 2 ≤
            3 * ((left - middle) ^ 2 + (middle - right) ^ 2) := by
        nlinarith [sq_nonneg ((left - middle) - (middle - right))]
      have hvariance :
          ((left - middle) ^ 2 + (left - right) ^ 2 + (middle - right) ^ 2) /
              (3 * (left + middle + right)) ≤
            ((left - middle) ^ 2 + (middle - right) ^ 2) /
              (left + middle + right) := by
        calc
          _ ≤ (3 * ((left - middle) ^ 2 + (middle - right) ^ 2)) /
                (3 * (left + middle + right)) :=
              div_le_div_of_nonneg_right hlongDifference (by positivity)
          _ = _ := by field_simp
      have hleftDenominator :
          (left - middle) ^ 2 / (left + middle + right) ≤
            (left - middle) ^ 2 / (left + middle) := by
        exact div_le_div₀ (sq_nonneg _) le_rfl hlmPos (by linarith)
      have hrightDenominator :
          (middle - right) ^ 2 / (left + middle + right) ≤
            (middle - right) ^ 2 / (middle + right) := by
        exact div_le_div₀ (sq_nonneg _) le_rfl hmrPos (by linarith)
      calc
        _ ≤ (left + middle + right) / 3 +
            ((left - middle) ^ 2 + (middle - right) ^ 2) /
              (left + middle + right) := by linarith
        _ = (left + middle + right) / 3 +
            (left - middle) ^ 2 / (left + middle + right) +
            (middle - right) ^ 2 / (left + middle + right) := by
              rw [add_div]
              ring
        _ ≤ _ := by linarith

/-- **Generic ternary adjacent-shift bound.**  The cost of hiding a uniform ternary value is
at most one plus the triangular discriminations of the two adjacent translates. -/
theorem ternaryHintDensityCost_le_one_add_adjacent
    {Output : Type} [Fintype Output]
    (left middle right : Output → ℝ)
    (hleft : ∀ output, 0 ≤ left output)
    (hmiddle : ∀ output, 0 ≤ middle output)
    (hright : ∀ output, 0 ≤ right output)
    (hsumLeft : ∑ output, left output = 1)
    (hsumMiddle : ∑ output, middle output = 1)
    (hsumRight : ∑ output, right output = 1) :
    ternaryHintDensityCost left middle right ≤
      1 + triangularDiscrimination left middle +
        triangularDiscrimination middle right := by
  classical
  unfold ternaryHintDensityCost triangularDiscrimination
  calc
    _ ≤ ∑ output,
        ((left output + middle output + right output) / 3 +
          (left output - middle output) ^ 2 / (left output + middle output) +
          (middle output - right output) ^ 2 /
            (middle output + right output)) := by
          apply Finset.sum_le_sum
          intro output _
          exact ternary_density_pointwise_le _ _ _
            (hleft output) (hmiddle output) (hright output)
    _ = 1 +
        (∑ output,
          (left output - middle output) ^ 2 / (left output + middle output)) +
        ∑ output,
          (middle output - right output) ^ 2 / (middle output + right output) := by
          simp_rw [Finset.sum_add_distrib]
          rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
            hsumLeft, hsumMiddle, hsumRight]
          ring

/-! ## The exact fair-binomial adjacent-shift calculation -/

/-- The centered second moment of the fair-binomial coefficient table.  This is the
combinatorial identity `sum_i choose(n,i) (n-2i)^2 = n 2^n`. -/
theorem centeredChooseSquareSum (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ((n : ℝ) - 2 * (i : ℝ)) ^ 2 =
      (n : ℝ) * (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_choose_succ_mul
        (R := ℝ) (f := fun i _ => (((n + 1 : ℕ) : ℝ) - 2 * (i : ℝ)) ^ 2) n]
      rw [← Finset.sum_add_distrib]
      calc
        ∑ i ∈ Finset.range (n + 1),
            ((n.choose i : ℝ) * (((n + 1 : ℕ) : ℝ) - 2 * (i : ℝ)) ^ 2 +
              (n.choose i : ℝ) *
                (((n + 1 : ℕ) : ℝ) - 2 * ((i + 1 : ℕ) : ℝ)) ^ 2) =
          ∑ i ∈ Finset.range (n + 1),
            (2 * ((n.choose i : ℝ) * ((n : ℝ) - 2 * (i : ℝ)) ^ 2) +
              2 * (n.choose i : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i _
            push_cast
            ring
        _ = 2 * (∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * ((n : ℝ) - 2 * (i : ℝ)) ^ 2) +
            2 * (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ = ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (n + 1) := by
          rw [ih]
          have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) =
              (2 : ℝ) ^ n := by
            exact_mod_cast Nat.sum_range_choose n
          rw [hsum, pow_succ]
          push_cast
          ring

/-- First translate of the fair-binomial table of order `2 eta`, extended by one zero
endpoint so that it shares a type with its adjacent translate. -/
def fairBinomialLeftMass (eta : ℕ) (index : Fin (2 * eta + 2)) : ℝ :=
  (Nat.choose (2 * eta) index.val : ℝ) / (2 : ℝ) ^ (2 * eta)

/-- Adjacent translate of `fairBinomialLeftMass`. -/
def fairBinomialRightMass (eta : ℕ) (index : Fin (2 * eta + 2)) : ℝ :=
  if index.val = 0 then 0 else
    (Nat.choose (2 * eta) (index.val - 1) : ℝ) / (2 : ℝ) ^ (2 * eta)

theorem fairBinomialLeftMass_nonneg (eta : ℕ) (index : Fin (2 * eta + 2)) :
    0 ≤ fairBinomialLeftMass eta index := by
  unfold fairBinomialLeftMass
  positivity

theorem fairBinomialRightMass_nonneg (eta : ℕ) (index : Fin (2 * eta + 2)) :
    0 ≤ fairBinomialRightMass eta index := by
  unfold fairBinomialRightMass
  split <;> positivity

theorem sum_fairBinomialLeftMass (eta : ℕ) :
    ∑ index, fairBinomialLeftMass eta index = 1 := by
  change (∑ index : Fin (2 * eta + 2),
    (fun j : ℕ => (Nat.choose (2 * eta) j : ℝ) /
      (2 : ℝ) ^ (2 * eta)) index) = 1
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (Nat.choose (2 * eta) j : ℝ) / (2 : ℝ) ^ (2 * eta))
    (2 * eta + 2)]
  rw [← Finset.sum_div, Finset.sum_range_succ]
  simp only [Nat.choose_eq_zero_of_lt (by omega : 2 * eta < 2 * eta + 1),
    Nat.cast_zero, add_zero]
  have hsum : (∑ index ∈ Finset.range (2 * eta + 1),
      (Nat.choose (2 * eta) index : ℝ)) = (2 : ℝ) ^ (2 * eta) := by
    exact_mod_cast Nat.sum_range_choose (2 * eta)
  rw [hsum]
  norm_num

theorem sum_fairBinomialRightMass (eta : ℕ) :
    ∑ index, fairBinomialRightMass eta index = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [fairBinomialRightMass, Fin.val_zero, ↓reduceIte, zero_add, Fin.val_succ,
    Nat.succ_ne_zero, Nat.add_sub_cancel]
  change (∑ index : Fin (2 * eta + 1),
    (fun j : ℕ => (Nat.choose (2 * eta) j : ℝ) /
      (2 : ℝ) ^ (2 * eta)) index) = 1
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (Nat.choose (2 * eta) j : ℝ) / (2 : ℝ) ^ (2 * eta))
    (2 * eta + 1), ← Finset.sum_div]
  have hsum : (∑ index ∈ Finset.range (2 * eta + 1),
      (Nat.choose (2 * eta) index : ℝ)) = (2 : ℝ) ^ (2 * eta) := by
    exact_mod_cast Nat.sum_range_choose (2 * eta)
  rw [hsum]
  norm_num

/-- The adjacent fair-binomial masses obey the exact affine score equation. -/
theorem fairBinomial_score_relation (eta : ℕ) (index : Fin (2 * eta + 2)) :
    (((2 * eta + 1 : ℕ) : ℝ) *
        (fairBinomialLeftMass eta index - fairBinomialRightMass eta index)) =
      (((2 * eta + 1 : ℕ) : ℝ) - 2 * (index.val : ℝ)) *
        (fairBinomialLeftMass eta index + fairBinomialRightMass eta index) := by
  by_cases hi : index.val = 0
  · simp [fairBinomialLeftMass, fairBinomialRightMass, hi]
  · obtain ⟨j, hjEq⟩ := Nat.exists_eq_succ_of_ne_zero hi
    have hj : j ≤ 2 * eta := by omega
    have hchooseNat := Nat.choose_succ_right_eq (2 * eta) j
    have hchoose :
        (Nat.choose (2 * eta) (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) =
          (Nat.choose (2 * eta) j : ℝ) * (((2 * eta - j : ℕ) : ℝ)) := by
      exact_mod_cast hchooseNat
    rw [Nat.cast_sub hj] at hchoose
    rw [hjEq]
    simp only [fairBinomialLeftMass, fairBinomialRightMass, hjEq,
      Nat.succ_ne_zero, ↓reduceIte]
    have hpow : (2 : ℝ) ^ (2 * eta) ≠ 0 := by positivity
    field_simp [hpow]
    push_cast at hchoose ⊢
    nlinarith

/-- The score equation turns every triangular-discrimination summand into a quadratic
fair-binomial score. -/
theorem fairBinomial_quotient_eq_weighted_score
    (eta : ℕ) (index : Fin (2 * eta + 2)) :
    (fairBinomialLeftMass eta index - fairBinomialRightMass eta index) ^ 2 /
        (fairBinomialLeftMass eta index + fairBinomialRightMass eta index) =
      (fairBinomialLeftMass eta index + fairBinomialRightMass eta index) *
        (((2 * eta + 1 : ℕ) : ℝ) - 2 * (index.val : ℝ)) ^ 2 /
          (((2 * eta + 1 : ℕ) : ℝ) ^ 2) := by
  have hrel := fairBinomial_score_relation eta index
  have hA : (((2 * eta + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  by_cases hsum : fairBinomialLeftMass eta index + fairBinomialRightMass eta index = 0
  · have hdiff : fairBinomialLeftMass eta index - fairBinomialRightMass eta index = 0 := by
      apply mul_left_cancel₀ hA
      simpa [hsum] using hrel
    simp [hsum, hdiff]
  · have hsquare := congrArg (fun x : ℝ => x ^ 2) hrel
    field_simp [hsum, hA]
    nlinarith

/-- Exact unnormalised quadratic score of the two adjacent tables. -/
theorem fairBinomial_score_weighted_sum (eta : ℕ) :
    ∑ index : Fin (2 * eta + 2),
        (fairBinomialLeftMass eta index + fairBinomialRightMass eta index) *
          (((2 * eta + 1 : ℕ) : ℝ) - 2 * (index.val : ℝ)) ^ 2 =
      2 * (((2 * eta + 1 : ℕ) : ℝ)) := by
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  rw [Fin.sum_univ_castSucc (fun index : Fin (2 * eta + 2) =>
    fairBinomialLeftMass eta index *
      (((2 * eta + 1 : ℕ) : ℝ) - 2 * (index.val : ℝ)) ^ 2)]
  rw [Fin.sum_univ_succ (fun index : Fin (2 * eta + 2) =>
    fairBinomialRightMass eta index *
      (((2 * eta + 1 : ℕ) : ℝ) - 2 * (index.val : ℝ)) ^ 2)]
  simp only [fairBinomialLeftMass, fairBinomialRightMass, Fin.val_last,
    Fin.val_castSucc, Nat.choose_eq_zero_of_lt
      (by omega : 2 * eta < 2 * eta + 1), Nat.cast_zero, zero_div, zero_mul,
    add_zero, Fin.val_zero, zero_add, Fin.val_succ, Nat.succ_ne_zero,
    ↓reduceIte, Nat.add_sub_cancel]
  rw [← Finset.sum_add_distrib]
  change (∑ index : Fin (2 * eta + 1),
      (fun j : ℕ =>
        ((Nat.choose (2 * eta) j : ℝ) / (2 : ℝ) ^ (2 * eta) *
            (((2 * eta + 1 : ℕ) : ℝ) - 2 * (j : ℝ)) ^ 2 +
          (Nat.choose (2 * eta) j : ℝ) / (2 : ℝ) ^ (2 * eta) *
            (((2 * eta + 1 : ℕ) : ℝ) - 2 * ((j + 1 : ℕ) : ℝ)) ^ 2)) index) =
      2 * (((2 * eta + 1 : ℕ) : ℝ))
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ =>
      ((Nat.choose (2 * eta) j : ℝ) / (2 : ℝ) ^ (2 * eta) *
          (((2 * eta + 1 : ℕ) : ℝ) - 2 * (j : ℝ)) ^ 2 +
        (Nat.choose (2 * eta) j : ℝ) / (2 : ℝ) ^ (2 * eta) *
          (((2 * eta + 1 : ℕ) : ℝ) - 2 * ((j + 1 : ℕ) : ℝ)) ^ 2))
    (2 * eta + 1)]
  calc
    ∑ i ∈ Finset.range (2 * eta + 1),
        ((Nat.choose (2 * eta) i : ℝ) / (2 : ℝ) ^ (2 * eta) *
            (((2 * eta + 1 : ℕ) : ℝ) - 2 * (i : ℝ)) ^ 2 +
          (Nat.choose (2 * eta) i : ℝ) / (2 : ℝ) ^ (2 * eta) *
            (((2 * eta + 1 : ℕ) : ℝ) - 2 * ((i + 1 : ℕ) : ℝ)) ^ 2) =
      ∑ i ∈ Finset.range (2 * eta + 1),
        (2 * ((Nat.choose (2 * eta) i : ℝ) / (2 : ℝ) ^ (2 * eta) *
            (((2 * eta : ℕ) : ℝ) - 2 * (i : ℝ)) ^ 2) +
          2 * ((Nat.choose (2 * eta) i : ℝ) / (2 : ℝ) ^ (2 * eta))) := by
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      ring
    _ = 2 * ((2 * eta : ℕ) : ℝ) + 2 := by
      rw [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]
      have hsum : (∑ i ∈ Finset.range (2 * eta + 1),
          (Nat.choose (2 * eta) i : ℝ)) = (2 : ℝ) ^ (2 * eta) := by
        exact_mod_cast Nat.sum_range_choose (2 * eta)
      have hpow : (2 : ℝ) ^ (2 * eta) ≠ 0 := by positivity
      have hmoment :
          (∑ i ∈ Finset.range (2 * eta + 1),
            (Nat.choose (2 * eta) i : ℝ) / (2 : ℝ) ^ (2 * eta) *
              (((2 * eta : ℕ) : ℝ) - 2 * (i : ℝ)) ^ 2) =
            ((2 * eta : ℕ) : ℝ) := by
        calc
          _ = (∑ i ∈ Finset.range (2 * eta + 1),
                (Nat.choose (2 * eta) i : ℝ) *
                  (((2 * eta : ℕ) : ℝ) - 2 * (i : ℝ)) ^ 2) /
                (2 : ℝ) ^ (2 * eta) := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro i _
              ring
          _ = ((2 * eta : ℕ) : ℝ) := by
              rw [centeredChooseSquareSum (2 * eta)]
              field_simp [hpow]
      rw [hmoment, ← Finset.sum_div, hsum]
      field_simp [hpow]
    _ = 2 * (((2 * eta + 1 : ℕ) : ℝ)) := by
      push_cast
      ring

/-- **Exact adjacent-CBD triangular discrimination.** -/
theorem fairBinomial_triangularDiscrimination (eta : ℕ) :
    triangularDiscrimination
      (fairBinomialLeftMass eta) (fairBinomialRightMass eta) =
      2 / (2 * (eta : ℝ) + 1) := by
  unfold triangularDiscrimination
  simp_rw [fairBinomial_quotient_eq_weighted_score]
  rw [← Finset.sum_div, fairBinomial_score_weighted_sum]
  push_cast
  have hden : (2 * (eta : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hden]

/-- Finite certificate for the exact adjacent-shift CBD calculation.  The final field is the
single scalar combinatorial identity supplied by the fair-binomial coefficient recurrence. -/
structure AdjacentCBDCertificate (eta : ℕ) (Output : Type) [Fintype Output] where
  left : Output → ℝ
  right : Output → ℝ
  left_nonneg : ∀ output, 0 ≤ left output
  right_nonneg : ∀ output, 0 ≤ right output
  sum_left : ∑ output, left output = 1
  sum_right : ∑ output, right output = 1
  triangular_eq :
    triangularDiscrimination left right = 2 / (2 * (eta : ℝ) + 1)

/-- The literal fair-binomial coefficient tables furnish an adjacent-CBD certificate; no
numerically selected constant is involved. -/
def fairBinomialAdjacentCBDCertificate (eta : ℕ) :
    AdjacentCBDCertificate eta (Fin (2 * eta + 2)) where
  left := fairBinomialLeftMass eta
  right := fairBinomialRightMass eta
  left_nonneg := fairBinomialLeftMass_nonneg eta
  right_nonneg := fairBinomialRightMass_nonneg eta
  sum_left := sum_fairBinomialLeftMass eta
  sum_right := sum_fairBinomialRightMass eta
  triangular_eq := fairBinomial_triangularDiscrimination eta

/-- Certificate for three normalized translates whose two adjacent CBD discriminations have
the exact fair-binomial value. -/
structure TernaryAdjacentCBDCertificate (eta : ℕ) (Output : Type) [Fintype Output] where
  left : Output → ℝ
  middle : Output → ℝ
  right : Output → ℝ
  left_nonneg : ∀ output, 0 ≤ left output
  middle_nonneg : ∀ output, 0 ≤ middle output
  right_nonneg : ∀ output, 0 ≤ right output
  sum_left : ∑ output, left output = 1
  sum_middle : ∑ output, middle output = 1
  sum_right : ∑ output, right output = 1
  left_middle_triangular_eq :
    triangularDiscrimination left middle = 2 / (2 * (eta : ℝ) + 1)
  middle_right_triangular_eq :
    triangularDiscrimination middle right = 2 / (2 * (eta : ℝ) + 1)

/-- A certified adjacent CBD table has scalar binary density cost
`1 + 1/(2 eta + 1)`. -/
theorem binaryHintDensityCost_eq_of_adjacentCBD
    {eta : ℕ} {Output : Type} [Fintype Output]
    (certificate : AdjacentCBDCertificate eta Output) :
    binaryHintDensityCost certificate.left certificate.right =
      1 + 1 / (2 * (eta : ℝ) + 1) := by
  rw [binaryHintDensityCost_eq_one_add_half_triangular
    certificate.left certificate.right certificate.left_nonneg
    certificate.right_nonneg certificate.sum_left certificate.sum_right,
    certificate.triangular_eq]
  ring

/-- Exact one-coordinate density cost for a uniform binary value hidden by fair-binomial CBD
noise of width `eta`. -/
theorem binaryHintDensityCost_fairBinomial (eta : ℕ) :
    binaryHintDensityCost
        (fairBinomialLeftMass eta) (fairBinomialRightMass eta) =
      1 + 1 / (2 * (eta : ℝ) + 1) :=
  binaryHintDensityCost_eq_of_adjacentCBD
    (fairBinomialAdjacentCBDCertificate eta)

/-- A uniform ternary value hidden by adjacent CBD translates has scalar cost at most
`1 + 4/(2 eta + 1)`. -/
theorem ternaryHintDensityCost_le_of_adjacentCBD
    {eta : ℕ} {Output : Type} [Fintype Output]
    (certificate : TernaryAdjacentCBDCertificate eta Output) :
    ternaryHintDensityCost certificate.left certificate.middle certificate.right ≤
      1 + 4 / (2 * (eta : ℝ) + 1) := by
  calc
    _ ≤ 1 + triangularDiscrimination certificate.left certificate.middle +
        triangularDiscrimination certificate.middle certificate.right :=
      ternaryHintDensityCost_le_one_add_adjacent
        certificate.left certificate.middle certificate.right
        certificate.left_nonneg certificate.middle_nonneg certificate.right_nonneg
        certificate.sum_left certificate.sum_middle certificate.sum_right
    _ = 1 + 4 / (2 * (eta : ℝ) + 1) := by
      rw [certificate.left_middle_triangular_eq,
        certificate.middle_right_triangular_eq]
      ring

/-- Tensorization of the exact binary CBD scalar cost. -/
theorem binary_product_densityCost_eq
    {A : Type} [Fintype A]
    (degree eta : ℕ) (actual reference : ProbComp A)
    (hScalar : FormalProof4FHE.WeightedSquare.densitySecondMoment actual reference =
      1 + 1 / (2 * (eta : ℝ) + 1)) :
    FormalProof4FHE.WeightedSquare.densitySecondMoment
        (ProbComp.sampleIID degree actual)
        (ProbComp.sampleIID degree reference) =
      (1 + 1 / (2 * (eta : ℝ) + 1)) ^ degree := by
  rw [FormalProof4FHE.WeightedSquare.densitySecondMoment_sampleIID, hScalar]

/-- Exponential form of the binary CBD product bound. -/
theorem binary_product_densityCost_le_exp
    {A : Type} [Fintype A]
    (degree eta : ℕ) (actual reference : ProbComp A)
    (hScalar : FormalProof4FHE.WeightedSquare.densitySecondMoment actual reference =
      1 + 1 / (2 * (eta : ℝ) + 1)) :
    FormalProof4FHE.WeightedSquare.densitySecondMoment
        (ProbComp.sampleIID degree actual)
        (ProbComp.sampleIID degree reference) ≤
      Real.exp ((degree : ℝ) / (2 * (eta : ℝ) + 1)) := by
  rw [FormalProof4FHE.WeightedSquare.densitySecondMoment_sampleIID, hScalar]
  have hdenom : 0 ≤ (2 * (eta : ℝ) + 1) := by positivity
  convert FormalProof4FHE.WeightedSquare.one_add_pow_le_exp_nat_mul
    degree (1 / (2 * (eta : ℝ) + 1)) (one_div_nonneg.mpr hdenom) using 1
  ring_nf

/-- Product/exponential form of the ternary CBD concentration bound. -/
theorem ternary_product_densityCost_le_exp
    {A : Type} [Fintype A]
    (degree eta : ℕ) (actual reference : ProbComp A)
    (hScalar : FormalProof4FHE.WeightedSquare.densitySecondMoment actual reference ≤
      1 + 4 / (2 * (eta : ℝ) + 1)) :
    FormalProof4FHE.WeightedSquare.densitySecondMoment
        (ProbComp.sampleIID degree actual)
        (ProbComp.sampleIID degree reference) ≤
      Real.exp (4 * (degree : ℝ) / (2 * (eta : ℝ) + 1)) := by
  rw [FormalProof4FHE.WeightedSquare.densitySecondMoment_sampleIID]
  have hnonneg := FormalProof4FHE.WeightedSquare.densitySecondMoment_nonneg actual reference
  calc
    FormalProof4FHE.WeightedSquare.densitySecondMoment actual reference ^ degree ≤
        (1 + 4 / (2 * (eta : ℝ) + 1)) ^ degree :=
      pow_le_pow_left₀ hnonneg hScalar degree
    _ ≤ Real.exp ((degree : ℝ) * (4 / (2 * (eta : ℝ) + 1))) := by
      apply FormalProof4FHE.WeightedSquare.one_add_pow_le_exp_nat_mul
      positivity
    _ = Real.exp (4 * (degree : ℝ) / (2 * (eta : ℝ) + 1)) := by
      congr 1
      ring

end

end FormalProof4FHE.RLWE.CenteredBinomialHintConcentration
