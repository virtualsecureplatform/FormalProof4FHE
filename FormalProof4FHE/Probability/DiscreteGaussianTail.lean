/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.ModularGaussian
import Mathlib.Analysis.SpecificLimits.Basic
import FormalProof4FHE.TFHE.NoiseBounds
import FormalProof4FHE.Probability.FinitePMFCompiler
import VCVio.CryptoFoundations.Asymptotics.Negligible

/-!
# A scalar tail bound for the centered integer discrete Gaussian

At positive integer standard deviation `s`, the tail above `s^2` is bounded
by `4 * exp (-s^2/2)`. The proof uses normalization at zero, symmetry, and an
explicit geometric majorant. These are ideal mathematical PMFs; an executable
sampler still needs its own approximation certificate and a polynomial cost proof.
-/

open scoped BigOperators ENNReal

namespace FormalProof4FHE.DiscreteGaussianTail

open LatticeCrypto

/-- Real probability mass outside a centered integer interval. -/
noncomputable def tailMass (sigma : ℝ) (bound : ℕ) : ℝ :=
  ∑' value : ℤ, if bound < value.natAbs then discreteGaussianPMF sigma 0 value else 0

/-- The zero weight alone makes the centered normalizing constant at least one. -/
theorem normalizer_ge_one (sigma : ℝ) (hsigma : 0 < sigma) :
    1 ≤ discreteGaussianSum sigma 0 := by
  have h := (discreteGaussianSum_summable sigma 0 hsigma).sum_le_tsum
    ({0} : Finset ℤ) (fun value _ ↦ discreteGaussianWeight_nonneg sigma 0 value)
  simpa [discreteGaussianSum, discreteGaussianWeight] using h

/-- The normalized mass is at most its unnormalized Gaussian weight. -/
theorem mass_le_weight (sigma : ℝ) (hsigma : 0 < sigma) (value : ℤ) :
    discreteGaussianPMF sigma 0 value ≤ discreteGaussianWeight sigma 0 value := by
  exact div_le_self (discreteGaussianWeight_nonneg sigma 0 value)
    (normalizer_ge_one sigma hsigma)

/-- A shifted Gaussian tail is bounded pointwise by a fixed exponential times `exp (-k)`. -/
theorem mass_square_tail_le (width : ℕ) (hwidth : 0 < width) (index : ℕ) :
    discreteGaussianPMF width 0 ((width ^ 2 + index + 1 : ℕ) : ℤ) ≤
      Real.exp (-(width : ℝ) ^ 2 / 2) * Real.exp (-(index : ℝ)) := by
  have hwidthReal : (0 : ℝ) < width := Nat.cast_pos.mpr hwidth
  apply (mass_le_weight width hwidthReal _).trans
  rw [discreteGaussianWeight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  have hden : (0 : ℝ) < 2 * (width : ℝ) ^ 2 := by positivity
  have hidentity :
      -((width : ℝ) ^ 2 + index + 1) ^ 2 / (2 * (width : ℝ) ^ 2) =
      -(width : ℝ) ^ 2 / 2 - (index + 1) -
        ((index : ℝ) + 1) ^ 2 / (2 * (width : ℝ) ^ 2) := by
    field_simp
    ring
  simp only [sub_zero]
  rw [hidentity]
  linarith [div_nonneg (sq_nonneg ((index : ℝ) + 1)) hden.le]

/-- `exp (-1)` is at most one half, by the elementary exponential lower bound. -/
theorem exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  have hexp : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hproduct : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-1)]

/-- A convenient coarse bound for the geometric majorant. -/
theorem tsum_exp_neg_nat_le_two :
    (∑' index : ℕ, Real.exp (-(index : ℝ))) ≤ 2 := by
  have hr := exp_neg_one_le_half
  have hpow (index : ℕ) : Real.exp (-(index : ℝ)) = Real.exp (-1) ^ index := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [hpow]
  rw [tsum_geometric_of_lt_one (Real.exp_nonneg _) (by linarith : Real.exp (-1) < 1)]
  rw [inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - Real.exp (-1))]
  linarith

/-- The positive half of the tail above the squared integer width. -/
theorem positive_tail_le (width : ℕ) (hwidth : 0 < width) :
    (∑' index : ℕ, discreteGaussianPMF width 0 ((width ^ 2 + index + 1 : ℕ) : ℤ)) ≤
      2 * Real.exp (-(width : ℝ) ^ 2 / 2) := by
  have hwidthReal : (0 : ℝ) < width := Nat.cast_pos.mpr hwidth
  have hmass : Summable (fun index : ℕ ↦
      discreteGaussianPMF width 0 ((width ^ 2 + index + 1 : ℕ) : ℤ)) := by
    apply (discreteGaussianPMF_summable width 0 hwidthReal).comp_injective
    intro first second heq
    exact Nat.add_left_cancel (Nat.add_right_cancel (Int.ofNat_inj.mp heq))
  calc
    _ ≤ ∑' index : ℕ, Real.exp (-(width : ℝ) ^ 2 / 2) * Real.exp (-(index : ℝ)) :=
      hmass.tsum_le_tsum (mass_square_tail_le width hwidth)
        (Real.summable_exp_neg_nat.mul_left _)
    _ = Real.exp (-(width : ℝ) ^ 2 / 2) * ∑' index : ℕ, Real.exp (-(index : ℝ)) :=
      tsum_mul_left
    _ ≤ Real.exp (-(width : ℝ) ^ 2 / 2) * 2 :=
      mul_le_mul_of_nonneg_left tsum_exp_neg_nat_le_two (Real.exp_nonneg _)
    _ = _ := by ring

/-- The nonnegative tail terms are summable because they are bounded by the full PMF. -/
theorem tail_terms_summable (sigma : ℝ) (hsigma : 0 < sigma) (bound : ℕ) :
    Summable (fun value : ℤ ↦
      if bound < value.natAbs then discreteGaussianPMF sigma 0 value else 0) := by
  apply Summable.of_nonneg_of_le _ _ (discreteGaussianPMF_summable sigma 0 hsigma)
  · intro value
    split_ifs
    · exact discreteGaussianPMF_nonneg sigma 0 hsigma value
    · exact le_rfl
  · intro value
    split_ifs
    · exact le_rfl
    · exact discreteGaussianPMF_nonneg sigma 0 hsigma value

/-- Symmetry and deletion of the finite zero prefix identify the two signed tails exactly. -/
theorem tailMass_eq_two_mul_positive (sigma : ℝ) (hsigma : 0 < sigma) (bound : ℕ) :
    tailMass sigma bound =
      2 * ∑' index : ℕ, discreteGaussianPMF sigma 0 ((bound + index + 1 : ℕ) : ℤ) := by
  classical
  let term : ℤ → ℝ := fun value ↦
    if bound < value.natAbs then discreteGaussianPMF sigma 0 value else 0
  let positive : ℕ → ℝ := fun index ↦ term ((index : ℤ) + 1)
  have hterms : Summable term := tail_terms_summable sigma hsigma bound
  have hpositive : Summable positive := by
    have hinjective : Function.Injective (fun index : ℕ ↦ (index : ℤ) + 1) := by
      intro first second heq
      exact Int.ofNat_inj.mp (add_right_cancel heq)
    exact hterms.comp_injective hinjective
  have hnegative : Summable (fun index : ℕ ↦ term (-((index : ℤ) + 1))) := by
    have hinjective : Function.Injective (fun index : ℕ ↦ -((index : ℤ) + 1)) := by
      intro first second heq
      exact Int.ofNat_inj.mp (add_right_cancel (neg_injective heq))
    exact hterms.comp_injective hinjective
  have hpositiveValue (index : ℕ) : positive index =
      if bound < index + 1 then discreteGaussianPMF sigma 0 ((index + 1 : ℕ) : ℤ) else 0 := by
    dsimp only [positive, term]
    rw [show (index : ℤ) + 1 = ((index + 1 : ℕ) : ℤ) by norm_cast]
    simp only [Int.natAbs_natCast]
    rfl
  have hprefix : ∑ index ∈ Finset.range bound, positive index = 0 := by
    apply Finset.sum_eq_zero
    intro index hindex
    have hindex' := Finset.mem_range.mp hindex
    rw [hpositiveValue, if_neg (by omega)]
  have hshift (index : ℕ) : positive (index + bound) =
      discreteGaussianPMF sigma 0 ((bound + index + 1 : ℕ) : ℤ) := by
    rw [hpositiveValue, if_pos (by omega)]
    congr 2
    omega
  have htail : (∑' index : ℕ, positive index) =
      ∑' index : ℕ, discreteGaussianPMF sigma 0 ((bound + index + 1 : ℕ) : ℤ) := by
    rw [← hpositive.sum_add_tsum_nat_add bound, hprefix, zero_add]
    exact tsum_congr hshift
  have hnegativeValue (index : ℕ) : term (-((index : ℤ) + 1)) = positive index := by
    simp only [term, positive, Int.natAbs_neg, ModularGaussian.discreteGaussianPMF_zero_neg]
  have hzero : term 0 = 0 := by simp [term]
  change (∑' value : ℤ, term value) = _
  rw [tsum_of_add_one_of_neg_add_one hpositive hnegative, hzero, add_zero]
  simp_rw [hnegativeValue]
  change (∑' index : ℕ, positive index) + (∑' index : ℕ, positive index) = _
  rw [htail]
  ring

/-- Concrete scalar Gaussian tail bound at the correctness budget of the one-key family. -/
theorem tailMass_square_le (width : ℕ) (hwidth : 0 < width) :
    tailMass width (width ^ 2) ≤ 4 * Real.exp (-(width : ℝ) ^ 2 / 2) := by
  rw [tailMass_eq_two_mul_positive width (Nat.cast_pos.mpr hwidth)]
  have h := mul_le_mul_of_nonneg_left (positive_tail_le width hwidth) (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

/-- Event probability of the ideal integer Gaussian is the real tail mass. -/
theorem probEvent_integer_tail_eq (sigma : ℝ) (hsigma : 0 < sigma) (bound : ℕ) :
    Pr[(fun value : ℤ ↦ bound < value.natAbs) | discreteGaussianDist sigma 0 hsigma] =
      ENNReal.ofReal (tailMass sigma bound) := by
  classical
  rw [probEvent_eq_tsum_ite]
  simp only [PMF.probOutput_eq_apply]
  change (∑' value : ℤ, if bound < value.natAbs then
    ENNReal.ofReal (discreteGaussianPMF sigma 0 value) else 0) = _
  have hterm (value : ℤ) :
      (if bound < value.natAbs then ENNReal.ofReal (discreteGaussianPMF sigma 0 value) else 0) =
      ENNReal.ofReal (if bound < value.natAbs then discreteGaussianPMF sigma 0 value else 0) := by
    split_ifs <;> simp
  simp_rw [hterm]
  exact (ENNReal.ofReal_tsum_of_nonneg (by
    intro value
    split_ifs
    · exact discreteGaussianPMF_nonneg sigma 0 hsigma value
    · exact le_rfl) (tail_terms_summable sigma hsigma bound)).symm

/-- Modular reduction can only decrease centered magnitude, so its tail is no larger. -/
theorem probEvent_modular_tail_le (q width : ℕ) [NeZero q] (hwidth : 0 < width) :
    Pr[(fun value : ZMod q ↦ width ^ 2 < (LatticeCrypto.centeredRepr value).natAbs) |
      ModularGaussian.distribution q width (Nat.cast_pos.mpr hwidth)] ≤
      ENNReal.ofReal (4 * Real.exp (-(width : ℝ) ^ 2 / 2)) := by
  rw [ModularGaussian.distribution, probEvent_map]
  apply le_trans (b := Pr[(fun value : ℤ ↦ width ^ 2 < value.natAbs) |
    discreteGaussianDist width 0 (Nat.cast_pos.mpr hwidth)])
  · rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
    apply ENNReal.tsum_le_tsum
    intro value
    change (if width ^ 2 < (LatticeCrypto.centeredRepr (value : ZMod q)).natAbs then _ else 0) ≤ _
    by_cases hbad : width ^ 2 < (LatticeCrypto.centeredRepr (value : ZMod q)).natAbs
    · rw [if_pos hbad, if_pos (lt_of_lt_of_le hbad
        (TFHE.NoiseBounds.centeredRepr_intCast_natAbs_le value))]
    · rw [if_neg hbad]
      exact zero_le
  · rw [probEvent_integer_tail_eq]
    exact ENNReal.ofReal_le_ofReal (tailMass_square_le width hwidth)

/-- Changing a PMF can increase one event probability by at most its extended TV distance. -/
theorem probEvent_le_add_etvDist {Output : Type} (left right : PMF Output)
    (event : Output → Prop) :
    Pr[event | left] ≤ Pr[event | right] + left.etvDist right := by
  classical
  let mark : Output → Option PUnit := fun value ↦ if event value then some () else none
  have hmark (distribution : PMF Output) :
      (mark <$> distribution) (some ()) = Pr[event | distribution] := by
    rw [PMF.monad_map_eq_map, PMF.map_apply, probEvent_eq_tsum_ite]
    simp only [PMF.probOutput_eq_apply]
    apply tsum_congr
    intro value
    by_cases hevent : event value <;> simp [mark, hevent]
  have h := PMF.etvDist_map_le mark left right
  rw [PMF.etvDist_option_punit, hmark, hmark] at h
  apply tsub_le_iff_left.mp
  apply le_trans _ h
  unfold ENNReal.absDiff
  exact le_add_of_nonneg_right zero_le

/-- The finite sampler and its denoted PMF give exactly the same event probability. -/
theorem probEvent_ticket_eq_outputPMF {Output : Type} [DecidableEq Output]
    (table : FinitePMFCompiler.TicketTable Output) (event : Output → Prop) :
    Pr[event | table.sampler] = Pr[event | table.outputPMF] := by
  classical
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    FinitePMFCompiler.TicketTable.outputPMF_apply,
    FinitePMFCompiler.TicketTable.probOutput_sampler]

/-- The ideal Gaussian tail plus one certified approximation error bounds the actual sampler. -/
theorem probEvent_ticket_tail_le (q width : ℕ) [NeZero q] (hwidth : 0 < width)
    (certificate : FinitePMFCompiler.TicketTable.Certificate
      (ModularGaussian.distribution q width (Nat.cast_pos.mpr hwidth))) :
    Pr[(fun value : ZMod q ↦ width ^ 2 < (LatticeCrypto.centeredRepr value).natAbs) |
      certificate.table.sampler] ≤
      ENNReal.ofReal (4 * Real.exp (-(width : ℝ) ^ 2 / 2)) + certificate.bound := by
  rw [probEvent_ticket_eq_outputPMF]
  apply (probEvent_le_add_etvDist certificate.table.outputPMF _ _).trans
  exact add_le_add (probEvent_modular_tail_le q width hwidth) certificate.etvDist_le

/-- The Gaussian exponent at width `n+1` is bounded by a fixed geometric decay in `n`. -/
theorem exp_square_succ_le_half_pow (dimension : ℕ) :
    Real.exp (-((dimension + 1 : ℕ) : ℝ) ^ 2 / 2) ≤ (1 / 2 : ℝ) ^ dimension := by
  have hr := exp_neg_one_le_half
  calc
    _ ≤ Real.exp (-(dimension : ℝ)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith [sq_nonneg (dimension : ℝ)]
    _ = Real.exp (-1) ^ dimension := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hr _

/-- The real geometric majorant embedded into extended probabilities is negligible. -/
theorem half_pow_negligible :
    negligible (fun dimension : ℕ ↦ ENNReal.ofReal ((1 / 2 : ℝ) ^ dimension)) := by
  intro power
  have hreal : Filter.Tendsto
      (fun dimension : ℕ ↦ (dimension : ℝ) ^ power * (1 / 2 : ℝ) ^ dimension)
      Filter.atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one power (by norm_num) (by norm_num)
  have h := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  convert h using 1
  · funext dimension
    change (dimension : ℝ≥0∞) ^ power * ENNReal.ofReal ((1 / 2 : ℝ) ^ dimension) =
      ENNReal.ofReal ((dimension : ℝ) ^ power * (1 / 2 : ℝ) ^ dimension)
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (dimension : ℝ) ^ power),
      ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (dimension : ℝ)), ENNReal.ofReal_natCast]
  · simp

/-- The explicit ideal scalar Gaussian bound is negligible, with no asymptotic tail premise. -/
theorem gaussian_tail_bound_negligible :
    negligible (fun dimension : ℕ ↦
      ENNReal.ofReal (4 * Real.exp (-((dimension + 1 : ℕ) : ℝ) ^ 2 / 2))) := by
  apply negligible_of_le (g := fun dimension ↦
    (4 : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ dimension))
  · intro dimension
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num only [ENNReal.ofReal_ofNat]
    exact mul_le_mul_of_nonneg_left
      (ENNReal.ofReal_le_ofReal (exp_square_succ_le_half_pow dimension)) zero_le
  · exact negligible_const_mul half_pow_negligible (by norm_num)

end FormalProof4FHE.DiscreteGaussianTail
