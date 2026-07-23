/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.MajorityAmplification
import Mathlib.Data.Nat.Log

/-!
# Quantitative Bounds for Recursive Majority Amplification

This module supplies the analytic estimate needed to turn the finite TFHE search reduction into
an asymptotic reduction without postulating negligibility of its amplification residual.

For errors between `1 / 4` and `1 / 2`, one majority-of-three level grows the bias from one half
by a factor of at least `11 / 8`.  Once the error is at most `1 / 4`, every further level shrinks
it by a factor of at most `3 / 4`.  Both estimates are deliberately rational, so their complete
proof stays inside elementary ordered-field arithmetic.
-/

open ENNReal

namespace FormalProof4FHE.MajorityAmplification

/-- Real-valued presentation of the exact majority-of-three error recurrence. -/
noncomputable def majorityErrorReal (error : ℝ) : ℝ :=
  error ^ 2 * (1 + 2 * (1 - error))

/-- Real-valued iteration of `majorityErrorReal`. -/
noncomputable def amplifiedErrorReal : ℕ → ℝ → ℝ
  | 0, error => error
  | rounds + 1, error => majorityErrorReal (amplifiedErrorReal rounds error)

/-- `ENNReal.toReal` commutes with one majority update on the probability interval. -/
theorem majorityError_toReal {error : ENNReal} (herror : error ≤ 1) :
    (majorityError error).toReal = majorityErrorReal error.toReal := by
  have hsub_ne : 1 - error ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hmul_ne : 2 * (1 - error) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hsub_ne
  unfold majorityError majorityErrorReal
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_add ENNReal.one_ne_top hmul_ne,
    ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le herror ENNReal.one_ne_top]
  norm_num

/-- `ENNReal.toReal` commutes with every iterated majority update. -/
theorem amplifiedError_toReal (rounds : ℕ) {error : ENNReal} (herror : error ≤ 1) :
    (amplifiedError rounds error).toReal = amplifiedErrorReal rounds error.toReal := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      simp only [amplifiedError, amplifiedErrorReal]
      rw [majorityError_toReal (amplifiedError_le_one rounds herror), ih]

/-- The real recurrence preserves nonnegativity on the probability interval. -/
theorem majorityErrorReal_nonneg {error : ℝ} (herror_one : error ≤ 1) :
    0 ≤ majorityErrorReal error := by
  unfold majorityErrorReal
  exact mul_nonneg (sq_nonneg error) (by linarith)

/-- Below one half, one majority level never increases the error. -/
theorem majorityErrorReal_le_self {error : ℝ} (herror_nonneg : 0 ≤ error)
    (herror_half : error ≤ 1 / 2) : majorityErrorReal error ≤ error := by
  unfold majorityErrorReal
  nlinarith [mul_nonneg herror_nonneg (sub_nonneg.mpr (by linarith : error ≤ 1)),
    mul_nonneg (sub_nonneg.mpr (by linarith : error ≤ 1))
      (sub_nonneg.mpr (by linarith : 2 * error ≤ 1))]

/-- One majority level grows bias by at least `11 / 8` while the error is in `[1/4, 1/2]`. -/
theorem eleven_eighths_mul_bias_le_bias_majorityErrorReal {error : ℝ}
    (hquarter : 1 / 4 ≤ error) (hhalf : error ≤ 1 / 2) :
    (11 / 8 : ℝ) * (1 / 2 - error) ≤ 1 / 2 - majorityErrorReal error := by
  unfold majorityErrorReal
  have hbias_nonneg : 0 ≤ 1 / 2 - error := by linarith
  have hbias_quarter : 1 / 2 - error ≤ 1 / 4 := by linarith
  nlinarith [mul_nonneg hbias_nonneg
    (sub_nonneg.mpr (by nlinarith [sq_nonneg (1 / 2 - error)] :
      2 * (1 / 2 - error) ^ 2 ≤ 1 / 8))]

/-- Once the error is at most one quarter, a majority level contracts it by `3 / 4`. -/
theorem majorityErrorReal_le_three_quarters_mul {error : ℝ}
    (herror_nonneg : 0 ≤ error) (hquarter : error ≤ 1 / 4) :
    majorityErrorReal error ≤ (3 / 4 : ℝ) * error := by
  unfold majorityErrorReal
  nlinarith [mul_nonneg herror_nonneg (sub_nonneg.mpr hquarter)]

/-- Every real iterate stays nonnegative and below its initial error when the latter is at most
one half. -/
theorem amplifiedErrorReal_nonneg_and_le (rounds : ℕ) {error : ℝ}
    (herror_nonneg : 0 ≤ error) (herror_half : error ≤ 1 / 2) :
    0 ≤ amplifiedErrorReal rounds error ∧ amplifiedErrorReal rounds error ≤ error := by
  induction rounds with
  | zero => exact ⟨herror_nonneg, le_rfl⟩
  | succ rounds ih =>
      simp only [amplifiedErrorReal]
      have hcurrent_half : amplifiedErrorReal rounds error ≤ 1 / 2 :=
        ih.2.trans herror_half
      exact ⟨majorityErrorReal_nonneg (hcurrent_half.trans (by norm_num)),
        (majorityErrorReal_le_self ih.1 hcurrent_half).trans ih.2⟩

/-- If the final iterate has not crossed one quarter, its bias records every preceding
`11 / 8` growth step. -/
theorem pow_eleven_eighths_mul_bias_le_final_bias_of_quarter_lt
    (rounds : ℕ) {error : ℝ} (herror_nonneg : 0 ≤ error) (herror_half : error ≤ 1 / 2)
    (hfinal : 1 / 4 < amplifiedErrorReal rounds error) :
    (11 / 8 : ℝ) ^ rounds * (1 / 2 - error) ≤
      1 / 2 - amplifiedErrorReal rounds error := by
  induction rounds with
  | zero =>
      simp only [amplifiedErrorReal, pow_zero, one_mul]
      exact le_rfl
  | succ rounds ih =>
      simp only [amplifiedErrorReal] at hfinal ⊢
      have hbounds := amplifiedErrorReal_nonneg_and_le rounds herror_nonneg herror_half
      have hcurrent_half : amplifiedErrorReal rounds error ≤ 1 / 2 :=
        hbounds.2.trans herror_half
      have hstep_le :
          majorityErrorReal (amplifiedErrorReal rounds error) ≤
            amplifiedErrorReal rounds error :=
        majorityErrorReal_le_self hbounds.1 hcurrent_half
      have hcurrent_quarter : 1 / 4 < amplifiedErrorReal rounds error :=
        hfinal.trans_le hstep_le
      have hih := ih hcurrent_quarter
      have hgrowth := eleven_eighths_mul_bias_le_bias_majorityErrorReal
        hcurrent_quarter.le hcurrent_half
      rw [pow_succ]
      nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 8)
        (sub_nonneg.mpr hcurrent_half)]

/-- Enough accumulated bias growth forces the error below one quarter. -/
theorem amplifiedErrorReal_le_quarter_of_bias_growth
    (rounds : ℕ) {error : ℝ} (herror_nonneg : 0 ≤ error) (herror_half : error ≤ 1 / 2)
    (hgrowth : 1 / 4 ≤ (11 / 8 : ℝ) ^ rounds * (1 / 2 - error)) :
    amplifiedErrorReal rounds error ≤ 1 / 4 := by
  by_contra h
  have hfinal : 1 / 4 < amplifiedErrorReal rounds error := lt_of_not_ge h
  have hbias := pow_eleven_eighths_mul_bias_le_final_bias_of_quarter_lt
    rounds herror_nonneg herror_half hfinal
  linarith

/-- Below one quarter, iterated contraction is bounded by `(3 / 4)^rounds`. -/
theorem amplifiedErrorReal_le_pow_three_quarters_mul
    (rounds : ℕ) {error : ℝ} (herror_nonneg : 0 ≤ error) (hquarter : error ≤ 1 / 4) :
    amplifiedErrorReal rounds error ≤ (3 / 4 : ℝ) ^ rounds * error := by
  induction rounds with
  | zero => simp [amplifiedErrorReal]
  | succ rounds ih =>
      simp only [amplifiedErrorReal]
      have hbounds := amplifiedErrorReal_nonneg_and_le rounds herror_nonneg
        (hquarter.trans (by norm_num))
      have hcurrent_quarter : amplifiedErrorReal rounds error ≤ 1 / 4 :=
        hbounds.2.trans hquarter
      calc
        majorityErrorReal (amplifiedErrorReal rounds error) ≤
            (3 / 4 : ℝ) * amplifiedErrorReal rounds error :=
          majorityErrorReal_le_three_quarters_mul hbounds.1 hcurrent_quarter
        _ ≤ (3 / 4 : ℝ) * ((3 / 4 : ℝ) ^ rounds * error) := by gcongr
        _ = (3 / 4 : ℝ) ^ (rounds + 1) * error := by ring

/-- Iterating for `warmup + cooldown` levels is the composition of the two stages. -/
theorem amplifiedErrorReal_add (warmup cooldown : ℕ) (error : ℝ) :
    amplifiedErrorReal (warmup + cooldown) error =
      amplifiedErrorReal cooldown (amplifiedErrorReal warmup error) := by
  induction cooldown with
  | zero => simp [amplifiedErrorReal]
  | succ cooldown ih =>
      rw [Nat.add_succ]
      simp only [amplifiedErrorReal, ih]

/-- Warm-up bias growth followed by geometric contraction. -/
theorem amplifiedErrorReal_le_warmup_cooldown
    (warmup cooldown : ℕ) {error : ℝ} (herror_nonneg : 0 ≤ error)
    (herror_half : error ≤ 1 / 2)
    (hgrowth : 1 / 4 ≤ (11 / 8 : ℝ) ^ warmup * (1 / 2 - error)) :
    amplifiedErrorReal (warmup + cooldown) error ≤
      (3 / 4 : ℝ) ^ cooldown / 4 := by
  rw [amplifiedErrorReal_add]
  have hwarm := amplifiedErrorReal_le_quarter_of_bias_growth
    warmup herror_nonneg herror_half hgrowth
  have hwarm_nonneg :=
    (amplifiedErrorReal_nonneg_and_le warmup herror_nonneg herror_half).1
  calc
    amplifiedErrorReal cooldown (amplifiedErrorReal warmup error) ≤
        (3 / 4 : ℝ) ^ cooldown * amplifiedErrorReal warmup error :=
      amplifiedErrorReal_le_pow_three_quarters_mul cooldown hwarm_nonneg hwarm
    _ ≤ (3 / 4 : ℝ) ^ cooldown * (1 / 4) := by gcongr
    _ = (3 / 4 : ℝ) ^ cooldown / 4 := by ring

/-! ## Logarithmic-depth schedules -/

/-- One plus the base-two floor logarithm.  It is positive even at parameter zero and satisfies
`n + 1 < 2 ^ logScale n`. -/
def logScale (securityParameter : ℕ) : ℕ :=
  Nat.log 2 (securityParameter + 1) + 1

/-- Levels used to grow an inverse-polynomial initial bias to a constant. -/
def warmupRounds (strength securityParameter : ℕ) : ℕ :=
  3 * strength * logScale securityParameter

/-- Levels used to contract a constant error by an inverse-polynomial factor. -/
def cooldownRounds (strength securityParameter : ℕ) : ℕ :=
  3 * strength * logScale securityParameter

/-- Complete logarithmic-depth schedule, with independently selectable warm-up and cooldown
strengths. -/
def logarithmicRounds (warmupStrength cooldownStrength securityParameter : ℕ) : ℕ :=
  warmupRounds warmupStrength securityParameter +
    cooldownRounds cooldownStrength securityParameter

theorem add_one_lt_two_pow_logScale (securityParameter : ℕ) :
    securityParameter + 1 < 2 ^ logScale securityParameter := by
  simpa only [logScale, Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self Nat.one_lt_two (securityParameter + 1)

theorem two_pow_logScale_le_two_mul_add_one (securityParameter : ℕ) :
    2 ^ logScale securityParameter ≤ 2 * (securityParameter + 1) := by
  rw [logScale, pow_succ]
  have h := Nat.pow_log_le_self 2 (Nat.add_one_ne_zero securityParameter)
  omega

/-- Three warm-up levels grow bias by at least a factor two. -/
theorem two_le_eleven_eighths_pow_three :
    (2 : ℝ) ≤ (11 / 8 : ℝ) ^ 3 := by
  norm_num

/-- Three cooldown levels contract error by at least a factor two. -/
theorem three_quarters_pow_three_le_half :
    (3 / 4 : ℝ) ^ 3 ≤ 1 / 2 := by
  norm_num

/-- The warm-up stage supplies the polynomial bias growth advertised by its strength. -/
theorem add_one_pow_le_eleven_eighths_pow_warmupRounds
    (strength securityParameter : ℕ) :
    ((securityParameter + 1 : ℕ) : ℝ) ^ strength ≤
      (11 / 8 : ℝ) ^ warmupRounds strength securityParameter := by
  let scale := logScale securityParameter
  have hparameter : ((securityParameter + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ scale := by
    exact_mod_cast (add_one_lt_two_pow_logScale securityParameter).le
  have hparameterPow : ((securityParameter + 1 : ℕ) : ℝ) ^ strength ≤
      ((2 : ℝ) ^ scale) ^ strength := by
    gcongr
  have hbasePow : (2 : ℝ) ^ (strength * scale) ≤
      ((11 / 8 : ℝ) ^ 3) ^ (strength * scale) := by
    gcongr
    exact two_le_eleven_eighths_pow_three
  calc
    ((securityParameter + 1 : ℕ) : ℝ) ^ strength ≤
        ((2 : ℝ) ^ scale) ^ strength := hparameterPow
    _ = (2 : ℝ) ^ (strength * scale) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ ((11 / 8 : ℝ) ^ 3) ^ (strength * scale) := hbasePow
    _ = (11 / 8 : ℝ) ^ warmupRounds strength securityParameter := by
      rw [← pow_mul]
      simp only [warmupRounds, scale]
      congr 1
      ring

/-- The cooldown stage supplies the inverse-polynomial contraction advertised by its strength. -/
theorem three_quarters_pow_cooldownRounds_le_inv_add_one_pow
    (strength securityParameter : ℕ) :
    (3 / 4 : ℝ) ^ cooldownRounds strength securityParameter ≤
      (((securityParameter + 1 : ℕ) : ℝ) ^ strength)⁻¹ := by
  let scale := logScale securityParameter
  have hparameter : ((securityParameter + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ scale := by
    exact_mod_cast (add_one_lt_two_pow_logScale securityParameter).le
  have hinv : ((2 : ℝ) ^ scale)⁻¹ ≤
      (((securityParameter + 1 : ℕ) : ℝ))⁻¹ := by
    exact inv_anti₀ (by positivity) hparameter
  have hinvPow : (((2 : ℝ) ^ scale)⁻¹) ^ strength ≤
      ((((securityParameter + 1 : ℕ) : ℝ))⁻¹) ^ strength := by
    gcongr
  have hbasePow : ((3 / 4 : ℝ) ^ 3) ^ (strength * scale) ≤
      (1 / 2 : ℝ) ^ (strength * scale) := by
    gcongr
    exact three_quarters_pow_three_le_half
  calc
    (3 / 4 : ℝ) ^ cooldownRounds strength securityParameter =
        ((3 / 4 : ℝ) ^ 3) ^ (strength * scale) := by
      rw [← pow_mul]
      simp only [cooldownRounds, scale]
      congr 1
      ring
    _ ≤ (1 / 2 : ℝ) ^ (strength * scale) := hbasePow
    _ = (((2 : ℝ) ^ scale)⁻¹) ^ strength := by
      rw [Nat.mul_comm, pow_mul]
      congr 1
      simp
    _ ≤ ((((securityParameter + 1 : ℕ) : ℝ))⁻¹) ^ strength := hinvPow
    _ = (((securityParameter + 1 : ℕ) : ℝ) ^ strength)⁻¹ := by rw [inv_pow]

/-- A polynomial bound on the number of ternary leaves used by `logarithmicRounds`. -/
theorem three_pow_logarithmicRounds_le
    (warmupStrength cooldownStrength securityParameter : ℕ) :
    3 ^ logarithmicRounds warmupStrength cooldownStrength securityParameter ≤
      2 ^ (6 * (warmupStrength + cooldownStrength)) *
        (securityParameter + 1) ^ (6 * (warmupStrength + cooldownStrength)) := by
  let totalStrength := warmupStrength + cooldownStrength
  let scale := logScale securityParameter
  have hthree_four : 3 ≤ 4 := by omega
  have hpow : 3 ^ (3 * totalStrength * scale) ≤ 4 ^ (3 * totalStrength * scale) :=
    Nat.pow_le_pow_left hthree_four _
  have hscale := two_pow_logScale_le_two_mul_add_one securityParameter
  have hscalePow : (2 ^ scale) ^ (6 * totalStrength) ≤
      (2 * (securityParameter + 1)) ^ (6 * totalStrength) :=
    Nat.pow_le_pow_left hscale _
  calc
    3 ^ logarithmicRounds warmupStrength cooldownStrength securityParameter =
        3 ^ (3 * totalStrength * scale) := by
      congr 1
      simp only [logarithmicRounds, warmupRounds, cooldownRounds,
        totalStrength, scale]
      ring
    _ ≤ 4 ^ (3 * totalStrength * scale) := hpow
    _ = (2 ^ scale) ^ (6 * totalStrength) := by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      ring
    _ ≤ (2 * (securityParameter + 1)) ^ (6 * totalStrength) := hscalePow
    _ = 2 ^ (6 * totalStrength) *
        (securityParameter + 1) ^ (6 * totalStrength) := by
      rw [mul_pow]
    _ = 2 ^ (6 * (warmupStrength + cooldownStrength)) *
        (securityParameter + 1) ^ (6 * (warmupStrength + cooldownStrength)) := by
      rfl

/-- Polynomial realizing the preceding exact leaf-count bound. -/
noncomputable def logarithmicViewPolynomial
    (warmupStrength cooldownStrength : ℕ) : Polynomial ℕ :=
  Polynomial.C (2 ^ (6 * (warmupStrength + cooldownStrength))) *
    (Polynomial.X + 1) ^ (6 * (warmupStrength + cooldownStrength))

theorem three_pow_logarithmicRounds_le_polynomial
    (warmupStrength cooldownStrength securityParameter : ℕ) :
    3 ^ logarithmicRounds warmupStrength cooldownStrength securityParameter ≤
      (logarithmicViewPolynomial warmupStrength cooldownStrength).eval securityParameter := by
  simpa [logarithmicViewPolynomial] using
    three_pow_logarithmicRounds_le warmupStrength cooldownStrength securityParameter

/-! ## Uniform inverse-polynomial residual bound -/

/-- If a decision advantage is at least the inverse-polynomial floor selected by the warm-up
strength, logarithmic-depth amplification drives its balanced threshold below the cooldown
inverse-polynomial bound. -/
theorem amplifiedErrorReal_logarithmicRounds_le_of_inverse_floor
    (warmupStrength cooldownStrength securityParameter : ℕ) {advantage : ℝ}
    (hadvantage_nonneg : 0 ≤ advantage) (hadvantage_one : advantage ≤ 1)
    (hfloor : (((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength)⁻¹ ≤ advantage) :
    amplifiedErrorReal
        (logarithmicRounds warmupStrength cooldownStrength securityParameter)
        ((2 - advantage) / 4) ≤
      ((((securityParameter + 1 : ℕ) : ℝ) ^ cooldownStrength)⁻¹) / 4 := by
  have herror_nonneg : 0 ≤ (2 - advantage) / 4 := by linarith
  have herror_half : (2 - advantage) / 4 ≤ 1 / 2 := by linarith
  have hwarm := add_one_pow_le_eleven_eighths_pow_warmupRounds
    warmupStrength securityParameter
  have hpositive : 0 < ((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength := by positivity
  have hcancel :
      ((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength *
          (((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength)⁻¹ = 1 := by
    exact mul_inv_cancel₀ hpositive.ne'
  have hgrowth :
      1 / 4 ≤ (11 / 8 : ℝ) ^ warmupRounds warmupStrength securityParameter *
        (1 / 2 - (2 - advantage) / 4) := by
    have hproduct : 1 ≤
        (11 / 8 : ℝ) ^ warmupRounds warmupStrength securityParameter * advantage := by
      calc
        1 = ((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength *
            (((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength)⁻¹ := hcancel.symm
        _ ≤ ((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength * advantage := by
          gcongr
        _ ≤ (11 / 8 : ℝ) ^ warmupRounds warmupStrength securityParameter *
            advantage := by
          gcongr
    nlinarith
  have hbound := amplifiedErrorReal_le_warmup_cooldown
    (warmupRounds warmupStrength securityParameter)
    (cooldownRounds cooldownStrength securityParameter)
    herror_nonneg herror_half hgrowth
  rw [← logarithmicRounds] at hbound
  exact hbound.trans (by
    gcongr
    exact three_quarters_pow_cooldownRounds_le_inv_add_one_pow
      cooldownStrength securityParameter)

/-- Uniform capped-error estimate.  For small advantage the cap itself wins; above the selected
floor, the logarithmic majority schedule wins. -/
theorem min_dimension_mul_amplifiedErrorReal_half_advantage_le
    (dimension warmupStrength cooldownStrength securityParameter : ℕ) {advantage : ℝ}
    (hadvantage_nonneg : 0 ≤ advantage) (hadvantage_one : advantage ≤ 1) :
    min
        ((dimension : ℝ) * amplifiedErrorReal
          (logarithmicRounds warmupStrength cooldownStrength securityParameter)
          ((2 - advantage) / 4))
        (advantage / 2) ≤
      ((((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength)⁻¹) / 2 +
        (dimension : ℝ) *
          ((((securityParameter + 1 : ℕ) : ℝ) ^ cooldownStrength)⁻¹) / 4 := by
  by_cases hsmall :
      advantage ≤ (((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength)⁻¹
  · calc
      min
          ((dimension : ℝ) * amplifiedErrorReal
            (logarithmicRounds warmupStrength cooldownStrength securityParameter)
            ((2 - advantage) / 4))
          (advantage / 2) ≤ advantage / 2 := min_le_right _ _
      _ ≤ (((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength)⁻¹ / 2 := by
        gcongr
      _ ≤ (((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength)⁻¹ / 2 +
          (dimension : ℝ) *
            (((securityParameter + 1 : ℕ) : ℝ) ^ cooldownStrength)⁻¹ / 4 := by
        have hterm : 0 ≤ (dimension : ℝ) *
            (((securityParameter + 1 : ℕ) : ℝ) ^ cooldownStrength)⁻¹ / 4 := by
          positivity
        linarith
  · have hfloor : (((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength)⁻¹ ≤
        advantage := le_of_not_ge hsmall
    have hamp := amplifiedErrorReal_logarithmicRounds_le_of_inverse_floor
      warmupStrength cooldownStrength securityParameter
      hadvantage_nonneg hadvantage_one hfloor
    calc
      min
          ((dimension : ℝ) * amplifiedErrorReal
            (logarithmicRounds warmupStrength cooldownStrength securityParameter)
            ((2 - advantage) / 4))
          (advantage / 2) ≤
          (dimension : ℝ) * amplifiedErrorReal
            (logarithmicRounds warmupStrength cooldownStrength securityParameter)
            ((2 - advantage) / 4) := min_le_left _ _
      _ ≤ (dimension : ℝ) *
          ((((securityParameter + 1 : ℕ) : ℝ) ^ cooldownStrength)⁻¹ / 4) := by
        gcongr
      _ ≤ (((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength)⁻¹ / 2 +
          (dimension : ℝ) *
            (((securityParameter + 1 : ℕ) : ℝ) ^ cooldownStrength)⁻¹ / 4 := by
        have hfirst : 0 ≤
            (((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength)⁻¹ / 2 := by
          positivity
        ring_nf at hfirst ⊢
        linarith

/-! ## Elementary bounds for natural-coefficient polynomials -/

/-- Sum of all coefficients that can occur below the natural degree. -/
noncomputable def polynomialCoefficientSum (polynomial : Polynomial ℕ) : ℕ :=
  ∑ index ∈ Finset.range (polynomial.natDegree + 1), polynomial.coeff index

/-- A natural-coefficient polynomial is bounded by its coefficient sum times
`(securityParameter + 1)^natDegree`. -/
theorem polynomial_eval_le_coefficientSum_mul_add_one_pow
    (polynomial : Polynomial ℕ) (securityParameter : ℕ) :
    polynomial.eval securityParameter ≤
      polynomialCoefficientSum polynomial *
        (securityParameter + 1) ^ polynomial.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    ∑ index ∈ Finset.range (polynomial.natDegree + 1),
        polynomial.coeff index * securityParameter ^ index ≤
      ∑ index ∈ Finset.range (polynomial.natDegree + 1),
        polynomial.coeff index *
          (securityParameter + 1) ^ polynomial.natDegree := by
        apply Finset.sum_le_sum
        intro index hindex
        have hdegree : index ≤ polynomial.natDegree :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hindex)
        have hbase : securityParameter ^ index ≤
            (securityParameter + 1) ^ index :=
          Nat.pow_le_pow_left (Nat.le_succ securityParameter) index
        have hexponent : (securityParameter + 1) ^ index ≤
            (securityParameter + 1) ^ polynomial.natDegree :=
          pow_le_pow_right' (by omega) hdegree
        exact Nat.mul_le_mul_left _ (hbase.trans hexponent)
    _ = polynomialCoefficientSum polynomial *
        (securityParameter + 1) ^ polynomial.natDegree := by
      rw [polynomialCoefficientSum, Finset.sum_mul]

/-- Multiplying the uniform residual estimate by the selected negligibility power leaves an
inverse-square tail, even after a polynomial dimension factor. -/
theorem pow_mul_inverse_bounds_le_inverse_square
    (power degree : ℕ) {parameter scale dimension coefficientSum : ℝ}
    (hparameter_nonneg : 0 ≤ parameter) (hscale_pos : 0 < scale)
    (hparameter_scale : parameter ≤ scale) (hdimension_nonneg : 0 ≤ dimension)
    (hdimension : dimension ≤ coefficientSum * scale ^ degree) :
    parameter ^ power *
        (scale ^ (2 + power))⁻¹ / 2 +
      parameter ^ power *
        (dimension * (scale ^ (2 + power + degree))⁻¹ / 4) ≤
      (1 / 2 + coefficientSum / 4) * (scale ^ 2)⁻¹ := by
  have hpower : parameter ^ power ≤ scale ^ power := by
    gcongr
  have hwarm_nonneg : 0 ≤ (scale ^ (2 + power))⁻¹ / 2 := by positivity
  have hcool_nonneg : 0 ≤ dimension * (scale ^ (2 + power + degree))⁻¹ / 4 := by
    positivity
  have hwarm : parameter ^ power * (scale ^ (2 + power))⁻¹ / 2 ≤
      scale ^ power * (scale ^ (2 + power))⁻¹ / 2 := by
    gcongr
  have hcool : parameter ^ power *
        (dimension * (scale ^ (2 + power + degree))⁻¹ / 4) ≤
      scale ^ power *
        ((coefficientSum * scale ^ degree) *
          (scale ^ (2 + power + degree))⁻¹ / 4) := by
    gcongr
  calc
    parameter ^ power * (scale ^ (2 + power))⁻¹ / 2 +
        parameter ^ power *
          (dimension * (scale ^ (2 + power + degree))⁻¹ / 4) ≤
      scale ^ power * (scale ^ (2 + power))⁻¹ / 2 +
        scale ^ power *
          ((coefficientSum * scale ^ degree) *
            (scale ^ (2 + power + degree))⁻¹ / 4) := add_le_add hwarm hcool
    _ = (1 / 2 + coefficientSum / 4) * (scale ^ 2)⁻¹ := by
      field_simp [hscale_pos.ne']
      ring

end FormalProof4FHE.MajorityAmplification
