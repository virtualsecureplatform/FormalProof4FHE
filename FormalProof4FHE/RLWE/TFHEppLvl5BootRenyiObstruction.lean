/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RankOneHNFLossinessRenyi

/-!
# TFHEpp `lvl5bootparam` Renyi Mean-Energy Obstruction

This module checks the exact finite arithmetic behind the first necessary
mean-energy condition of the uniform fixed-weight, equal-covariance Gaussian
Renyi route.  For the TFHEpp level-5 bootstrap parameters, the contribution of
the highest quadratic gadget row alone is larger than twice the entropy of the
whole fixed-weight signed-ternary secret support.

The result rules out this particular sufficient certificate.  It does not
prove insecurity and does not identify a concrete TFHEpp channel with the
abstract Gaussian certificate: the theorem takes the channel's mean-energy
lower bound as a hypothesis.
-/

namespace FormalProof4FHE.RLWE.TFHEppLvl5BootRenyiObstruction

open RankOneHNFLossinessSupportAware

noncomputable section

/-- A small exact lower bound on `96!` used in the support-cardinality proof. -/
theorem two_pow_lt_factorial_96 : 2 ^ 498 < Nat.factorial 96 := by
  native_decide

/-- The standard falling-factorial bound specialized without evaluating the binomial
coefficient. -/
theorem factorial_mul_choose_le_pow :
    Nat.factorial 96 * Nat.choose 32768 96 ≤ 32768 ^ 96 := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow 32768 96

/-- Power normalization used to cancel the factorial bound. -/
theorem support_bound_power_identity :
    2 ^ 498 * 2 ^ 942 = 32768 ^ 96 := by
  rw [← pow_add, show (32768 : ℕ) = 2 ^ 15 by norm_num, ← pow_mul]

/-- The binomial part of the exact secret support has at most 942 bits. -/
theorem choose_32768_96_lt_two_pow : Nat.choose 32768 96 < 2 ^ 942 := by
  by_contra hnot
  have hchooseLower : 2 ^ 942 ≤ Nat.choose 32768 96 := Nat.le_of_not_gt hnot
  have hstrict : 2 ^ 498 * 2 ^ 942 <
      Nat.factorial 96 * Nat.choose 32768 96 :=
    (Nat.mul_lt_mul_of_pos_right two_pow_lt_factorial_96 (by positivity)).trans_le
      (Nat.mul_le_mul_left (Nat.factorial 96) hchooseLower)
  have hcontra := hstrict.trans_le factorial_mul_choose_le_pow
  rw [support_bound_power_identity] at hcontra
  exact (Nat.lt_irrefl _ hcontra)

/-- Exact bit-length certificate used by the executable parameter checker. -/
theorem lvl5SecretSupportCard_lt_two_pow :
    2 ^ 96 * Nat.choose 32768 96 < 2 ^ 1038 := by
  calc
    2 ^ 96 * Nat.choose 32768 96 < 2 ^ 96 * 2 ^ 942 :=
      Nat.mul_lt_mul_of_pos_left choose_32768_96_lt_two_pow (by positivity)
    _ = 2 ^ 1038 := by rw [← pow_add]

/-- The exact fixed-weight value `E[||S²||²]` at `n = 32768`, `w = 96`. -/
def lvl5SquareSecondMoment : ℝ := 600806592 / 32767

/-- Arithmetic specialization of
`2 n² p₂ + n (p - 3 p₂)`, with `p=w/n` and
`p₂=w(w-1)/(n(n-1))`. -/
theorem lvl5SquareSecondMoment_formula :
    2 * (32768 : ℝ) ^ 2 *
          ((96 : ℝ) * 95 / (32768 * 32767)) +
        32768 *
          ((96 : ℝ) / 32768 -
            3 * ((96 : ℝ) * 95 / (32768 * 32767))) =
      lvl5SquareSecondMoment := by
  norm_num [lvl5SquareSecondMoment]

/-- The highest TFHEpp gadget exponent is `640 - 18 = 622`; whitening by
`sigma = 2^33` and squaring gives exponent `2 * (622 - 33) = 1178`. -/
def lvl5TopQuadraticEnergy : ℝ :=
  lvl5SquareSecondMoment * (2 : ℝ) ^ 1178

/-- The top-row energy exceeds the elementary strict upper bound `2076` on twice entropy. -/
theorem lvl5TopQuadraticEnergy_gt_twiceEntropyUpper :
    (2076 : ℝ) < lvl5TopQuadraticEnergy := by
  have hmoment : (1 : ℝ) < lvl5SquareSecondMoment := by
    norm_num [lvl5SquareSecondMoment]
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ 1178 := by positivity
  calc
    (2076 : ℝ) < (2 : ℝ) ^ 12 := by norm_num
    _ ≤ (2 : ℝ) ^ 1178 :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    _ = 1 * (2 : ℝ) ^ 1178 := by rw [one_mul]
    _ < lvl5SquareSecondMoment * (2 : ℝ) ^ 1178 :=
      mul_lt_mul_of_pos_right hmoment hpowPos
    _ = lvl5TopQuadraticEnergy := rfl

/-- The natural-log entropy of the exact secret support is strictly below `1038` nats.
The deliberately elementary estimate uses `log 2 < 1`; the executable checker reports the
much sharper value in bits and nats. -/
theorem lvl5SecretEntropy_lt_integerUpper :
    Real.log ((2 ^ 96 * Nat.choose 32768 96 : ℕ) : ℝ) < 1038 := by
  have hcardPosNat : 0 < 2 ^ 96 * Nat.choose 32768 96 :=
    Nat.mul_pos (by positivity) (Nat.choose_pos (by norm_num))
  have hcardPos : (0 : ℝ) < (2 ^ 96 * Nat.choose 32768 96 : ℕ) := by
    exact_mod_cast hcardPosNat
  have hcardLt : ((2 ^ 96 * Nat.choose 32768 96 : ℕ) : ℝ) <
      (2 : ℝ) ^ 1038 := by
    exact_mod_cast lvl5SecretSupportCard_lt_two_pow
  have hlogTwo : Real.log (2 : ℝ) < 1 := by
    have hbound := Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at hbound
    exact hbound
  calc
    Real.log ((2 ^ 96 * Nat.choose 32768 96 : ℕ) : ℝ) <
        Real.log ((2 : ℝ) ^ 1038) := Real.log_lt_log hcardPos hcardLt
    _ = (1038 : ℝ) * Real.log 2 := by rw [Real.log_pow]; norm_num
    _ < (1038 : ℝ) * 1 := mul_lt_mul_of_pos_left hlogTwo (by norm_num)
    _ = 1038 := by norm_num

/-- The top quadratic row alone consumes more than the complete first-order entropy budget. -/
theorem lvl5_twiceSecretEntropy_lt_topQuadraticEnergy :
    2 * Real.log ((2 ^ 96 * Nat.choose 32768 96 : ℕ) : ℝ) <
      lvl5TopQuadraticEnergy := by
  linarith only [lvl5SecretEntropy_lt_integerUpper,
    lvl5TopQuadraticEnergy_gt_twiceEntropyUpper]

/-- Any channel whose mean energy contains the checked top-row contribution fails the strict
mean condition needed for a positive first-order Renyi margin. -/
theorem lvl5_directRenyiMeanCondition_fails
    (meanEnergy : ℝ) (topRow_le_mean : lvl5TopQuadraticEnergy ≤ meanEnergy) :
    ¬meanEnergy <
      2 * Real.log ((2 ^ 96 * Nat.choose 32768 96 : ℕ) : ℝ) := by
  linarith only [lvl5_twiceSecretEntropy_lt_topQuadraticEnergy, topRow_le_mean]

/-- Equivalent formulation using the margin `entropy - mean/2` occurring in the explicit
subgaussian theorem. -/
theorem lvl5_firstOrderRenyiMargin_not_pos
    (meanEnergy : ℝ) (topRow_le_mean : lvl5TopQuadraticEnergy ≤ meanEnergy) :
    ¬0 < Real.log ((2 ^ 96 * Nat.choose 32768 96 : ℕ) : ℝ) -
      meanEnergy / 2 := by
  intro hmargin
  apply lvl5_directRenyiMeanCondition_fails meanEnergy topRow_le_mean
  have hhalf : meanEnergy / 2 <
      Real.log ((2 ^ 96 * Nat.choose 32768 96 : ℕ) : ℝ) :=
    sub_pos.mp hmargin
  calc
    meanEnergy = 2 * (meanEnergy / 2) := by ring
    _ < 2 * Real.log ((2 ^ 96 * Nat.choose 32768 96 : ℕ) : ℝ) :=
      mul_lt_mul_of_pos_left hhalf (by norm_num)

end

end FormalProof4FHE.RLWE.TFHEppLvl5BootRenyiObstruction
