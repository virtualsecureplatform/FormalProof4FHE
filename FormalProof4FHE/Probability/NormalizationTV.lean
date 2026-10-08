/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.ModularGaussian

/-!
# Total variation from an unnormalized approximation

Comparing a PMF `p` with a nonnegative scalar multiple of another PMF `q`
suffices: the `L¹` discrepancy also bounds the difference of normalizers.
Consequently `TV(p,q) ≤ Σ |p-c*q|`. This handles a finite weighted sampler
against an infinite-support target without adding a support-cardinality loss.
-/

open scoped BigOperators ENNReal

namespace FormalProof4FHE.NormalizationTV

variable {Output : Type}

theorem pmf_real_summable (distribution : PMF Output) :
    Summable (fun value ↦ (distribution value).toReal) := by
  apply ENNReal.summable_toReal
  rw [distribution.tsum_coe]
  exact ENNReal.one_ne_top

theorem pmf_real_sum (distribution : PMF Output) :
    (∑' value, (distribution value).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun value ↦ distribution.apply_ne_top value),
    distribution.tsum_coe, ENNReal.toReal_one]

/-- The mass discrepancy accounts for renormalization, using the target's scale. -/
theorem tvDist_le_scaled_error (target actual : PMF Output) (scale : ℝ) :
    target.tvDist actual ≤
      ∑' value, |(target value).toReal - scale * (actual value).toReal| := by
  have htarget := pmf_real_summable target
  have hactual := pmf_real_summable actual
  have hdiff := htarget.sub (hactual.mul_left scale)
  have habs := hdiff.abs
  have hsum : (∑' value, ((target value).toReal - scale * (actual value).toReal)) = 1 - scale := by
    rw [htarget.tsum_sub (hactual.mul_left scale), tsum_mul_left, pmf_real_sum, pmf_real_sum, mul_one]
  have hscale : |1 - scale| ≤
      ∑' value, |(target value).toReal - scale * (actual value).toReal| := by
    have h := norm_tsum_le_tsum_norm (show Summable (fun value ↦
      ‖(target value).toReal - scale * (actual value).toReal‖) by
      simpa only [Real.norm_eq_abs] using habs)
    rw [hsum] at h
    simpa only [Real.norm_eq_abs] using h
  have hpoint (value : Output) : |(target value).toReal - (actual value).toReal| ≤
      |(target value).toReal - scale * (actual value).toReal| +
        |1 - scale| * (actual value).toReal := by
    have h := abs_sub_le (target value).toReal (scale * (actual value).toReal) (actual value).toReal
    have hid : scale * (actual value).toReal - (actual value).toReal =
        (scale - 1) * (actual value).toReal := by ring
    simpa only [hid, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, abs_sub_comm scale 1] using h
  have hbound := (htarget.sub hactual).abs.tsum_le_tsum hpoint
    (habs.add (hactual.mul_left |1 - scale|))
  rw [habs.tsum_add (hactual.mul_left |1 - scale|), tsum_mul_left, pmf_real_sum, mul_one] at hbound
  rw [ModularGaussian.tvDist_eq_half_tsum_abs_toReal]
  linarith

/-- Extended-TV form for sampler certificates. -/
theorem etvDist_le_of_scaled_error (target actual : PMF Output) (scale bound : ℝ)
    (herror : (∑' value, |(target value).toReal - scale * (actual value).toReal|) ≤ bound) :
    target.etvDist actual ≤ ENNReal.ofReal bound := by
  calc
    _ = ENNReal.ofReal (target.tvDist actual) := by
      rw [PMF.tvDist, ENNReal.ofReal_toReal (PMF.etvDist_ne_top target actual)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal ((tvDist_le_scaled_error target actual scale).trans herror)

end FormalProof4FHE.NormalizationTV
