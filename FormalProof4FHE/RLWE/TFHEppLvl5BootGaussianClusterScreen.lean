/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RankOneHNFLossinessGaussianCluster

/-!
# TFHEpp `lvl5bootparam` Gaussian-Cluster Screen

This module checks the finite certificate emitted by
`Parameter-Selection/python/proof/lvl5boot_gaussian_cluster.py`.

For a fixed signed weight-`w` centre, candidates obtained by replacing exactly `k` support
positions form an orbit of size

`2^w * choose(w,k) * choose(n-w,k)`.

The radius-two cloud (`k = 0,1,2`) is larger than `2^128`, so it has enough cardinality in the
hypothetical perfect-overlap case.  The executable checker uses one uniform mask coordinate to
bound every nonidentity Gaussian overlap by `2^-604`.  Lean checks the resulting Markov and
finite-support union arithmetic.  The elementary analytic input

`sum_z exp (-z^2/(2*sigma^2)) < 4*sigma`

is intentionally an explicit boundary of this module rather than an axiom.

The final section proves directly that TFHEpp's now-total signed-`int64` lift has diameter below
`2^64`.  Consequently a centred mean shift of magnitude at least `2^64` gives disjoint lifted
noise supports.  Identifying source-level modular Gaussian generation and the uniform mask with
these arithmetic premises remains an implementation-refinement obligation.
-/

namespace FormalProof4FHE.RLWE.TFHEppLvl5BootGaussianClusterScreen

noncomputable section

/-! ## Source parameter arithmetic -/

/-- `MultiLimbUInt<10>` has a 640-bit torus word. -/
theorem lvl5_modulusBits : 10 * 64 = 640 := by norm_num

/-- `alpha = 2^-607` at a 640-bit torus gives coefficient scale `2^33`. -/
theorem lvl5_errorStdExponent : 640 - 607 = 33 := by norm_num

/-- The highest ordinary gadget row has weight `2^(640-18) = 2^622`. -/
theorem lvl5_topGadgetExponent : 640 - 18 = 622 := by norm_num

/-- Forty base-`2^16` auxiliary digits cover the complete torus word. -/
theorem lvl5_doubleDecompositionCapacity : 40 * 16 = 640 := by norm_num

/-! ## Three support-transition orbits -/

/-- All sign choices on the unchanged support (`k=0`). -/
def sameSupportOrbitCard : ℕ := 2 ^ 96

/-- Replace one of 96 positions and choose its replacement outside the support (`k=1`). -/
def oneReplacementOrbitCard : ℕ :=
  2 ^ 96 * Nat.choose 96 1 * Nat.choose (32768 - 96) 1

/-- Replace two support positions (`k=2`). -/
def twoReplacementOrbitCard : ℕ :=
  2 ^ 96 * Nat.choose 96 2 * Nat.choose (32768 - 96) 2

/-- Cloud containing every candidate with at most one support replacement. -/
def radiusOneOrbitCard : ℕ :=
  sameSupportOrbitCard + oneReplacementOrbitCard

/-- Cloud containing every candidate with at most two support replacements. -/
def radiusTwoOrbitCard : ℕ :=
  radiusOneOrbitCard + twoReplacementOrbitCard

theorem sameSupportOrbitCard_value :
    sameSupportOrbitCard = 79228162514264337593543950336 := by
  norm_num [sameSupportOrbitCard]

theorem oneReplacementOrbitCard_value :
    oneReplacementOrbitCard = 248500082463940266034201722756268032 := by
  norm_num [oneReplacementOrbitCard]

theorem twoReplacementOrbitCard_value :
    twoReplacementOrbitCard =
      192820222111760570250580856499038280744960 := by
  norm_num [twoReplacementOrbitCard, Nat.choose_two_right]

theorem radiusTwoOrbitCard_value :
    radiusTwoOrbitCard =
      192820470611922262353361155038354580963328 := by
  norm_num [radiusTwoOrbitCard, radiusOneOrbitCard, sameSupportOrbitCard,
    oneReplacementOrbitCard, twoReplacementOrbitCard, Nat.choose_two_right]

/-- Radius one cannot contain 128 bits of candidates even under perfect overlap. -/
theorem radiusOneOrbitCard_lt_two_pow_118 : radiusOneOrbitCard < 2 ^ 118 := by
  norm_num [radiusOneOrbitCard, sameSupportOrbitCard, oneReplacementOrbitCard]

/-- Radius two removes that cardinality obstruction. -/
theorem two_pow_128_lt_radiusTwoOrbitCard : 2 ^ 128 < radiusTwoOrbitCard := by
  rw [radiusTwoOrbitCard_value]
  norm_num

/-- A compact bit-length bound used by both probability certificates. -/
theorem radiusTwoOrbitCard_lt_two_pow_138 : radiusTwoOrbitCard < 2 ^ 138 := by
  rw [radiusTwoOrbitCard_value]
  norm_num

/-! ## Exact Gaussian and finite-channel probability arithmetic -/

/-- If each nonidentity Gaussian kernel has expectation at most `2^-604`, Markov at excess
`2^-128` produces the factor comparison below and hence bad probability below `2^-338`.
The executable checker supplies the per-pair analytic estimate. -/
theorem radiusTwoGaussianMarkov_powerCertificate :
    (radiusTwoOrbitCard - 1) * 2 ^ (128 + 338) < 2 ^ 604 := by
  have hcard : radiusTwoOrbitCard - 1 < 2 ^ 138 :=
    (Nat.sub_le radiusTwoOrbitCard 1).trans_lt radiusTwoOrbitCard_lt_two_pow_138
  calc
    (radiusTwoOrbitCard - 1) * 2 ^ (128 + 338) <
        2 ^ 138 * 2 ^ (128 + 338) :=
      Nat.mul_lt_mul_of_pos_right hcard (by positivity)
    _ = 2 ^ 604 := by rw [← pow_add]

/-- If a fixed candidate's selected uniform coordinate is within one signed-`int64` noise
diameter with probability below `2^-574`, the union over the complete radius-two cloud is below
`2^-436`. -/
theorem radiusTwoImplementedChannelUnion_powerCertificate :
    (radiusTwoOrbitCard - 1) * 2 ^ 436 < 2 ^ 574 := by
  have hcard : radiusTwoOrbitCard - 1 < 2 ^ 138 :=
    (Nat.sub_le radiusTwoOrbitCard 1).trans_lt radiusTwoOrbitCard_lt_two_pow_138
  calc
    (radiusTwoOrbitCard - 1) * 2 ^ 436 < 2 ^ 138 * 2 ^ 436 :=
      Nat.mul_lt_mul_of_pos_right hcard (by positivity)
    _ = 2 ^ 574 := by rw [← pow_add]

/-- Cross-multiplied form of the exact rational Gaussian Markov comparison. -/
theorem radiusTwoGaussianMarkov_crossCertificate :
    (radiusTwoOrbitCard - 1) * 2 ^ 338 < 2 ^ 476 := by
  have hcard : radiusTwoOrbitCard - 1 < 2 ^ 138 :=
    (Nat.sub_le radiusTwoOrbitCard 1).trans_lt radiusTwoOrbitCard_lt_two_pow_138
  calc
    (radiusTwoOrbitCard - 1) * 2 ^ 338 < 2 ^ 138 * 2 ^ 338 :=
      Nat.mul_lt_mul_of_pos_right hcard (by positivity)
    _ = 2 ^ 476 := by rw [← pow_add]

/-- Exact rational Markov upper bound reported by the executable checker. -/
def radiusTwoGaussianMarkovUpper : ℚ :=
  (radiusTwoOrbitCard - 1 : ℕ) / (2 : ℚ) ^ (604 - 128)

/-- Rational form of `radiusTwoGaussianMarkov_powerCertificate`. -/
theorem radiusTwoGaussianMarkovUpper_lt :
    radiusTwoGaussianMarkovUpper < 1 / (2 : ℚ) ^ 338 := by
  unfold radiusTwoGaussianMarkovUpper
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num only [one_mul]
  exact_mod_cast radiusTwoGaussianMarkov_crossCertificate

/-- Exact rational close-shift union bound for the implemented channel. -/
def radiusTwoImplementedChannelUnionUpper : ℚ :=
  (radiusTwoOrbitCard - 1 : ℕ) / (2 : ℚ) ^ 574

/-- Rational form of `radiusTwoImplementedChannelUnion_powerCertificate`. -/
theorem radiusTwoImplementedChannelUnionUpper_lt :
    radiusTwoImplementedChannelUnionUpper < 1 / (2 : ℚ) ^ 436 := by
  unfold radiusTwoImplementedChannelUnionUpper
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  norm_num only [one_mul]
  exact_mod_cast radiusTwoImplementedChannelUnion_powerCertificate

/-- The good-mask upper bound `1+2^-128` on effective overlap is strictly below two. -/
theorem one_add_inv_two_pow_128_lt_two :
    (1 : ℝ) + 1 / (2 : ℝ) ^ 128 < 2 := by
  norm_num

/-- Any positive Renyi order applied to an effective codebook smaller than two returns a
guessing-probability upper bound larger than one half.  Thus such a numerical certificate cannot
establish even one bit, regardless of optimization over `r`. -/
theorem renyiBound_gt_half_of_effective_lt_two
    (r effectiveSize : ℝ) (hr : 0 < r)
    (hone : 1 ≤ effectiveSize) (htwo : effectiveSize < 2) :
    (1 : ℝ) / 2 < effectiveSize ^ (-r / (1 + r)) := by
  have hden : 0 < 1 + r := by linarith
  have hexponent : (-1 : ℝ) < -r / (1 + r) := by
    have hinv : 0 < 1 / (1 + r) := one_div_pos.mpr hden
    have hid : -r / (1 + r) = -1 + 1 / (1 + r) := by
      field_simp
      ring
    rw [hid]
    linarith
  by_cases heq : effectiveSize = 1
  · subst effectiveSize
    norm_num
  · have honeStrict : 1 < effectiveSize := lt_of_le_of_ne hone (Ne.symm heq)
    have hpositive : 0 < effectiveSize := zero_lt_one.trans honeStrict
    have hinverse : (1 : ℝ) / 2 < effectiveSize⁻¹ := by
      simpa only [one_div] using one_div_lt_one_div_of_lt hpositive htwo
    have hpow := Real.rpow_lt_rpow_of_exponent_lt honeStrict hexponent
    rw [Real.rpow_neg_one] at hpow
    exact hinverse.trans hpow

/-- Direct interface to the executable good-mask result: `K <= 1+2^-128` cannot yield a
128-bit guessing certificate at any positive Renyi order. -/
theorem radiusTwoGoodMask_no_128bit_certificate
    (r effectiveSize : ℝ) (hr : 0 < r) (hone : 1 ≤ effectiveSize)
    (hgood : effectiveSize ≤ 1 + 1 / (2 : ℝ) ^ 128) :
    ¬effectiveSize ^ (-r / (1 + r)) ≤ 1 / (2 : ℝ) ^ 128 := by
  have htwo : effectiveSize < 2 :=
    hgood.trans_lt one_add_inv_two_pow_128_lt_two
  have hhalf := renyiBound_gt_half_of_effective_lt_two r effectiveSize hr hone htwo
  have htarget : (1 : ℝ) / (2 : ℝ) ^ 128 < 1 / 2 := by norm_num
  linarith

/-! ## Exact support of the implemented signed lift -/

/-- Source-level support invariant of `doubleToI64Saturating`. -/
def lvl5SignedNoiseSupport (error : ℤ) : Prop :=
  -(2 : ℤ) ^ 63 ≤ error ∧ error < (2 : ℤ) ^ 63

/-- Two supported errors differ in magnitude by strictly less than `2^64`. -/
theorem lvl5SignedNoise_difference_abs_lt
    (left right : ℤ)
    (hleft : lvl5SignedNoiseSupport left)
    (hright : lvl5SignedNoiseSupport right) :
    |left - right| < (2 : ℤ) ^ 64 := by
  simp only [lvl5SignedNoiseSupport] at hleft hright
  rw [abs_lt]
  constructor <;> omega

/-- A mean separation of at least `2^64` cannot be cancelled by two implemented errors. -/
theorem lvl5SignedNoise_translatedSupport_disjoint
    (meanDifference leftError rightError : ℤ)
    (hmean : (2 : ℤ) ^ 64 ≤ |meanDifference|)
    (hleft : lvl5SignedNoiseSupport leftError)
    (hright : lvl5SignedNoiseSupport rightError) :
    meanDifference + leftError ≠ rightError := by
  intro heq
  have hmeanEq : meanDifference = rightError - leftError := by omega
  rw [hmeanEq] at hmean
  have hsmall := lvl5SignedNoise_difference_abs_lt rightError leftError hright hleft
  exact (not_lt_of_ge hmean) hsmall

end

end FormalProof4FHE.RLWE.TFHEppLvl5BootGaussianClusterScreen
