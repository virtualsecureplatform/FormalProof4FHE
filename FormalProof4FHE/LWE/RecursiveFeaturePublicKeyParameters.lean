/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveFeaturePublicKey
import FormalProof4FHE.LWE.RecursivePublicKeyParameters

/-!
# Parameters for full-coordinate recursive-feature public encryption

The sample count pays for the entire flattened quadratic feature vector and all
GSW columns. The resulting public-encryption experiment has a negligible masking
term, polynomial source rows, and eventual supported correctness under one
binary underlying secret. Fixed quadratic context is retained in its security
experiment. Cubic refresh controls and reusable bootstrapping are not covered.
-/

open OracleComp AsymmEncAlg
open scoped ENNReal Topology

namespace FormalProof4FHE.LWE.RecursiveFeaturePublicKeyParameters

open RecursiveQuadraticParameters

abbrev dimension (parameter : ℕ) := binaryDimension parameter * 1

def featureRows (parameter : ℕ) : ℕ := dimension parameter * dimension parameter + dimension parameter + 1

def params (parameter : ℕ) : GSWGadget.Parameters (modulus parameter) where
  base := 2
  levels := scale parameter ^ 2
  one_lt_base := by decide
  modulus_le_capacity := by unfold modulus; rfl

def level (parameter : ℕ) : Fin (params parameter).levels :=
  ⟨scale parameter ^ 2 - 1, Nat.sub_lt (pow_pos (scale_pos parameter) 2) (by decide)⟩

def publicSamples (parameter : ℕ) : ℕ :=
  featureRows parameter * scale parameter ^ 2 + 2 * parameter + 1

noncomputable def featureRowsPolynomial : Polynomial ℕ :=
  (2 * (Polynomial.X + 1) ^ 5) ^ 2 + 2 * (Polynomial.X + 1) ^ 5 + 1

noncomputable def publicSamplesPolynomial : Polynomial ℕ :=
  featureRowsPolynomial * (Polynomial.X + 1) ^ 2 + 2 * Polynomial.X + 1

theorem featureRowsPolynomial_eval (parameter : ℕ) :
    featureRowsPolynomial.eval parameter = featureRows parameter := by
  simp [featureRowsPolynomial, featureRows, binaryDimension, scale, pow_two]

theorem publicSamplesPolynomial_eval (parameter : ℕ) :
    publicSamplesPolynomial.eval parameter = publicSamples parameter := by
  simp [publicSamplesPolynomial, publicSamples, featureRowsPolynomial_eval, scale]

theorem masking_cardinality_margin (parameter : ℕ) :
    modulus parameter ^ featureRows parameter * 2 ^ (2 * parameter) ≤ 2 ^ publicSamples parameter := by
  unfold modulus publicSamples
  rw [← pow_mul, ← pow_add]
  apply pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ))
  have he := Nat.mul_comm (scale parameter ^ 2) (featureRows parameter)
  omega

noncomputable def maskingPerColumnBound (parameter : ℕ) : ℝ :=
  Real.sqrt ((modulus parameter : ℝ) ^ featureRows parameter / (2 : ℝ) ^ publicSamples parameter) / 2

noncomputable def maskingBound (parameter : ℕ) : ℝ :=
  (featureRows parameter * scale parameter ^ 2 : ℕ) * maskingPerColumnBound parameter

theorem maskingPerColumnBound_le_half_pow (parameter : ℕ) :
    maskingPerColumnBound parameter ≤ (1 / 2 : ℝ) ^ parameter := by
  have hmargin : (modulus parameter : ℝ) ^ featureRows parameter *
      (2 : ℝ) ^ (2 * parameter) ≤ (2 : ℝ) ^ publicSamples parameter := by
    exact_mod_cast masking_cardinality_margin parameter
  have hsqrt : Real.sqrt ((modulus parameter : ℝ) ^ featureRows parameter /
      (2 : ℝ) ^ publicSamples parameter) ≤ (1 / 2 : ℝ) ^ parameter := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 1 / (2 : ℝ) ^ (2 * parameter) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        simpa only [one_mul] using hmargin
      _ = _ := by rw [div_pow, one_pow, div_pow, one_pow, ← pow_mul, Nat.mul_comm parameter 2]
  unfold maskingPerColumnBound
  have hnonneg := Real.sqrt_nonneg
    ((modulus parameter : ℝ) ^ featureRows parameter /
      (2 : ℝ) ^ publicSamples parameter)
  linarith

theorem maskingBound_le_polynomial_half_pow (parameter : ℕ) :
    maskingBound parameter ≤ (featureRows parameter * scale parameter ^ 2 : ℕ) * (1 / 2 : ℝ) ^ parameter :=
  mul_le_mul_of_nonneg_left (maskingPerColumnBound_le_half_pow parameter) (Nat.cast_nonneg _)

theorem maskingBound_negligible :
    negligible (fun parameter ↦ ENNReal.ofReal (maskingBound parameter)) := by
  apply negligible_of_le (g := fun parameter ↦
    ((featureRows parameter * scale parameter ^ 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ parameter))
  · intro parameter
    have h := ENNReal.ofReal_le_ofReal (maskingBound_le_polynomial_half_pow parameter)
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using h
  · have h := negligible_polynomial_mul DiscreteGaussianTail.half_pow_negligible
      (featureRowsPolynomial * (Polynomial.X + 1) ^ 2)
    simpa [featureRowsPolynomial_eval, scale] using h

/-- The extra n+1 factor pays for each recursive zero-column's supported phase error. -/
def selectorBound (parameter : ℕ) : ℕ := publicSamples parameter * (dimension parameter + 1)

noncomputable def selectorBoundPolynomial : Polynomial ℕ :=
  publicSamplesPolynomial * (2 * (Polynomial.X + 1) ^ 5 + 1)

theorem selectorBoundPolynomial_eval (parameter : ℕ) :
    selectorBoundPolynomial.eval parameter = selectorBound parameter := by
  simp [selectorBoundPolynomial, selectorBound, publicSamplesPolynomial_eval, binaryDimension, scale]

theorem eventually_public_quarter_margin :
    ∀ᶠ parameter in Filter.atTop,
      4 * selectorBound parameter * radius parameter < modulus parameter := by
  let polynomial : Polynomial ℕ := 4 * selectorBoundPolynomial
  have hn := negligible_polynomial_mul DiscreteGaussianTail.half_pow_negligible polynomial
  have hz : Filter.Tendsto
      (fun parameter ↦ ((polynomial.eval parameter : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((1 / 2 : ℝ) ^ parameter)) Filter.atTop (nhds 0) := by
    simpa only [pow_zero, one_mul] using hn 0
  have hevent := hz.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  filter_upwards [hevent] with parameter hparameter
  have hr : ((4 * selectorBound parameter : ℕ) : ℝ) * (1 / 2 : ℝ) ^ parameter < 1 := by
    have hc : ENNReal.ofReal (((4 * selectorBound parameter : ℕ) : ℝ) *
        (1 / 2 : ℝ) ^ parameter) < ENNReal.ofReal 1 := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_one]
      simpa [polynomial, selectorBoundPolynomial_eval] using hparameter
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mp hc
  rw [div_pow, one_pow, mul_one_div] at hr
  have hreal := (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ parameter)).mp hr
  have hnat : 4 * selectorBound parameter < 2 ^ parameter := by
    have ht : ((4 * selectorBound parameter : ℕ) : ℝ) < ((2 ^ parameter : ℕ) : ℝ) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, one_mul] using hreal
    exact_mod_cast ht
  exact (Nat.mul_lt_mul_of_pos_right hnat (by unfold radius; positivity)).trans_le
    (radius_times_two_pow_le_modulus parameter)

theorem gadget_distance (parameter : ℕ) :
    TFHE.BootstrappingCorrectness.centeredDistance 0 (TFHE.Gadget.Base.gadget (params parameter) (level parameter)) =
      modulus parameter / 2 := by
  have hexp : 0 < scale parameter ^ 2 := by have := scale_pos parameter; positivity
  have hhalf : modulus parameter / 2 = 2 ^ (scale parameter ^ 2 - 1) := by
    have hp : modulus parameter = 2 * 2 ^ (scale parameter ^ 2 - 1) := by
      unfold modulus
      rw [← pow_succ']
      congr 1
    rw [hp]
    simp
  rw [← RecursivePublicKeyParameters.oneCode_distance]
  congr 1
  simp only [TFHE.Gadget.Base.gadget, params, level, RecursivePublicKeyParameters.oneCode, hhalf, Nat.cast_pow,
    Nat.cast_ofNat]

def sampleRows (parameter linear hints : ℕ) : ℕ :=
  linear + (publicSamples parameter + hints) * (dimension parameter + 1)

noncomputable def sampleRowsPolynomial (linear hints : Polynomial ℕ) : Polynomial ℕ :=
  linear + (publicSamplesPolynomial + hints) * (2 * (Polynomial.X + 1) ^ 5 + 1)

theorem sampleRowsPolynomial_eval (linear hints : Polynomial ℕ) (parameter : ℕ) :
    (sampleRowsPolynomial linear hints).eval parameter = sampleRows parameter (linear.eval parameter) (hints.eval parameter) := by
  simp [sampleRowsPolynomial, sampleRows, publicSamplesPolynomial_eval, binaryDimension, scale]

theorem family_implementationLoss_negligible (linear hints : Polynomial ℕ) :
    negligible (fun parameter ↦ ENNReal.ofReal
      (implementationLoss (sampleRows parameter (linear.eval parameter) (hints.eval parameter)) parameter)) := by
  simpa only [sampleRowsPolynomial_eval] using implementationLoss_negligible (sampleRowsPolynomial linear hints)

noncomputable def family (parameter linear hints : ℕ)
    (tail : RecursiveQuadratic.Polynomial (ZMod (modulus parameter)) (dimension parameter) hints) :=
  RecursiveFeaturePublicKey.scheme (params parameter) (level parameter)
    (RecursiveQuadratic.columnsEquiv (dimension parameter) linear (publicSamples parameter + hints)) tail
    (RecursivePublicKeyParameters.secretSampler parameter)
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))

noncomputable def familyAdversary (parameter linear hints : ℕ)
    (tail : RecursiveQuadratic.Polynomial (ZMod (modulus parameter)) (dimension parameter) hints)
    (adversary : IND_CPA_Adv (family parameter linear hints tail)) :
    RecursiveFeaturePublicKey.Adversary (n := dimension parameter) (r := linear) (p := publicSamples parameter)
      (k := hints) (params parameter) :=
  RecursiveFeaturePublicKey.fromINDCPA (params parameter) (level parameter)
    (RecursiveQuadratic.columnsEquiv (dimension parameter) linear (publicSamples parameter + hints)) tail
    (RecursivePublicKeyParameters.secretSampler parameter)
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) adversary

/-- All computational terms are observers of uniform-secret ordinary LWE at the source. -/
theorem oneTime_abs_signedAdvantage_le (parameter linear hints : ℕ)
    (tail : RecursiveQuadratic.Polynomial (ZMod (modulus parameter)) (dimension parameter) hints)
    (adversary : IND_CPA_Adv (family parameter linear hints tail)) :
    |IND_CPA_OneTime_signedAdvantageReal (family parameter linear hints tail) adversary| ≤
      ordinaryReductionLoss parameter
        (RecursiveQuadratic.columnsEquiv (dimension parameter) linear (publicSamples parameter + hints))
        (RecursiveFeaturePublicKey.joinedPolynomial tail)
        (fun original ↦ RecursiveFeaturePublicKey.observe (params parameter)
          (familyAdversary parameter linear hints tail adversary) (RecursiveFeaturePublicKey.publish original)) +
      implementationLoss (sampleRows parameter linear hints) parameter + maskingBound parameter := by
  have hgame := RecursiveFeaturePublicKey.oneTime_game_evalDist (params parameter) (level parameter)
    (RecursiveQuadratic.columnsEquiv (dimension parameter) linear (publicSamples parameter + hints)) tail
    (RecursivePublicKeyParameters.secretSampler parameter)
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) adversary
  have hbound := RecursiveFeaturePublicKey.sampled_game_abs_advantage_le parameter (params parameter)
    (RecursiveQuadratic.columnsEquiv (dimension parameter) linear (publicSamples parameter + hints)) tail
    (familyAdversary parameter linear hints tail adversary)
  unfold IND_CPA_OneTime_signedAdvantageReal family
  rw [probOutput_congr (rfl : true = true) hgame]
  simpa only [familyAdversary, RecursivePublicKeyParameters.secretSampler, maskingBound, maskingPerColumnBound,
    featureRows, sampleRows, params, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hbound

/-- For sufficiently large parameters, every supported fresh encryption decodes correctly. -/
theorem correctExp_probability_one (parameter linear hints : ℕ)
    (hmargin : 4 * selectorBound parameter * radius parameter < modulus parameter)
    (tail : RecursiveQuadratic.Polynomial (ZMod (modulus parameter)) (dimension parameter) hints) (bit : Bool) :
    Pr[= true | (family parameter linear hints tail).CorrectExp bit] = 1 := by
  apply RecursiveFeaturePublicKey.correctExp_probability_one (params parameter) (level parameter)
    (RecursiveQuadratic.columnsEquiv (dimension parameter) linear (publicSamples parameter + hints)) tail
    (RecursivePublicKeyParameters.secretSampler parameter)
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) (radius parameter)
  · intro secret hsecret row
    obtain ⟨key, _, hkey⟩ := mem_support_map_peel _ _ hsecret
    subst secret
    simp only [BlockBinary.expand]
    split_ifs <;> simp
  · exact fun error herror ↦ UniformInterval.sample_support_centered_bound _ _ _ error herror
  · rw [gadget_distance]
    have heven := RecursivePublicKeyParameters.modulus_eq_two_mul_half parameter
    have heq : 4 * selectorBound parameter * radius parameter =
        2 * (2 * (publicSamples parameter * ((dimension parameter + 1) * radius parameter))) := by
      unfold selectorBound
      ring
    omega

theorem eventually_correctExp_probability_one :
    ∀ᶠ parameter in Filter.atTop, ∀ linear hints : ℕ,
      ∀ tail : RecursiveQuadratic.Polynomial (ZMod (modulus parameter)) (dimension parameter) hints, ∀ bit : Bool,
        Pr[= true | (family parameter linear hints tail).CorrectExp bit] = 1 := by
  filter_upwards [eventually_public_quarter_margin] with parameter hmargin
  intro linear hints tail bit
  exact correctExp_probability_one parameter linear hints hmargin tail bit

end FormalProof4FHE.LWE.RecursiveFeaturePublicKeyParameters
