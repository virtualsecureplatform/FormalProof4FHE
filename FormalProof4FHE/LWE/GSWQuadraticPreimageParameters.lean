/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWQuadraticPreimageGSW
import FormalProof4FHE.LWE.RecursiveFeatureBootstrapParameters

/-!
# Noise compatibility for any polynomial correlated-control l1 bound

Use the existing ordinary-source dimension, binary key dimension, wide error
radius and polynomial-bit-length modulus. Reuse its power-of-two lookup, but
evaluate native GSW under the original binary key, without quadratic features.
For ANY fixed polynomial P, control error (1+P(lambda))*radius admits eventual
NAND/refresh/output margins and a reusable output invariant.

This proves parameter compatibility, NOT that a public builder has l1 norm
bounded by P, satisfies its certificates with negligible failure, or has a
verified efficient implementation. Those construction obligations remain.
-/

open scoped BigOperators ENNReal Topology

namespace FormalProof4FHE.LWE.GSWQuadraticPreimageParameters

open RecursiveQuadraticParameters
abbrev dimension : ℕ → ℕ := RecursiveFeatureBootstrapParameters.dimension
abbrev lookupModulus : ℕ → ℕ := RecursiveFeatureBootstrapParameters.lookupModulus
abbrev lookupExponent : ℕ → ℕ := RecursiveFeatureBootstrapParameters.lookupExponent
abbrev factor : ℕ → ℕ := RecursiveFeatureBootstrapParameters.factor
abbrev params := RecursiveFeatureBootstrapParameters.params
abbrev level := RecursiveFeatureBootstrapParameters.level
noncomputable abbrev oneCode (parameter : ℕ) : ZMod (lookupModulus parameter) :=
  RecursiveFeatureBootstrapParameters.oneCode parameter

def growth (parameter : ℕ) := (dimension parameter + 1) * scale parameter ^ 2
def keyBound (normPolynomial : Polynomial ℕ) (parameter : ℕ) :=
  (1 + normPolynomial.eval parameter) * radius parameter
def outputBound (normPolynomial : Polynomial ℕ) (parameter : ℕ) :=
  lookupModulus parameter * dimension parameter * growth parameter * keyBound normPolynomial parameter
def postNandBound (normPolynomial : Polynomial ℕ) (parameter : ℕ) :=
  (growth parameter + 1) * outputBound normPolynomial parameter

theorem dimension_ge (parameter : ℕ) : 2 ≤ dimension parameter := by
  have hs : 1 ≤ scale parameter := by have := scale_pos parameter; omega
  have hp := one_le_pow₀ hs (n := 5)
  change 2 ≤ 2 * scale parameter ^ 5 * 1
  omega

theorem rows_le (parameter : ℕ) :
    dimension parameter + 1 ≤ RecursiveFeatureBootstrapParameters.featureRows parameter := by
  change dimension parameter + 1 ≤ dimension parameter * dimension parameter + dimension parameter + 1
  omega

theorem growth_le (parameter : ℕ) :
    growth parameter ≤ RecursiveFeatureBootstrapParameters.growth parameter :=
  Nat.mul_le_mul_right _ (rows_le parameter)

noncomputable def budgetPolynomial (normPolynomial : Polynomial ℕ) : Polynomial ℕ :=
  let rows := RecursiveFeaturePublicKeyParameters.featureRowsPolynomial
  let g := RecursiveFeatureBootstrapParameters.growthPolynomial
  (16 * rows) ^ 2 * rows * g * (g + 1) * (1 + normPolynomial)

theorem budgetPolynomial_eval (P : Polynomial ℕ) (parameter : ℕ) :
    (budgetPolynomial P).eval parameter =
      (16 * RecursiveFeatureBootstrapParameters.featureRows parameter) ^ 2 *
        RecursiveFeatureBootstrapParameters.featureRows parameter *
        RecursiveFeatureBootstrapParameters.growth parameter *
        (RecursiveFeatureBootstrapParameters.growth parameter + 1) * (1 + P.eval parameter) := by
  simp [budgetPolynomial, RecursiveFeaturePublicKeyParameters.featureRowsPolynomial_eval,
    RecursiveFeatureBootstrapParameters.growthPolynomial_eval]

theorem budget_le_polynomial (P : Polynomial ℕ) (parameter : ℕ) :
    lookupModulus parameter * postNandBound P parameter ≤
      (budgetPolynomial P).eval parameter * radius parameter := by
  rw [budgetPolynomial_eval]
  have hl := RecursiveFeatureBootstrapParameters.lookup_upper parameter
  have hn : dimension parameter ≤ RecursiveFeatureBootstrapParameters.featureRows parameter :=
    (Nat.le_succ _).trans (rows_le parameter)
  have hg := growth_le parameter
  calc
    _ = lookupModulus parameter ^ 2 * dimension parameter * growth parameter *
        (growth parameter + 1) * (1 + P.eval parameter) * radius parameter := by
      unfold postNandBound outputBound keyBound
      ring
    _ ≤ _ := by gcongr

/-- The universal polynomial-bound compatibility test, with no builder premise. -/
theorem eventually_budget (P : Polynomial ℕ) :
    ∀ᶠ parameter in Filter.atTop,
      lookupModulus parameter * postNandBound P parameter < modulus parameter := by
  have hn := negligible_polynomial_mul DiscreteGaussianTail.half_pow_negligible (budgetPolynomial P)
  have hz : Filter.Tendsto
      (fun parameter ↦ (((budgetPolynomial P).eval parameter : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((1 / 2 : ℝ) ^ parameter)) Filter.atTop (nhds 0) := by
    simpa only [pow_zero, one_mul] using hn 0
  have hevent := hz.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  filter_upwards [hevent] with parameter hparameter
  have hr : (((budgetPolynomial P).eval parameter : ℕ) : ℝ) * (1 / 2 : ℝ) ^ parameter < 1 := by
    have hc : ENNReal.ofReal ((((budgetPolynomial P).eval parameter : ℕ) : ℝ) *
        (1 / 2 : ℝ) ^ parameter) < ENNReal.ofReal 1 := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_one]
      exact hparameter
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mp hc
  rw [div_pow, one_pow, mul_one_div] at hr
  have hreal := (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ parameter)).mp hr
  have hnat : (budgetPolynomial P).eval parameter < 2 ^ parameter := by
    have hc : (budgetPolynomial P).eval parameter < 1 * 2 ^ parameter := by exact_mod_cast hreal
    simpa only [one_mul] using hc
  exact (budget_le_polynomial P parameter).trans_lt
    ((Nat.mul_lt_mul_of_pos_right hnat (by unfold radius; positivity)).trans_le
      (radius_times_two_pow_le_modulus parameter))

theorem postNandBound_pos (P : Polynomial ℕ) (parameter : ℕ) : 0 < postNandBound P parameter := by
  have hd := dimension_ge parameter
  have ht := scale_pos parameter
  have hl := NeZero.pos (lookupModulus parameter)
  unfold postNandBound outputBound growth keyBound radius
  positivity

theorem capacity_of_budget (P : Polynomial ℕ) (parameter : ℕ)
    (hbudget : lookupModulus parameter * postNandBound P parameter < modulus parameter) :
    lookupExponent parameter ≤ scale parameter ^ 2 := by
  have hl : lookupModulus parameter ≤ modulus parameter :=
    (Nat.le_mul_of_pos_right _ (postNandBound_pos P parameter)).trans (Nat.le_of_lt hbudget)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  simpa only [lookupModulus, RecursiveFeatureBootstrapParameters.lookupModulus, modulus] using hl

theorem growth_eq (parameter : ℕ) (hcapacity : lookupExponent parameter ≤ scale parameter ^ 2) :
    GSWGadget.growth (params parameter hcapacity) (dimension parameter + 1) = growth parameter := by
  simp [GSWGadget.growth, params, RecursiveFeatureBootstrapParameters.params, growth]

theorem rounding_margin (P : Polynomial ℕ) (parameter : ℕ)
    (hbudget : lookupModulus parameter * postNandBound P parameter < modulus parameter) :
    2 * (postNandBound P parameter + (dimension parameter + 1) * (factor parameter - 1)) <
      factor parameter * TFHE.BootstrappingCorrectness.centeredDistance 0 (oneCode parameter) := by
  have hcap := capacity_of_budget P parameter hbudget
  have hf : postNandBound P parameter ≤ factor parameter := by
    rw [← RecursiveFeatureBootstrapParameters.factor_mul_lookup parameter hcap] at hbudget
    have hh : lookupModulus parameter * postNandBound P parameter <
        lookupModulus parameter * factor parameter := by
      simpa only [Nat.mul_comm (factor parameter) (lookupModulus parameter)] using hbudget
    exact Nat.le_of_lt ((Nat.mul_lt_mul_left (NeZero.pos (lookupModulus parameter))).mp hh)
  have hd := dimension_ge parameter
  have hr := rows_le parameter
  have hl := RecursiveFeatureBootstrapParameters.lookup_lower parameter
  change 8 * RecursiveFeatureBootstrapParameters.featureRows parameter ≤ lookupModulus parameter at hl
  have hhalf : 4 * (dimension parameter + 1) ≤ lookupModulus parameter / 2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    omega
  rw [RecursiveFeatureBootstrapParameters.oneCode_distance]
  calc
    _ ≤ 2 * ((dimension parameter + 2) * factor parameter) := by
      have hsub := Nat.sub_le (factor parameter) 1
      nlinarith
    _ = factor parameter * (2 * (dimension parameter + 2)) := by ring
    _ < factor parameter * (4 * (dimension parameter + 1)) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (NeZero.pos (factor parameter))
    _ ≤ _ := Nat.mul_le_mul_left _ hhalf

theorem output_margin (P : Polynomial ℕ) (parameter : ℕ)
    (hbudget : lookupModulus parameter * postNandBound P parameter < modulus parameter) :
    2 * outputBound P parameter < factor parameter * (lookupModulus parameter / 2) := by
  have hl := RecursiveFeatureBootstrapParameters.lookup_lower parameter
  change 8 * RecursiveFeatureBootstrapParameters.featureRows parameter ≤ lookupModulus parameter at hl
  have hr := RecursiveFeatureBootstrapParameters.featureRows_ge parameter
  have hpost : outputBound P parameter ≤ postNandBound P parameter :=
    Nat.le_mul_of_pos_left _ (by unfold growth; omega)
  have hfour : 4 * outputBound P parameter < modulus parameter :=
    (Nat.mul_le_mul (by omega : 4 ≤ lookupModulus parameter) hpost).trans_lt hbudget
  rw [← RecursiveFeatureBootstrapParameters.factor_mul_lookup parameter (capacity_of_budget P parameter hbudget),
    RecursiveFeatureBootstrapParameters.lookup_even parameter] at hfour
  nlinarith

/-- One NAND followed by refresh returns to the SAME bound; induction permits reuse. -/
theorem noiseBound_refreshedNand (P : Polynomial ℕ) (parameter : ℕ)
    (hbudget : lookupModulus parameter * postNandBound P parameter < modulus parameter)
    (bits : Fin (dimension parameter) → Bool)
    (first second : GSWGadget.Ciphertext
      (params parameter (capacity_of_budget P parameter hbudget)) (dimension parameter + 1))
    (allControls : Fin (dimension parameter) → GSWGadget.Ciphertext
      (params parameter (capacity_of_budget P parameter hbudget)) (dimension parameter + 1))
    (firstBit secondBit : Bool)
    (hcontrols : ∀ index, GSWGadget.NoiseBound (params parameter (capacity_of_budget P parameter hbudget))
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits)) (allControls index)
      (GSWGadget.bitMessage (bits index)) (keyBound P parameter))
    (hfirst : GSWGadget.NoiseBound (params parameter (capacity_of_budget P parameter hbudget))
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits)) first
      (GSWGadget.bitMessage firstBit) (outputBound P parameter))
    (hsecond : GSWGadget.NoiseBound (params parameter (capacity_of_budget P parameter hbudget))
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits)) second
      (GSWGadget.bitMessage secondBit) (outputBound P parameter)) :
    GSWGadget.NoiseBound (params parameter (capacity_of_budget P parameter hbudget))
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (GSWBootstrap.bootstrap (params parameter (capacity_of_budget P parameter hbudget)) allControls
        (GSWGadget.nand (params parameter (capacity_of_budget P parameter hbudget)) first second)
        (level parameter (capacity_of_budget P parameter hbudget)) (oneCode parameter))
      (GSWGadget.bitMessage (!(firstBit && secondBit))) (outputBound P parameter) := by
  have hnand := GSWGadget.noiseBound_nand (params parameter (capacity_of_budget P parameter hbudget))
    (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits)) first second firstBit secondBit
    (outputBound P parameter) (outputBound P parameter) hfirst hsecond
  have hh : GSWGadget.growth (params parameter (capacity_of_budget P parameter hbudget))
      (dimension parameter + 1) * outputBound P parameter + outputBound P parameter = postNandBound P parameter := by
    rw [growth_eq]
    unfold postNandBound
    ring
  rw [hh] at hnand
  have h := GSWBootstrap.noiseBound_bootstrap (params parameter (capacity_of_budget P parameter hbudget))
    bits allControls _ (level parameter (capacity_of_budget P parameter hbudget)) (oneCode parameter)
    (!(firstBit && secondBit)) (postNandBound P parameter) (keyBound P parameter)
    (RecursiveFeatureBootstrapParameters.gadget_eq_up parameter _) hnand hcontrols
    (rounding_margin P parameter hbudget)
  simpa only [growth_eq, outputBound] using h

def publicSamples (parameter : ℕ) := growth parameter + 2 * parameter + 1

/-- Native public encryption has the required leftover-hash cardinality margin. -/
theorem masking_cardinality_margin (parameter : ℕ) :
    modulus parameter ^ (dimension parameter + 1) * 2 ^ (2 * parameter) ≤
      2 ^ publicSamples parameter := by
  unfold modulus publicSamples growth
  rw [← pow_mul, ← pow_add]
  apply pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ))
  have he := Nat.mul_comm (scale parameter ^ 2) (dimension parameter + 1)
  omega

theorem publicEncryptionBound_le_outputBound (P : Polynomial ℕ) (parameter : ℕ) :
    publicSamples parameter * radius parameter ≤ outputBound P parameter := by
  have hd := dimension_ge parameter
  have ht : 1 ≤ scale parameter ^ 2 := one_le_pow₀ (by have := scale_pos parameter; omega)
  have hp : parameter ≤ scale parameter ^ 2 := parameter_le_retries parameter
  have hg : 3 * scale parameter ^ 2 ≤ growth parameter := Nat.mul_le_mul_right _ (by omega)
  have hpublic : publicSamples parameter ≤ 2 * growth parameter := by
    unfold publicSamples
    omega
  have hl := NeZero.pos (lookupModulus parameter)
  have hfactor : 2 ≤ lookupModulus parameter * dimension parameter :=
    hd.trans (Nat.le_mul_of_pos_left _ hl)
  have hbig : 2 * growth parameter ≤
      lookupModulus parameter * dimension parameter * growth parameter * (1 + P.eval parameter) :=
    (Nat.mul_le_mul_right _ hfactor).trans (Nat.le_mul_of_pos_right _ (by omega))
  calc
    _ ≤ (2 * growth parameter) * radius parameter := Nat.mul_le_mul_right _ hpublic
    _ ≤ _ := by simpa only [outputBound, keyBound, Nat.mul_assoc] using Nat.mul_le_mul_right (radius parameter) hbig

/-- The very same modulus/dimension retains the existing ordinary-source entropy margin. -/
theorem entropy_cardinality_margin (parameter : ℕ) :
    modulus parameter ^ sourceDimension parameter * 2 ^ (2 * parameter) ≤ 2 ^ dimension parameter := by
  simpa only [dimension, RecursiveFeatureBootstrapParameters.dimension,
    RecursiveFeaturePublicKeyParameters.dimension, Nat.mul_one] using
    RecursiveQuadraticParameters.entropy_cardinality_margin parameter

theorem decode_refreshedNand (P : Polynomial ℕ) (parameter : ℕ)
    (hbudget : lookupModulus parameter * postNandBound P parameter < modulus parameter)
    (bits : Fin (dimension parameter) → Bool)
    (first second : GSWGadget.Ciphertext
      (params parameter (capacity_of_budget P parameter hbudget)) (dimension parameter + 1))
    (allControls : Fin (dimension parameter) → GSWGadget.Ciphertext
      (params parameter (capacity_of_budget P parameter hbudget)) (dimension parameter + 1))
    (firstBit secondBit : Bool)
    (hcontrols : ∀ index, GSWGadget.NoiseBound (params parameter (capacity_of_budget P parameter hbudget))
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits)) (allControls index)
      (GSWGadget.bitMessage (bits index)) (keyBound P parameter))
    (hfirst : GSWGadget.NoiseBound (params parameter (capacity_of_budget P parameter hbudget))
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits)) first
      (GSWGadget.bitMessage firstBit) (outputBound P parameter))
    (hsecond : GSWGadget.NoiseBound (params parameter (capacity_of_budget P parameter hbudget))
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits)) second
      (GSWGadget.bitMessage secondBit) (outputBound P parameter)) :
    GSWGadget.decrypt (params parameter (capacity_of_budget P parameter hbudget))
      (GSWSelfKey.binaryEmbed bits)
      (GSWBootstrap.bootstrap (params parameter (capacity_of_budget P parameter hbudget)) allControls
        (GSWGadget.nand (params parameter (capacity_of_budget P parameter hbudget)) first second)
        (level parameter (capacity_of_budget P parameter hbudget)) (oneCode parameter))
      (level parameter (capacity_of_budget P parameter hbudget)) = !(firstBit && secondBit) := by
  apply GSWGadget.decrypt_eq_bit _ _ _ _ (outputBound P parameter)
  · exact noiseBound_refreshedNand P parameter hbudget bits first second allControls
      firstBit secondBit hcontrols hfirst hsecond
  · rw [RecursiveFeatureBootstrapParameters.gadget_distance]
    exact output_margin P parameter hbudget

end FormalProof4FHE.LWE.GSWQuadraticPreimageParameters
