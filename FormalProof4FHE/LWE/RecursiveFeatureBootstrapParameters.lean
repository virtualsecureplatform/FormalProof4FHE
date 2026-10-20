/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveFeatureBootstrap
import FormalProof4FHE.LWE.RecursiveFeaturePublicKeyParameters
import Mathlib.Data.Nat.Log

/-!
# Compatible parameters for recursive-feature NAND and refresh

The coefficient modulus, binary dimension, scalar-error radius and base-two
gadget match the existing fresh public-encryption security family. Round to the
least power of two at least eight times the number of features. This lookup has
polynomial size. A polynomial bound and the existing negligible geometric bound
prove eventual compatibility, rounding, and output-decoding margins.

These are correctness parameters. Original-bit cubic control security and
polynomial-time implementations/reductions are still required for the FHE goal.
-/

open scoped ENNReal Topology

namespace FormalProof4FHE.LWE.RecursiveFeatureBootstrapParameters

open RecursiveQuadraticParameters

abbrev dimension (parameter : ℕ) := RecursiveFeaturePublicKeyParameters.dimension parameter
abbrev featureRows (parameter : ℕ) := RecursiveFeaturePublicKeyParameters.featureRows parameter

theorem rows_eq_featureRows (parameter : ℕ) :
    RecursiveFeatureGSW.rows (dimension parameter) = featureRows parameter := by
  simp [RecursiveFeatureGSW.rows, featureRows, dimension, RecursiveFeaturePublicKeyParameters.featureRows]

def growth (parameter : ℕ) : ℕ := featureRows parameter * scale parameter ^ 2
@[irreducible] def lookupExponent (parameter : ℕ) : ℕ := Nat.clog 2 (8 * featureRows parameter)
@[irreducible] def lookupModulus (parameter : ℕ) : ℕ := 2 ^ lookupExponent parameter
@[irreducible] def factor (parameter : ℕ) : ℕ := 2 ^ (scale parameter ^ 2 - lookupExponent parameter)
def keyBound (parameter : ℕ) : ℕ := (dimension parameter + 1) * radius parameter
def outputBound (parameter : ℕ) : ℕ :=
  lookupModulus parameter * featureRows parameter * growth parameter *
    ((growth parameter + 1) * keyBound parameter)
def postNandBound (parameter : ℕ) : ℕ := (growth parameter + 1) * outputBound parameter

theorem featureRows_ge (parameter : ℕ) : 3 ≤ featureRows parameter := by
  have ht := scale_pos parameter
  have hd : 2 ≤ dimension parameter := by
    change 2 ≤ 2 * scale parameter ^ 5 * 1
    have hpow : 1 ≤ scale parameter ^ 5 := one_le_pow₀ (by omega)
    omega
  change 3 ≤ dimension parameter * dimension parameter + dimension parameter + 1
  omega

theorem lookup_lower (parameter : ℕ) : 8 * featureRows parameter ≤ lookupModulus parameter :=
  by simpa only [lookupModulus, lookupExponent] using Nat.le_pow_clog (by decide : 1 < 2) (8 * featureRows parameter)

theorem lookup_upper (parameter : ℕ) : lookupModulus parameter ≤ 16 * featureRows parameter := by
  have hr := featureRows_ge parameter
  have hk : 0 < lookupExponent parameter := by
    unfold lookupExponent
    exact Nat.clog_pos (by decide) (by omega)
  have h := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
    (by omega : 1 < 8 * featureRows parameter)
  change 2 ^ (Nat.clog 2 (8 * featureRows parameter)).pred < 8 * featureRows parameter at h
  have hsmall : 2 ^ (lookupExponent parameter).pred < 8 * featureRows parameter := by
    simpa only [lookupExponent] using h
  have heq : lookupExponent parameter = (lookupExponent parameter).pred + 1 :=
    (Nat.succ_pred_eq_of_pos hk).symm
  unfold lookupModulus
  rw [heq, pow_succ]
  omega

instance (parameter : ℕ) : NeZero (lookupModulus parameter) := ⟨by unfold lookupModulus; positivity⟩
instance (parameter : ℕ) : NeZero (factor parameter) := ⟨by unfold factor; positivity⟩

theorem lookup_even (parameter : ℕ) : lookupModulus parameter = 2 * (lookupModulus parameter / 2) := by
  have hr := featureRows_ge parameter
  have hk : 0 < lookupExponent parameter := by
    unfold lookupExponent
    exact Nat.clog_pos (by decide) (by omega)
  have heq : lookupExponent parameter = lookupExponent parameter - 1 + 1 := by omega
  have hp : lookupModulus parameter = 2 * 2 ^ (lookupExponent parameter - 1) := by
    unfold lookupModulus
    calc
      _ = 2 ^ (lookupExponent parameter - 1 + 1) := by exact congrArg (fun exponent : ℕ ↦ (2 : ℕ) ^ exponent) heq
      _ = _ := pow_succ' _ _
  rw [hp]
  simp

theorem factor_mul_lookup (parameter : ℕ) (hcapacity : lookupExponent parameter ≤ scale parameter ^ 2) :
    factor parameter * lookupModulus parameter = modulus parameter := by
  simp only [factor, lookupModulus, modulus, ← pow_add, Nat.sub_add_cancel hcapacity]

noncomputable def growthPolynomial : Polynomial ℕ :=
  RecursiveFeaturePublicKeyParameters.featureRowsPolynomial * (Polynomial.X + 1) ^ 2

noncomputable def budgetPolynomial : Polynomial ℕ :=
  (16 * RecursiveFeaturePublicKeyParameters.featureRowsPolynomial) ^ 2 *
    RecursiveFeaturePublicKeyParameters.featureRowsPolynomial * growthPolynomial *
    (growthPolynomial + 1) ^ 2 * (2 * (Polynomial.X + 1) ^ 5 + 1)

theorem growthPolynomial_eval (parameter : ℕ) : growthPolynomial.eval parameter = growth parameter := by
  simp [growthPolynomial, growth, RecursiveFeaturePublicKeyParameters.featureRowsPolynomial_eval, scale]

theorem budgetPolynomial_eval (parameter : ℕ) :
    budgetPolynomial.eval parameter = (16 * featureRows parameter) ^ 2 *
      featureRows parameter * growth parameter * (growth parameter + 1) ^ 2 * (dimension parameter + 1) := by
  simp [budgetPolynomial, growthPolynomial_eval,
    RecursiveFeaturePublicKeyParameters.featureRowsPolynomial_eval, dimension,
    RecursiveFeaturePublicKeyParameters.dimension, binaryDimension, scale]

/-- This pays for one extra lookup factor after the complete product-control and NAND errors. -/
theorem budget_le_polynomial (parameter : ℕ) :
    lookupModulus parameter * postNandBound parameter ≤ budgetPolynomial.eval parameter * radius parameter := by
  rw [budgetPolynomial_eval]
  have h := lookup_upper parameter
  calc
    _ = lookupModulus parameter ^ 2 * featureRows parameter * growth parameter *
        (growth parameter + 1) ^ 2 * (dimension parameter + 1) * radius parameter := by
      unfold postNandBound outputBound keyBound
      ring
    _ ≤ _ := by gcongr

theorem eventually_budget :
    ∀ᶠ parameter in Filter.atTop, lookupModulus parameter * postNandBound parameter < modulus parameter := by
  have hn := negligible_polynomial_mul DiscreteGaussianTail.half_pow_negligible budgetPolynomial
  have hz : Filter.Tendsto
      (fun parameter ↦ ((budgetPolynomial.eval parameter : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((1 / 2 : ℝ) ^ parameter)) Filter.atTop (nhds 0) := by
    simpa only [pow_zero, one_mul] using hn 0
  have hevent := hz.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  filter_upwards [hevent] with parameter hparameter
  have hr : ((budgetPolynomial.eval parameter : ℕ) : ℝ) * (1 / 2 : ℝ) ^ parameter < 1 := by
    have hc : ENNReal.ofReal (((budgetPolynomial.eval parameter : ℕ) : ℝ) * (1 / 2 : ℝ) ^ parameter) <
        ENNReal.ofReal 1 := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_one]
      exact hparameter
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mp hc
  rw [div_pow, one_pow, mul_one_div] at hr
  have hreal := (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ parameter)).mp hr
  have hnat : budgetPolynomial.eval parameter < 2 ^ parameter := by
    have hc : budgetPolynomial.eval parameter < 1 * 2 ^ parameter := by exact_mod_cast hreal
    simpa only [one_mul] using hc
  exact (budget_le_polynomial parameter).trans_lt
    ((Nat.mul_lt_mul_of_pos_right hnat (by unfold radius; positivity)).trans_le
      (radius_times_two_pow_le_modulus parameter))

theorem postNandBound_pos (parameter : ℕ) : 0 < postNandBound parameter := by
  have hr := featureRows_ge parameter
  have ht := scale_pos parameter
  have hp := NeZero.pos (lookupModulus parameter)
  unfold postNandBound outputBound growth keyBound radius
  positivity

theorem capacity_of_budget (parameter : ℕ)
    (hbudget : lookupModulus parameter * postNandBound parameter < modulus parameter) :
    lookupExponent parameter ≤ scale parameter ^ 2 := by
  have hlookup : lookupModulus parameter ≤ modulus parameter :=
    (Nat.le_mul_of_pos_right _ (postNandBound_pos parameter)).trans (Nat.le_of_lt hbudget)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  simpa only [lookupModulus, modulus] using hlookup

def params (parameter : ℕ) (hcapacity : lookupExponent parameter ≤ scale parameter ^ 2) :
    GSWGadget.Parameters (factor parameter * lookupModulus parameter) where
  base := 2
  levels := scale parameter ^ 2
  one_lt_base := by decide
  modulus_le_capacity := by rw [factor_mul_lookup parameter hcapacity]; unfold modulus; rfl

def level (parameter : ℕ) (hcapacity : lookupExponent parameter ≤ scale parameter ^ 2) :
    Fin (params parameter hcapacity).levels :=
  ⟨scale parameter ^ 2 - 1, Nat.sub_lt (pow_pos (scale_pos parameter) 2) (by decide)⟩

def halfCode (p : ℕ) : ZMod p := (p / 2 : ℕ)

noncomputable def oneCode (parameter : ℕ) : ZMod (lookupModulus parameter) := halfCode (lookupModulus parameter)

theorem growth_eq (parameter : ℕ) (hcapacity : lookupExponent parameter ≤ scale parameter ^ 2) :
    GSWGadget.growth (params parameter hcapacity) (featureRows parameter) =
      growth parameter := by
  simp [GSWGadget.growth, params, growth]

theorem gadget_eq_up (parameter : ℕ) (hcapacity : lookupExponent parameter ≤ scale parameter ^ 2) :
    TFHE.Gadget.Base.gadget (params parameter hcapacity) (level parameter hcapacity) =
      GSWModulusSwitch.up (factor parameter) (lookupModulus parameter) (oneCode parameter) := by
  have hr := featureRows_ge parameter
  have hk : 0 < lookupExponent parameter := by
    unfold lookupExponent
    exact Nat.clog_pos (by decide) (by omega)
  have heq : lookupExponent parameter = lookupExponent parameter - 1 + 1 := by omega
  have hp : lookupModulus parameter = 2 * 2 ^ (lookupExponent parameter - 1) := by
    unfold lookupModulus
    calc
      _ = 2 ^ (lookupExponent parameter - 1 + 1) := by exact congrArg (fun exponent : ℕ ↦ (2 : ℕ) ^ exponent) heq
      _ = _ := pow_succ' _ _
  have hhalf : lookupModulus parameter / 2 = 2 ^ (lookupExponent parameter - 1) := by
    rw [hp]
    simp
  rw [oneCode, halfCode, GSWModulusSwitch.up_natCast, hhalf]
  simp only [TFHE.Gadget.Base.gadget, params, level, factor, Nat.cast_pow, Nat.cast_ofNat,
    ← pow_add]
  congr 1
  omega

theorem oneCode_distance (parameter : ℕ) :
    TFHE.BootstrappingCorrectness.centeredDistance 0 (oneCode parameter) = lookupModulus parameter / 2 := by
  rw [TFHE.BootstrappingCorrectness.centeredDistance_symm]
  change (LatticeCrypto.centeredRepr ((oneCode parameter) - 0)).natAbs = _
  rw [sub_zero, oneCode, halfCode, LatticeCrypto.centeredRepr_eq_valMinAbs,
    ZMod.valMinAbs_natCast_of_le_half (le_refl (lookupModulus parameter / 2))]
  exact Int.natAbs_natCast _

theorem rounding_margin (parameter : ℕ)
    (hbudget : lookupModulus parameter * postNandBound parameter < modulus parameter) :
    2 * (postNandBound parameter + (featureRows parameter + 1) * (factor parameter - 1)) <
      factor parameter * TFHE.BootstrappingCorrectness.centeredDistance 0 (oneCode parameter) := by
  have hcap := capacity_of_budget parameter hbudget
  have hfactor : postNandBound parameter ≤ factor parameter := by
    rw [← factor_mul_lookup parameter hcap] at hbudget
    have hh : lookupModulus parameter * postNandBound parameter <
        lookupModulus parameter * factor parameter := by
      simpa only [Nat.mul_comm (factor parameter) (lookupModulus parameter)] using hbudget
    have h := (Nat.mul_lt_mul_left (NeZero.pos (lookupModulus parameter))).mp hh
    omega
  have hr := featureRows_ge parameter
  have hp := lookup_lower parameter
  have hhalf : 4 * featureRows parameter ≤ lookupModulus parameter / 2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    omega
  rw [oneCode_distance]
  calc
    _ ≤ 2 * ((featureRows parameter + 2) * factor parameter) := by
      have hsub := Nat.sub_le (factor parameter) 1
      nlinarith
    _ = factor parameter * (2 * (featureRows parameter + 2)) := by ring
    _ < factor parameter * (4 * featureRows parameter) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (NeZero.pos (factor parameter))
    _ ≤ _ := Nat.mul_le_mul_left _ hhalf

theorem outputBound_le_postNandBound (parameter : ℕ) : outputBound parameter ≤ postNandBound parameter :=
  Nat.le_mul_of_pos_left _ (by omega)

theorem output_margin (parameter : ℕ)
    (hbudget : lookupModulus parameter * postNandBound parameter < modulus parameter) :
    2 * outputBound parameter < factor parameter * (lookupModulus parameter / 2) := by
  have hp := lookup_lower parameter
  have hr := featureRows_ge parameter
  have hfour : 4 * outputBound parameter < modulus parameter :=
    (Nat.mul_le_mul (by omega : 4 ≤ lookupModulus parameter)
      (outputBound_le_postNandBound parameter)).trans_lt hbudget
  rw [← factor_mul_lookup parameter (capacity_of_budget parameter hbudget), lookup_even parameter] at hfour
  nlinarith

theorem gadget_distance (parameter : ℕ) (hcapacity : lookupExponent parameter ≤ scale parameter ^ 2) :
    TFHE.BootstrappingCorrectness.centeredDistance 0
      (TFHE.Gadget.Base.gadget (params parameter hcapacity) (level parameter hcapacity)) =
      factor parameter * (lookupModulus parameter / 2) := by
  rw [gadget_eq_up, TFHE.BootstrappingCorrectness.centeredDistance_symm]
  change (LatticeCrypto.centeredRepr (GSWModulusSwitch.up (factor parameter)
    (lookupModulus parameter) (oneCode parameter) - 0)).natAbs = _
  rw [sub_zero, GSWModulusSwitch.centered_up]
  have h := oneCode_distance parameter
  rw [TFHE.BootstrappingCorrectness.centeredDistance_symm] at h
  change (LatticeCrypto.centeredRepr (oneCode parameter - 0)).natAbs = _ at h
  simpa only [sub_zero] using congrArg (fun value ↦ factor parameter * value) h

theorem publicEncryptionBound_le_outputBound (parameter : ℕ) :
    RecursiveFeaturePublicKeyParameters.publicSamples parameter * keyBound parameter ≤ outputBound parameter := by
  have hr := featureRows_ge parameter
  have ht : 1 ≤ scale parameter ^ 2 := one_le_pow₀ (by have := scale_pos parameter; omega)
  have hp := lookup_lower parameter
  have hl := parameter_le_retries parameter
  change parameter ≤ scale parameter ^ 2 at hl
  have hg : 3 * scale parameter ^ 2 ≤ growth parameter := Nat.mul_le_mul_right _ hr
  have hpublic : RecursiveFeaturePublicKeyParameters.publicSamples parameter ≤ 2 * growth parameter := by
    change growth parameter + 2 * parameter + 1 ≤ 2 * growth parameter
    omega
  have hfactor : 2 ≤ lookupModulus parameter * featureRows parameter * (growth parameter + 1) := by
    calc
      2 ≤ lookupModulus parameter := by omega
      _ ≤ lookupModulus parameter * featureRows parameter := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  have hc : RecursiveFeaturePublicKeyParameters.publicSamples parameter ≤
      lookupModulus parameter * featureRows parameter * growth parameter * (growth parameter + 1) := by
    have hh := Nat.mul_le_mul_right (growth parameter) hfactor
    nlinarith
  simpa only [outputBound, Nat.mul_assoc] using Nat.mul_le_mul_right (keyBound parameter) hc

theorem noiseBound_refreshedNand (parameter : ℕ)
    (hbudget : lookupModulus parameter * postNandBound parameter < modulus parameter)
    (bits : Fin (dimension parameter) → Bool)
    (original : Fin (dimension parameter) → RecursiveFeatureGSW.Batch
      (params parameter (capacity_of_budget parameter hbudget)) (dimension parameter))
    (first second : RecursiveFeatureGSW.Batch
      (params parameter (capacity_of_budget parameter hbudget)) (dimension parameter))
    (firstBit secondBit : Bool)
    (hcontrols : ∀ index, RecursiveFeatureGSW.NoiseBound
      (params parameter (capacity_of_budget parameter hbudget)) (GSWSelfKey.binaryEmbed bits) (original index)
      (GSWGadget.bitMessage (bits index)) (keyBound parameter))
    (hfirst : RecursiveFeatureGSW.NoiseBound (params parameter (capacity_of_budget parameter hbudget))
      (GSWSelfKey.binaryEmbed bits) first (GSWGadget.bitMessage firstBit) (outputBound parameter))
    (hsecond : RecursiveFeatureGSW.NoiseBound (params parameter (capacity_of_budget parameter hbudget))
      (GSWSelfKey.binaryEmbed bits) second (GSWGadget.bitMessage secondBit) (outputBound parameter)) :
    RecursiveFeatureGSW.NoiseBound (params parameter (capacity_of_budget parameter hbudget))
      (GSWSelfKey.binaryEmbed bits)
      (RecursiveFeatureBootstrap.refreshedNand (params parameter (capacity_of_budget parameter hbudget))
        original first second (level parameter (capacity_of_budget parameter hbudget)) (oneCode parameter))
      (GSWGadget.bitMessage (!(firstBit && secondBit))) (outputBound parameter) := by
  have h := RecursiveFeatureBootstrap.noiseBound_refreshedNand
    (params parameter (capacity_of_budget parameter hbudget)) bits original first second
    (level parameter (capacity_of_budget parameter hbudget)) (oneCode parameter) firstBit secondBit
    (outputBound parameter) (keyBound parameter) (gadget_eq_up parameter _) hfirst hsecond hcontrols
    (by simpa only [growth_eq, rows_eq_featureRows, postNandBound] using rounding_margin parameter hbudget)
  simpa only [growth_eq, rows_eq_featureRows, outputBound] using h

theorem decode_refreshedNand (parameter : ℕ)
    (hbudget : lookupModulus parameter * postNandBound parameter < modulus parameter)
    (bits : Fin (dimension parameter) → Bool)
    (original : Fin (dimension parameter) → RecursiveFeatureGSW.Batch
      (params parameter (capacity_of_budget parameter hbudget)) (dimension parameter))
    (first second : RecursiveFeatureGSW.Batch
      (params parameter (capacity_of_budget parameter hbudget)) (dimension parameter))
    (firstBit secondBit : Bool)
    (hcontrols : ∀ index, RecursiveFeatureGSW.NoiseBound
      (params parameter (capacity_of_budget parameter hbudget)) (GSWSelfKey.binaryEmbed bits) (original index)
      (GSWGadget.bitMessage (bits index)) (keyBound parameter))
    (hfirst : RecursiveFeatureGSW.NoiseBound (params parameter (capacity_of_budget parameter hbudget))
      (GSWSelfKey.binaryEmbed bits) first (GSWGadget.bitMessage firstBit) (outputBound parameter))
    (hsecond : RecursiveFeatureGSW.NoiseBound (params parameter (capacity_of_budget parameter hbudget))
      (GSWSelfKey.binaryEmbed bits) second (GSWGadget.bitMessage secondBit) (outputBound parameter)) :
    RecursiveFeatureGSW.decode (params parameter (capacity_of_budget parameter hbudget)) (GSWSelfKey.binaryEmbed bits)
      (RecursiveFeatureBootstrap.refreshedNand (params parameter (capacity_of_budget parameter hbudget))
        original first second (level parameter (capacity_of_budget parameter hbudget)) (oneCode parameter))
      (level parameter (capacity_of_budget parameter hbudget)) = !(firstBit && secondBit) := by
  apply RecursiveFeatureGSW.decode_eq_bit _ _ _ _ (outputBound parameter)
    (level parameter (capacity_of_budget parameter hbudget))
    (noiseBound_refreshedNand parameter hbudget bits original first second firstBit secondBit hcontrols hfirst hsecond)
  rw [gadget_distance]
  exact output_margin parameter hbudget

/-- The parameter margins are discharged, rather than assumed in every gate theorem. -/
theorem eventually_refreshedNand_correct :
    ∀ᶠ parameter in Filter.atTop, ∃ hcapacity : lookupExponent parameter ≤ scale parameter ^ 2,
      ∀ bits : Fin (dimension parameter) → Bool,
      ∀ original : Fin (dimension parameter) → RecursiveFeatureGSW.Batch (params parameter hcapacity) (dimension parameter),
      ∀ first second : RecursiveFeatureGSW.Batch (params parameter hcapacity) (dimension parameter),
      ∀ firstBit secondBit : Bool,
      (∀ index, RecursiveFeatureGSW.NoiseBound (params parameter hcapacity) (GSWSelfKey.binaryEmbed bits)
        (original index) (GSWGadget.bitMessage (bits index)) (keyBound parameter)) →
      RecursiveFeatureGSW.NoiseBound (params parameter hcapacity) (GSWSelfKey.binaryEmbed bits) first
        (GSWGadget.bitMessage firstBit) (outputBound parameter) →
      RecursiveFeatureGSW.NoiseBound (params parameter hcapacity) (GSWSelfKey.binaryEmbed bits) second
        (GSWGadget.bitMessage secondBit) (outputBound parameter) →
      RecursiveFeatureGSW.decode (params parameter hcapacity) (GSWSelfKey.binaryEmbed bits)
        (RecursiveFeatureBootstrap.refreshedNand (params parameter hcapacity) original first second
          (level parameter hcapacity) (oneCode parameter)) (level parameter hcapacity) = !(firstBit && secondBit) := by
  filter_upwards [eventually_budget] with parameter hbudget
  refine ⟨capacity_of_budget parameter hbudget, ?_⟩
  intro bits original first second firstBit secondBit hcontrols hfirst hsecond
  exact decode_refreshedNand parameter hbudget bits original first second firstBit secondBit hcontrols hfirst hsecond

end FormalProof4FHE.LWE.RecursiveFeatureBootstrapParameters
