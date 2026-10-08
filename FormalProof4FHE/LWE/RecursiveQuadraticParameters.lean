/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveQuadratic
import FormalProof4FHE.Probability.WeightedBitSampler

/-!
# Parameters for the ordinary-LWE recursive quadratic component

At scale t=lambda+1, use ordinary source dimension t^3, binary dimension
2*t^5, coefficient modulus 2^(t^2), wide interval radius 2^t, and t^2
flooding retries. Narrow errors are compiled finite Gaussian errors of width
t^2, with squared precision and retry count t^4. This module discharges
statistical loss and fresh decryption-margin estimates for that component.
It does not construct a ciphertext-format conversion or reusable bootstrap.
LWE hardness at this parameter family is still a computational assumption;
no worst-case lattice hardness or complete arithmetic cost claim is made.
-/

open OracleComp
open scoped BigOperators ENNReal Topology

namespace FormalProof4FHE.LWE.RecursiveQuadraticParameters

def scale (parameter : ℕ) : ℕ := parameter + 1
def sourceDimension (parameter : ℕ) : ℕ := scale parameter ^ 3
def binaryDimension (parameter : ℕ) : ℕ := 2 * scale parameter ^ 5
@[irreducible] def modulus (parameter : ℕ) : ℕ := 2 ^ (scale parameter ^ 2)
def radius (parameter : ℕ) : ℕ := 2 ^ scale parameter
def retries (parameter : ℕ) : ℕ := scale parameter ^ 2
def narrowWidth (parameter : ℕ) : ℕ := scale parameter ^ 2
def narrowPrecision (parameter : ℕ) : ℕ := scale parameter ^ 4

instance (parameter : ℕ) : NeZero (modulus parameter) := ⟨by
  unfold modulus
  positivity⟩

theorem scale_pos (parameter : ℕ) : 0 < scale parameter := by unfold scale; omega

theorem parameter_le_retries (parameter : ℕ) : parameter ≤ retries parameter := by
  unfold retries scale
  nlinarith

theorem parameter_le_precision (parameter : ℕ) : parameter ≤ narrowPrecision parameter := by
  have h := parameter_le_retries parameter
  have hs : 1 ≤ scale parameter ^ 2 := one_le_pow₀ (by have := scale_pos parameter; omega)
  have hpow : scale parameter ^ 2 ≤ (scale parameter ^ 2) ^ 2 := by nlinarith
  simpa only [narrowPrecision, retries, ← pow_mul] using h.trans hpow

/-- The exponential coefficient modulus has polynomial word length. -/
theorem modulus_ticketWidth_le (parameter : ℕ) :
    BoundedUniform.ticketWidth (modulus parameter) ≤ scale parameter ^ 2 + 1 := by
  apply BoundedUniform.ticketWidth_le (NeZero.pos (modulus parameter))
  have hcap : 2 ^ (scale parameter ^ 2 + 1) = 2 * modulus parameter := by
    unfold modulus
    rw [pow_succ]
    ring
  rw [hcap]
  have hpositive := NeZero.pos (modulus parameter)
  omega

theorem entropy_cardinality_margin (parameter : ℕ) :
    modulus parameter ^ sourceDimension parameter * 2 ^ (2 * parameter) ≤
      2 ^ binaryDimension parameter := by
  have he : (scale parameter ^ 2) * (scale parameter ^ 3) = scale parameter ^ 5 := by ring
  have hsmall : 2 * parameter ≤ scale parameter ^ 5 := by
    have hs : 1 ≤ scale parameter := by have := scale_pos parameter; omega
    have hp : scale parameter ^ 2 ≤ scale parameter ^ 5 := pow_le_pow_right' hs (by decide)
    unfold scale at hp ⊢
    nlinarith
  unfold modulus sourceDimension binaryDimension
  rw [← pow_mul, he, ← pow_add]
  apply pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ))
  omega

noncomputable def entropyBound (parameter : ℕ) : ℝ :=
  Real.sqrt (((modulus parameter : ℝ) ^ sourceDimension parameter - 1) /
    (2 : ℝ) ^ binaryDimension parameter) / 2

theorem entropyBound_le_half_pow (parameter : ℕ) :
    entropyBound parameter ≤ (1 / 2 : ℝ) ^ parameter := by
  have hmargin : (modulus parameter : ℝ) ^ sourceDimension parameter *
      (2 : ℝ) ^ (2 * parameter) ≤ (2 : ℝ) ^ binaryDimension parameter := by
    exact_mod_cast entropy_cardinality_margin parameter
  have hsqrt : Real.sqrt ((modulus parameter : ℝ) ^ sourceDimension parameter /
      (2 : ℝ) ^ binaryDimension parameter) ≤ (1 / 2 : ℝ) ^ parameter := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ 1 / (2 : ℝ) ^ (2 * parameter) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        simpa only [one_mul] using hmargin
      _ = _ := by rw [div_pow, one_pow, div_pow, one_pow, ← pow_mul, Nat.mul_comm parameter 2]
  have hmono : Real.sqrt (((modulus parameter : ℝ) ^ sourceDimension parameter - 1) /
      (2 : ℝ) ^ binaryDimension parameter) ≤
      Real.sqrt ((modulus parameter : ℝ) ^ sourceDimension parameter /
        (2 : ℝ) ^ binaryDimension parameter) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  unfold entropyBound
  have hnonneg := Real.sqrt_nonneg
    (((modulus parameter : ℝ) ^ sourceDimension parameter - 1) /
      (2 : ℝ) ^ binaryDimension parameter)
  linarith

theorem inverse_interval_le_half_pow (parameter : ℕ) :
    1 / (2 * radius parameter + 1 : ℝ) ≤ (1 / 2 : ℝ) ^ parameter := by
  have hnat : 2 ^ parameter ≤ 2 * radius parameter + 1 := by
    unfold radius scale
    rw [pow_succ]
    have hp : 0 < (2 : ℕ) ^ parameter := by positivity
    omega
  have hreal : (2 : ℝ) ^ parameter ≤ (2 * radius parameter + 1 : ℝ) := by
    exact_mod_cast hnat
  rw [div_pow, one_pow]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hreal

theorem retry_error_le_half_pow (parameter : ℕ) :
    (1 / 2 : ℝ) ^ retries parameter ≤ (1 / 2 : ℝ) ^ parameter :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) (parameter_le_retries parameter)

def narrow (parameter : ℕ) : ProbComp (ZMod (modulus parameter)) :=
  (GaussianIntegerWeights.modularTable (modulus parameter) (narrowWidth parameter)
    (narrowPrecision parameter)).bitSampler (narrowPrecision parameter)

theorem scalarFirstMoment_le_of_support_bound (q bound : ℕ) [NeZero q]
    (sampler : ProbComp (ZMod q))
    (hbound : ∀ error, error ∈ support sampler →
      (LatticeCrypto.centeredRepr error).natAbs ≤ bound) :
    FormalProof4FHE.BlockBinary.scalarFirstMoment sampler
      (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ)) ≤ (bound : ℝ) := by
  have hmass : (∑ error, Pr[= error | sampler].toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun _ _ ↦ probOutput_ne_top),
      sum_probOutput_eq_one (by simp), ENNReal.toReal_one]
  unfold FormalProof4FHE.BlockBinary.scalarFirstMoment
  calc
    _ ≤ ∑ error, Pr[= error | sampler].toReal * (bound : ℝ) := by
      apply Finset.sum_le_sum
      intro error _
      by_cases hs : error ∈ support sampler
      · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        dsimp only
        exact_mod_cast hbound error hs
      · rw [probOutput_eq_zero_of_not_mem_support hs]
        simp
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

theorem narrow_support_bound (parameter : ℕ) (error : ZMod (modulus parameter))
    (herror : error ∈ support (narrow parameter)) :
    (LatticeCrypto.centeredRepr error).natAbs ≤ narrowPrecision parameter := by
  have hevent := WeightedSampler.Table.probEvent_bitSampler_eq_one_of_entries
    (GaussianIntegerWeights.modularTable (modulus parameter) (narrowWidth parameter)
      (narrowPrecision parameter)) (narrowPrecision parameter)
    (fun error ↦ (LatticeCrypto.centeredRepr error).natAbs ≤ narrowWidth parameter ^ 2)
    (fun entry hentry ↦ GaussianIntegerWeights.modularTable_entries_bounded _ _ _ entry hentry)
  have hb := (probEvent_eq_one_iff.mp hevent).2 error herror
  simpa only [narrowWidth, narrowPrecision, ← pow_mul] using hb

theorem narrow_firstMoment_le (parameter : ℕ) :
    FormalProof4FHE.BlockBinary.scalarFirstMoment (narrow parameter)
      (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ)) ≤
        (scale parameter ^ 4 : ℝ) := by
  simpa only [narrowPrecision, Nat.cast_pow] using
    scalarFirstMoment_le_of_support_bound (modulus parameter) (narrowPrecision parameter)
      (narrow parameter) (narrow_support_bound parameter)

theorem coinBound_narrow (parameter : ℕ) :
    BoundedUniform.CoinBound (narrow parameter)
      (scale parameter ^ 4 * (3 * scale parameter ^ 4 + 1)) := by
  have hw : BoundedUniform.ticketWidth
      (GaussianIntegerWeights.modularTable (modulus parameter) (narrowWidth parameter)
        (narrowPrecision parameter)).ticketCount ≤ 3 * scale parameter ^ 4 + 1 := by
    apply BoundedUniform.ticketWidth_le
      (GaussianIntegerWeights.modularTable _ _ _).total_pos
    have h := GaussianIntegerWeights.modularTable_ticketCount_lt
      (modulus parameter) (narrowWidth parameter) (narrowPrecision parameter)
    have he : narrowPrecision parameter + 2 * narrowWidth parameter ^ 2 + 1 =
        3 * scale parameter ^ 4 + 1 := by unfold narrowWidth narrowPrecision; ring
    rw [he] at h
    exact h
  exact (WeightedSampler.Table.coinBound_bitSampler _ _).mono
    (Nat.mul_le_mul_left (scale parameter ^ 4) hw)

theorem coinBound_wide (parameter : ℕ) :
    BoundedUniform.CoinBound
      (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))
      (scale parameter ^ 2 * (parameter + 3)) := by
  simpa only [radius, retries, scale, Nat.add_assoc] using
    UniformInterval.coinBound_exponential_sample (modulus parameter) (scale parameter)
      (retries parameter)

theorem narrowWidth_pos (parameter : ℕ) : 0 < narrowWidth parameter := by
  unfold narrowWidth
  exact pow_pos (scale_pos parameter) _

theorem gaussian_weightError_le (parameter : ℕ) :
    GaussianSamplerTV.weightError (narrowWidth parameter) (narrowPrecision parameter) ≤
      ((scale parameter ^ 4 + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ parameter := by
  have heq : GaussianSamplerTV.weightError (narrowWidth parameter) (narrowPrecision parameter) =
      ((scale parameter ^ 4 + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ narrowPrecision parameter := by
    unfold GaussianSamplerTV.weightError GaussianIntegerWeights.expansionPower narrowWidth
    rw [div_pow, one_pow]
    push_cast
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (parameter_le_precision parameter))
    (Nat.cast_nonneg _)

theorem gaussian_tail_le_half_pow (parameter : ℕ) :
    Real.exp (-(narrowWidth parameter : ℝ) ^ 2 / 2) ≤ (1 / 2 : ℝ) ^ parameter := by
  have hw : scale parameter ≤ narrowWidth parameter := by
    have hs := scale_pos parameter
    unfold narrowWidth
    nlinarith
  have hcast : (scale parameter : ℝ) ≤ (narrowWidth parameter : ℝ) := Nat.cast_le.mpr hw
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (scale parameter)) hcast 2
  calc
    _ ≤ Real.exp (-(scale parameter : ℝ) ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ _ := DiscreteGaussianTail.exp_square_succ_le_half_pow parameter

theorem gaussian_approximationBound_le (parameter : ℕ) :
    GaussianSamplerTV.approximationBound (narrowWidth parameter) (narrowPrecision parameter) ≤
      (((2 * scale parameter ^ 4 + 1) * (scale parameter ^ 4 + 2) + 4 : ℕ) : ℝ) *
        (1 / 2 : ℝ) ^ parameter := by
  unfold GaussianSamplerTV.approximationBound
  calc
    _ ≤ ((2 * narrowWidth parameter ^ 2 + 1 : ℕ) : ℝ) *
        (((scale parameter ^ 4 + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ parameter) +
        4 * (1 / 2 : ℝ) ^ parameter :=
      add_le_add
        (mul_le_mul_of_nonneg_left (gaussian_weightError_le parameter) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (gaussian_tail_le_half_pow parameter) (by norm_num))
    _ = _ := by unfold narrowWidth; push_cast; ring

noncomputable def gaussianComparisonBound (parameter : ℕ) : ℝ :=
  (((2 * scale parameter ^ 4 + 1) * (scale parameter ^ 4 + 2) + 5 : ℕ) : ℝ) *
    (1 / 2 : ℝ) ^ parameter

theorem narrow_reference_etvDist_le (parameter : ℕ) :
    (liftM (narrow parameter) : PMF (ZMod (modulus parameter))).etvDist
      (ModularGaussian.distribution (modulus parameter) (narrowWidth parameter)
        (Nat.cast_pos.mpr (narrowWidth_pos parameter))) ≤
          ENNReal.ofReal (gaussianComparisonBound parameter) := by
  have hr : (1 / 2 : ℝ) ^ narrowPrecision parameter ≤ (1 / 2 : ℝ) ^ parameter :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (parameter_le_precision parameter)
  calc
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ narrowPrecision parameter) +
        ENNReal.ofReal
          (GaussianSamplerTV.approximationBound (narrowWidth parameter) (narrowPrecision parameter)) :=
      WeightedBitSampler.modular_etvDist_le _ _ _ _ (narrowWidth_pos parameter)
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ parameter) +
        ENNReal.ofReal
          ((((2 * scale parameter ^ 4 + 1) * (scale parameter ^ 4 + 2) + 4 : ℕ) : ℝ) *
            (1 / 2 : ℝ) ^ parameter) :=
      add_le_add (ENNReal.ofReal_le_ofReal hr)
        (ENNReal.ofReal_le_ofReal (gaussian_approximationBound_le parameter))
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      unfold gaussianComparisonBound
      push_cast
      ring

theorem gaussianComparisonBound_negligible :
    negligible (fun parameter ↦ ENNReal.ofReal (gaussianComparisonBound parameter)) := by
  apply negligible_of_le (g := fun parameter ↦
    (((2 * scale parameter ^ 4 + 1) * (scale parameter ^ 4 + 2) + 5 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal ((1 / 2 : ℝ) ^ parameter))
  · intro parameter
    unfold gaussianComparisonBound
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · have h := negligible_polynomial_mul DiscreteGaussianTail.half_pow_negligible
      (((2 * (Polynomial.X + 1) ^ 4 + 1) * ((Polynomial.X + 1) ^ 4 + 2) + 5) : Polynomial ℕ)
    simpa [scale] using h

theorem narrow_reference_negligible :
    negligible (fun parameter ↦
      (liftM (narrow parameter) : PMF (ZMod (modulus parameter))).etvDist
        (ModularGaussian.distribution (modulus parameter) (narrowWidth parameter)
          (Nat.cast_pos.mpr (narrowWidth_pos parameter)))) :=
  negligible_of_le narrow_reference_etvDist_le gaussianComparisonBound_negligible

noncomputable def absorptionBound (samples parameter : ℕ) : ℝ :=
  min 1 (((samples : ℝ) * binaryDimension parameter / 2) *
    ((scale parameter ^ 4 : ℝ) / (2 * radius parameter + 1 : ℝ)))

noncomputable def floodingBound (samples parameter : ℕ) : ℝ :=
  (samples : ℝ) * ((scale parameter ^ 4 : ℝ) / (2 * radius parameter + 1 : ℝ) +
    (1 / 2 : ℝ) ^ retries parameter)

noncomputable def statisticalLoss (samples parameter : ℕ) : ℝ :=
  absorptionBound samples parameter + entropyBound parameter + floodingBound samples parameter

theorem moment_fraction_le (parameter : ℕ) :
    (scale parameter ^ 4 : ℝ) / (2 * radius parameter + 1 : ℝ) ≤
      (scale parameter ^ 4 : ℝ) * (1 / 2 : ℝ) ^ parameter := by
  simpa only [div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left (inverse_interval_le_half_pow parameter)
      (by positivity : 0 ≤ (scale parameter ^ 4 : ℝ))

theorem absorptionBound_le (samples parameter : ℕ) :
    absorptionBound samples parameter ≤
      (samples : ℝ) * (scale parameter ^ 9 : ℝ) * (1 / 2 : ℝ) ^ parameter := by
  unfold absorptionBound
  calc
    _ ≤ ((samples : ℝ) * binaryDimension parameter / 2) *
        ((scale parameter ^ 4 : ℝ) / (2 * radius parameter + 1 : ℝ)) := min_le_right _ _
    _ ≤ ((samples : ℝ) * binaryDimension parameter / 2) *
        ((scale parameter ^ 4 : ℝ) * (1 / 2 : ℝ) ^ parameter) :=
      mul_le_mul_of_nonneg_left (moment_fraction_le parameter) (by positivity)
    _ = _ := by simp only [binaryDimension, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]; ring

theorem floodingBound_le (samples parameter : ℕ) :
    floodingBound samples parameter ≤
      2 * (samples : ℝ) * (scale parameter ^ 4 : ℝ) * (1 / 2 : ℝ) ^ parameter := by
  have hscale : (1 : ℝ) ≤ scale parameter ^ 4 := by
    exact_mod_cast one_le_pow₀ (by have := scale_pos parameter; omega : 1 ≤ scale parameter)
  unfold floodingBound
  calc
    _ ≤ (samples : ℝ) *
        ((scale parameter ^ 4 : ℝ) * (1 / 2 : ℝ) ^ parameter + (1 / 2 : ℝ) ^ parameter) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (moment_fraction_le parameter) (retry_error_le_half_pow parameter))
        (Nat.cast_nonneg _)
    _ ≤ (samples : ℝ) *
        ((scale parameter ^ 4 : ℝ) * (1 / 2 : ℝ) ^ parameter +
          (scale parameter ^ 4 : ℝ) * (1 / 2 : ℝ) ^ parameter) := by
      gcongr
      exact le_mul_of_one_le_left (by positivity) hscale
    _ = _ := by ring

theorem statisticalLoss_le (samples parameter : ℕ) :
    statisticalLoss samples parameter ≤
      ((samples * (scale parameter ^ 9 + 2 * scale parameter ^ 4) + 1 : ℕ) : ℝ) *
        (1 / 2 : ℝ) ^ parameter := by
  have ha := absorptionBound_le samples parameter
  have he := entropyBound_le_half_pow parameter
  have hf := floodingBound_le samples parameter
  unfold statisticalLoss
  push_cast
  nlinarith

theorem statisticalLoss_negligible (rows : Polynomial ℕ) :
    negligible (fun parameter ↦ ENNReal.ofReal (statisticalLoss (rows.eval parameter) parameter)) := by
  apply negligible_of_le (g := fun parameter ↦
    ((rows.eval parameter * (scale parameter ^ 9 + 2 * scale parameter ^ 4) + 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal ((1 / 2 : ℝ) ^ parameter))
  · intro parameter
    have h := ENNReal.ofReal_le_ofReal (statisticalLoss_le (rows.eval parameter) parameter)
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using h
  · have h := negligible_polynomial_mul DiscreteGaussianTail.half_pow_negligible
      (rows * ((Polynomial.X + 1) ^ 9 + 2 * (Polynomial.X + 1) ^ 4) + 1)
    simpa [scale] using h

/-- The concrete statistical envelope bounds the previously proved complete-view reduction.
Every computational term has uniform-secret ordinary LWE with the compiled narrow law. -/
theorem advantage_le_narrowLWE {p k samples : ℕ} (parameter : ℕ)
    (columns : RecursiveQuadratic.Column (binaryDimension parameter * 1) p k ≃ Fin samples)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod (modulus parameter))
      (binaryDimension parameter * 1) k)
    (adversary : RecursiveQuadratic.View (ZMod (modulus parameter))
      (binaryDimension parameter * 1) p k → ProbComp Bool) :
    let wide := UniformInterval.draw (modulus parameter) (radius parameter)
    let downstream := RecursiveQuadratic.reduction columns polynomial adversary
    let maskReduction := FormalProof4FHE.BlockBinary.combinedMaskReduction 1
      (binaryDimension parameter) (sourceDimension parameter) samples (narrow parameter) wide downstream
    let extractedReduction := FormalProof4FHE.BlockBinary.extractedLWReduction 1
      (binaryDimension parameter) (sourceDimension parameter) samples (narrow parameter) wide downstream
    let sourceProblem := zmodBatchProblem (sourceDimension parameter) samples (modulus parameter)
      (narrow parameter)
    (RecursiveQuadratic.freshView columns polynomial
      ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (binaryDimension parameter))
      (FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter))) wide >>=
        adversary).boolDistAdvantage
      ((RecursiveQuadratic.idealView (R := ZMod (modulus parameter))
        (n := binaryDimension parameter * 1) (p := p) (k := k)) >>= adversary) ≤
      2 * (∑ coordinate : Fin (binaryDimension parameter * 1),
        LearningWithErrors.advantage sourceProblem
          (FormalProof4FHE.BlockBinary.rowHybridReduction (binaryDimension parameter * 1)
            (sourceDimension parameter) samples (narrow parameter) coordinate maskReduction)) +
      LearningWithErrors.advantage sourceProblem
        (NoiseFlooding.reduction
          (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))
          extractedReduction) + statisticalLoss samples parameter := by
  dsimp only
  have hbase := RecursiveQuadratic.interval_advantage_le_narrowLWE
    (modulus parameter) (radius parameter) (retries parameter) 1 (binaryDimension parameter)
    (sourceDimension parameter) columns polynomial (narrow parameter) (by simp) adversary
  simp only [Nat.cast_one, ZMod.card, mul_one (binaryDimension parameter : ℝ),
    show (1 : ℝ) + 1 = 2 from by norm_num] at hbase
  let moment := FormalProof4FHE.BlockBinary.scalarFirstMoment (narrow parameter)
    (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ))
  have hfrac : moment / (2 * radius parameter + 1 : ℝ) ≤
      (scale parameter ^ 4 : ℝ) / (2 * radius parameter + 1 : ℝ) :=
    div_le_div_of_nonneg_right (narrow_firstMoment_le parameter) (by positivity)
  have habs : min 1 (((samples : ℝ) * (binaryDimension parameter * 1 : ℕ) / 2) *
      (moment / (2 * radius parameter + 1 : ℝ))) ≤ absorptionBound samples parameter := by
    unfold absorptionBound
    simpa only [Nat.mul_one] using
      min_le_min_left 1 (mul_le_mul_of_nonneg_left hfrac
        (by positivity : 0 ≤ (samples : ℝ) * binaryDimension parameter / 2))
  have hflood : (samples : ℝ) * (moment / (2 * radius parameter + 1 : ℝ) +
      (1 / 2 : ℝ) ^ retries parameter) ≤ floodingBound samples parameter := by
    unfold floodingBound
    exact mul_le_mul_of_nonneg_left (add_le_add hfrac le_rfl) (Nat.cast_nonneg _)
  change _ ≤ _ + statisticalLoss samples parameter
  unfold statisticalLoss entropyBound
  dsimp only [moment] at habs hflood
  simp only [Nat.mul_one] at habs
  linarith

theorem radius_times_two_pow_le_modulus (parameter : ℕ) :
    2 ^ parameter * radius parameter ≤ modulus parameter := by
  unfold radius modulus
  rw [← pow_add]
  apply pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ))
  unfold scale
  nlinarith

/-- Replacing scalar errors retains the entire same-key public-key and message view. -/
theorem freshView_error_tvDist_le {Secret : Type} {q n p k samples : ℕ} [NeZero q]
    (columns : RecursiveQuadratic.Column n p k ≃ Fin samples)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) n k)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin n → ZMod q)
    (left right : ProbComp (ZMod q)) :
    tvDist (RecursiveQuadratic.freshView columns polynomial secretSampler embed left)
      (RecursiveQuadratic.freshView columns polynomial secretSampler embed right) ≤
        (samples : ℝ) * tvDist left right := by
  have hiid : tvDist (ProbComp.sampleIID samples left) (ProbComp.sampleIID samples right) ≤
      (samples : ℝ) * tvDist left right := by
    simpa [ProbComp.sampleIID] using
      FiniteProduct.tvDist_fin_mOfFn_le_sum samples (fun _ ↦ left) (fun _ ↦ right)
  letI : SampleableType (RecursiveQuadratic.Column n p k → ZMod q) := instSampleableTypePiFintype
  letI : SampleableType (Matrix (Fin n) (RecursiveQuadratic.Column n p k) (ZMod q)) :=
    instSampleableTypeFinFunc
  let challenges : ProbComp (Matrix (Fin n) (RecursiveQuadratic.Column n p k) (ZMod q)) := $ᵗ _
  let finish : Secret → Matrix (Fin n) (RecursiveQuadratic.Column n p k) (ZMod q) →
      (Fin samples → ZMod q) → ProbComp (RecursiveQuadratic.View (ZMod q) n p k) :=
    fun secret challenge errors ↦ pure (RecursiveQuadratic.fresh polynomial (embed secret) challenge
      (fun column ↦ errors (columns column)))
  have herrors (secret : Secret)
      (challenge : Matrix (Fin n) (RecursiveQuadratic.Column n p k) (ZMod q)) :
      tvDist (ProbComp.sampleIID samples left >>= finish secret challenge)
        (ProbComp.sampleIID samples right >>= finish secret challenge) ≤
          (samples : ℝ) * tvDist left right :=
    (tvDist_bind_right_le (finish secret challenge) _ _).trans hiid
  have hchallenges (secret : Secret) := tvDist_bind_left_le_const' (m := ProbComp) challenges
    (fun challenge ↦ ProbComp.sampleIID samples left >>= finish secret challenge)
    (fun challenge ↦ ProbComp.sampleIID samples right >>= finish secret challenge)
    ((samples : ℝ) * tvDist left right) (herrors secret)
  have hsecrets := tvDist_bind_left_le_const' (m := ProbComp) secretSampler
    (fun secret ↦ challenges >>= fun challenge ↦ ProbComp.sampleIID samples left >>= finish secret challenge)
    (fun secret ↦ challenges >>= fun challenge ↦ ProbComp.sampleIID samples right >>= finish secret challenge)
    ((samples : ℝ) * tvDist left right) hchallenges
  simpa only [RecursiveQuadratic.freshView, challenges, finish] using hsecrets

theorem sampled_view_tvDist_le {Secret : Type} {p k samples : ℕ} (parameter : ℕ)
    (columns : RecursiveQuadratic.Column (binaryDimension parameter * 1) p k ≃ Fin samples)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod (modulus parameter))
      (binaryDimension parameter * 1) k)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin (binaryDimension parameter * 1) → ZMod (modulus parameter)) :
    tvDist (RecursiveQuadratic.freshView columns polynomial secretSampler embed
      (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)))
      (RecursiveQuadratic.freshView columns polynomial secretSampler embed
        (UniformInterval.draw (modulus parameter) (radius parameter))) ≤
          (samples : ℝ) * (1 / 2 : ℝ) ^ retries parameter :=
  (freshView_error_tvDist_le columns polynomial secretSampler embed _ _).trans
    (mul_le_mul_of_nonneg_left (UniformInterval.sample_tvDist_le _ _ _) (Nat.cast_nonneg _))

noncomputable def implementationLoss (samples parameter : ℕ) : ℝ :=
  statisticalLoss samples parameter + (samples : ℝ) * (1 / 2 : ℝ) ^ retries parameter

theorem implementationLoss_le (samples parameter : ℕ) :
    implementationLoss samples parameter ≤
      ((samples * (scale parameter ^ 9 + 2 * scale parameter ^ 4 + 1) + 1 : ℕ) : ℝ) *
        (1 / 2 : ℝ) ^ parameter := by
  have hs := statisticalLoss_le samples parameter
  have hr := mul_le_mul_of_nonneg_left (retry_error_le_half_pow parameter) (Nat.cast_nonneg samples)
  unfold implementationLoss
  push_cast at hs ⊢
  nlinarith

theorem implementationLoss_negligible (rows : Polynomial ℕ) :
    negligible (fun parameter ↦ ENNReal.ofReal (implementationLoss (rows.eval parameter) parameter)) := by
  apply negligible_of_le (g := fun parameter ↦
    ((rows.eval parameter * (scale parameter ^ 9 + 2 * scale parameter ^ 4 + 1) + 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal ((1 / 2 : ℝ) ^ parameter))
  · intro parameter
    have h := ENNReal.ofReal_le_ofReal (implementationLoss_le (rows.eval parameter) parameter)
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using h
  · have h := negligible_polynomial_mul DiscreteGaussianTail.half_pow_negligible
      (rows * ((Polynomial.X + 1) ^ 9 + 2 * (Polynomial.X + 1) ^ 4 + 1) + 1)
    simpa [scale] using h

/-- The two kinds of explicit ordinary-LWE reductions in the concrete component bound. -/
noncomputable def ordinaryReductionLoss {p k samples : ℕ} (parameter : ℕ)
    (columns : RecursiveQuadratic.Column (binaryDimension parameter * 1) p k ≃ Fin samples)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod (modulus parameter))
      (binaryDimension parameter * 1) k)
    (adversary : RecursiveQuadratic.View (ZMod (modulus parameter))
      (binaryDimension parameter * 1) p k → ProbComp Bool) : ℝ :=
  let wide := UniformInterval.draw (modulus parameter) (radius parameter)
  let downstream := RecursiveQuadratic.reduction columns polynomial adversary
  let maskReduction := FormalProof4FHE.BlockBinary.combinedMaskReduction 1
    (binaryDimension parameter) (sourceDimension parameter) samples (narrow parameter) wide downstream
  let extractedReduction := FormalProof4FHE.BlockBinary.extractedLWReduction 1
    (binaryDimension parameter) (sourceDimension parameter) samples (narrow parameter) wide downstream
  let sourceProblem := zmodBatchProblem (sourceDimension parameter) samples (modulus parameter)
    (narrow parameter)
  2 * (∑ coordinate : Fin (binaryDimension parameter * 1),
    LearningWithErrors.advantage sourceProblem
      (FormalProof4FHE.BlockBinary.rowHybridReduction (binaryDimension parameter * 1)
        (sourceDimension parameter) samples (narrow parameter) coordinate maskReduction)) +
    LearningWithErrors.advantage sourceProblem
      (NoiseFlooding.reduction
        (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))
        extractedReduction)

/-- Honest key generation also uses finite-budget wide errors. Its full view has
the ordinary-LWE bound plus a negligible implementation loss at polynomial row counts. -/
theorem sampled_advantage_le_narrowLWE {p k samples : ℕ} (parameter : ℕ)
    (columns : RecursiveQuadratic.Column (binaryDimension parameter * 1) p k ≃ Fin samples)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod (modulus parameter))
      (binaryDimension parameter * 1) k)
    (adversary : RecursiveQuadratic.View (ZMod (modulus parameter))
      (binaryDimension parameter * 1) p k → ProbComp Bool) :
    (RecursiveQuadratic.freshView columns polynomial
      ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (binaryDimension parameter))
      (FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)))
      (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)) >>=
        adversary).boolDistAdvantage
      ((RecursiveQuadratic.idealView (R := ZMod (modulus parameter))
        (n := binaryDimension parameter * 1) (p := p) (k := k)) >>= adversary) ≤
          ordinaryReductionLoss parameter columns polynomial adversary +
            implementationLoss samples parameter := by
  let reference := RecursiveQuadratic.freshView columns polynomial
    ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (binaryDimension parameter))
    (FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)))
    (UniformInterval.draw (modulus parameter) (radius parameter))
  let actual := RecursiveQuadratic.freshView columns polynomial
    ($ᵗ FormalProof4FHE.BlockBinary.Key 1 (binaryDimension parameter))
    (FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)))
    (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))
  have hcompare : (actual >>= adversary).boolDistAdvantage (reference >>= adversary) ≤
      (samples : ℝ) * (1 / 2 : ℝ) ^ retries parameter :=
    (abs_probOutput_toReal_sub_le_tvDist _ _).trans
      ((tvDist_bind_right_le adversary actual reference).trans
        (sampled_view_tvDist_le parameter columns polynomial _ _))
  have hbase : (reference >>= adversary).boolDistAdvantage
      ((RecursiveQuadratic.idealView (R := ZMod (modulus parameter))
        (n := binaryDimension parameter * 1) (p := p) (k := k)) >>= adversary) ≤
        ordinaryReductionLoss parameter columns polynomial adversary + statisticalLoss samples parameter := by
    simpa only [reference, ordinaryReductionLoss] using
      advantage_le_narrowLWE parameter columns polynomial adversary
  have htriangle := ProbComp.boolDistAdvantage_triangle (actual >>= adversary)
    (reference >>= adversary)
    ((RecursiveQuadratic.idealView (R := ZMod (modulus parameter))
      (n := binaryDimension parameter * 1) (p := p) (k := k)) >>= adversary)
  have h := htriangle.trans (add_le_add hcompare hbase)
  unfold implementationLoss
  linarith

/-- Eventually every fresh binary recursive phase has a strict quarter-modulus error margin. -/
theorem eventually_fresh_quarter_margin :
    ∀ᶠ parameter in Filter.atTop,
      4 * (binaryDimension parameter + 1) * radius parameter < modulus parameter := by
  let polynomial : Polynomial ℕ := 4 * (2 * (Polynomial.X + 1) ^ 5 + 1)
  have hn := negligible_polynomial_mul DiscreteGaussianTail.half_pow_negligible polynomial
  have hz : Filter.Tendsto
      (fun parameter ↦ ((polynomial.eval parameter : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((1 / 2 : ℝ) ^ parameter)) Filter.atTop (nhds 0) := by
    simpa only [pow_zero, one_mul] using hn 0
  have hevent := hz.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  filter_upwards [hevent] with parameter hparameter
  have hr : ((4 * (binaryDimension parameter + 1) : ℕ) : ℝ) *
      (1 / 2 : ℝ) ^ parameter < 1 := by
    have hc : ENNReal.ofReal (((4 * (binaryDimension parameter + 1) : ℕ) : ℝ) *
        (1 / 2 : ℝ) ^ parameter) < ENNReal.ofReal 1 := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_one]
      simpa [polynomial, binaryDimension, scale] using hparameter
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mp hc
  rw [div_pow, one_pow, mul_one_div] at hr
  have hreal := (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ parameter)).mp hr
  have hnat : 4 * (binaryDimension parameter + 1) < 2 ^ parameter := by
    have ht : ((4 * (binaryDimension parameter + 1) : ℕ) : ℝ) < ((2 ^ parameter : ℕ) : ℝ) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, one_mul] using hreal
    exact_mod_cast ht
  exact (Nat.mul_lt_mul_of_pos_right hnat (by unfold radius; positivity)).trans_le
    (radius_times_two_pow_le_modulus parameter)

/-- Actual finite-budget error outcomes satisfy the fresh recursive phase margin. -/
theorem fresh_phase_quarter {p k : ℕ} (parameter : ℕ)
    (hmargin : 4 * (binaryDimension parameter + 1) * radius parameter < modulus parameter)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod (modulus parameter))
      (binaryDimension parameter * 1) k)
    (key : FormalProof4FHE.BlockBinary.Key 1 (binaryDimension parameter))
    (challenge : Matrix (Fin (binaryDimension parameter * 1))
      (RecursiveQuadratic.Column (binaryDimension parameter * 1) p k) (ZMod (modulus parameter)))
    (errors : RecursiveQuadratic.Column (binaryDimension parameter * 1) p k → ZMod (modulus parameter))
    (herrors : ∀ column, errors column ∈ support
      (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter)))
    (index : Fin k) :
    4 * (LatticeCrypto.centeredRepr
      (RecursiveQuadratic.decrypt (FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)) key)
        ((RecursiveQuadratic.fresh polynomial
          (FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)) key) challenge errors).2 index) -
        RecursiveQuadratic.message polynomial
          (FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)) key) index)).natAbs <
            modulus parameter := by
  have hsecret : ∀ coordinate,
      FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)) key coordinate = 0 ∨
      FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)) key coordinate = 1 := by
    intro coordinate
    unfold FormalProof4FHE.BlockBinary.expand
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hbound := RecursiveQuadratic.decrypt_fresh_binary_error_bound polynomial
    (FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)) key)
    challenge errors (radius parameter) hsecret
    (fun column ↦ UniformInterval.sample_support_centered_bound _ _ _ _ (herrors column)) index
  exact (Nat.mul_le_mul_left 4 hbound).trans_lt (by
    simpa only [Nat.mul_one, Nat.mul_assoc] using hmargin)

theorem eventually_fresh_phase_quarter :
    ∀ᶠ parameter in Filter.atTop, ∀ p k : ℕ,
      ∀ polynomial : RecursiveQuadratic.Polynomial (ZMod (modulus parameter))
        (binaryDimension parameter * 1) k,
      ∀ key : FormalProof4FHE.BlockBinary.Key 1 (binaryDimension parameter),
      ∀ challenge : Matrix (Fin (binaryDimension parameter * 1))
        (RecursiveQuadratic.Column (binaryDimension parameter * 1) p k) (ZMod (modulus parameter)),
      ∀ errors : RecursiveQuadratic.Column (binaryDimension parameter * 1) p k → ZMod (modulus parameter),
      (∀ column, errors column ∈ support
        (UniformInterval.sample (modulus parameter) (radius parameter) (retries parameter))) →
      ∀ index : Fin k,
        4 * (LatticeCrypto.centeredRepr
          (RecursiveQuadratic.decrypt (FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)) key)
            ((RecursiveQuadratic.fresh polynomial
              (FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)) key) challenge errors).2 index) -
            RecursiveQuadratic.message polynomial
              (FormalProof4FHE.BlockBinary.expand (ZMod (modulus parameter)) key) index)).natAbs <
                modulus parameter := by
  filter_upwards [eventually_fresh_quarter_margin] with parameter hmargin
  intro p k polynomial key challenge errors herrors index
  exact fresh_phase_quarter parameter hmargin polynomial key challenge errors herrors index

end FormalProof4FHE.LWE.RecursiveQuadraticParameters
