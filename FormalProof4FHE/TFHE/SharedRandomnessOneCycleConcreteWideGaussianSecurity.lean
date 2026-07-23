/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FinitePMFCompilerApproximation
import FormalProof4FHE.TFHE.DiscreteGaussianGrowingNoiseAdaptivePublicCircular
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleAsymptoticCircularSmudging

/-!
# Concrete Security-Only One-Cycle TFHE with a Wide Gaussian BRK

This module instantiates the numerical hypotheses of the statistical one-cycle theorem.  It uses
the existing polynomial TFHE dimensions and exponential-bitlength gadget modulus, and takes the
ideal modular-Gaussian target to have integer standard deviation `q * 2^lambda`.  Hence every
centered modular shift of magnitude at most `q / 2` has inverse-exponentially small translation
cost.

The implementation used by the final theorems is the explicit finite table containing every
residue exactly once.  Its sampler is therefore exactly uniform, while its certificate proves
that this uniform law is close to the deliberately wide ideal Gaussian.  In particular, the
literal real-self-BRK versus zero-BRK KDM advantage is exactly zero for every continuation.  The
resulting reusable adaptive and public-evaluation security theorems have only the ordinary scalar
batch-LWE premise; no circular/KDM or zero-BRK premise remains.  A separately checked canonical
rounded Gaussian table is retained below as a comparison certificate.

This is deliberately a security-only family.  Uniform BRK error is incompatible with ordinary
TFHE refresh correctness, so this theorem does not establish the security of practical
narrow-noise TFHE and does not resolve that research-level circular-security problem.
-/

open ENNReal OracleComp OracleSpec

namespace FormalProof4FHE.TFHE.SharedRandomnessOneCycle.ConcreteWideGaussian

noncomputable section

open CenteredBinomial.GrowingNoiseEndToEnd
open DiscreteGaussianTarget.GrowingNoise
open Encryption.Adaptive.SharedRandomnessOneCycle.Asymptotic
open Encryption.Adaptive.SharedRandomnessOneCycle.Asymptotic.CircularSecurity

/-- The scalar TLWE key and independent suffix have the same polynomial dimension. -/
abbrev prefixDimension (securityParameter : ℕ) : ℕ := ringDegree securityParameter

abbrev suffixDimension (securityParameter : ℕ) : ℕ := ringDegree securityParameter

/-- Relative width chosen so the integer Gaussian standard deviation is `q * 2^lambda`. -/
def wideAlpha (securityParameter : ℕ) : ℝ :=
  ((2 ^ securityParameter : ℕ) : ℝ)

theorem wideAlpha_pos (securityParameter : ℕ) : 0 < wideAlpha securityParameter := by
  unfold wideAlpha
  positivity

/-- Natural window used by the universal modular-shift estimate. -/
def wideWindow (securityParameter : ℕ) : ℕ :=
  gaussianModulus securityParameter * 2 ^ securityParameter

/-- The selected window is exactly the integer standard deviation. -/
theorem wideWindow_eq_integerStddev (securityParameter : ℕ) :
    (wideWindow securityParameter : ℝ) =
      ModularGaussian.integerStddev
        (gaussianModulus securityParameter) (wideAlpha securityParameter) := by
  unfold wideWindow wideAlpha ModularGaussian.integerStddev
  push_cast
  ring

/-- Security parameters for the exact shared-randomness one-cycle layout.  Ring BRK errors are
supplied separately by the `RingErrorFamily`; KSK and input errors use the growing
centered-binomial scalar sampler. -/
noncomputable def parameters :
    Encryption.Adaptive.SharedRandomnessOneCycle.Asymptotic.Parameters Bool where
  q := gaussianModulus
  prefixDimension := prefixDimension
  suffixDimension := suffixDimension
  tgswLevels := gaussianLevels
  keySwitchLevels := gaussianLevels
  scalarErrorSampler := fun securityParameter ↦
    CenteredBinomial.scalarSampler
      (gaussianModulus securityParameter) (errorWidth securityParameter)
  tgswGadget := fun securityParameter ↦
    Gadget.Base.ringGadget
      (degree := prefixDimension securityParameter + suffixDimension securityParameter)
      (gaussianDecomposition securityParameter)
  keySwitchGadget := fun securityParameter ↦
    Gadget.Base.gadget (gaussianDecomposition securityParameter)
  encode := fun securityParameter ↦
    CenteredBinomialDivisibleRefresh.inputCode
      (gaussianModulus securityParameter) (rotationDegree securityParameter)

instance instParametersNeZero :
    ∀ securityParameter, NeZero (parameters.q securityParameter) := by
  intro securityParameter
  change NeZero (gaussianModulus securityParameter)
  infer_instance

/-! ## Canonical finite Gaussian certificates -/

/-- A denominator cancelling both `ZMod q` cardinality factors in the generic compiler bound. -/
def certificateDenominator (securityParameter : ℕ) : ℕ :=
  gaussianModulus securityParameter * (gaussianModulus securityParameter + 1) *
    2 ^ securityParameter

theorem certificateDenominator_pos (securityParameter : ℕ) :
    0 < certificateDenominator securityParameter := by
  unfold certificateDenominator
  exact Nat.mul_pos
    (Nat.mul_pos (gaussianModulus_pos securityParameter)
      (Nat.succ_pos (gaussianModulus securityParameter)))
    (Nat.pow_pos (by omega))

/-- Canonical finite approximation to the deliberately wide exact modular Gaussian. -/
noncomputable def canonicalCertificate (securityParameter : ℕ) :
    DiscreteGaussianSampler.ScalarCertificate
      (gaussianModulus securityParameter) (wideAlpha securityParameter)
      (wideAlpha_pos securityParameter) :=
  FinitePMFCompiler.TicketTable.roundedCertificate
    (ModularGaussian.torusDistribution
      (gaussianModulus securityParameter) (wideAlpha securityParameter)
      (wideAlpha_pos securityParameter)) 0
    (certificateDenominator securityParameter)
    (certificateDenominator_pos securityParameter)

/-- The canonical finite compilation error is at most `2^-lambda`. -/
theorem canonicalCertificate_bound_le (securityParameter : ℕ) :
    (canonicalCertificate securityParameter).bound ≤
      ((2 : ℝ≥0∞) ^ securityParameter)⁻¹ := by
  rw [canonicalCertificate,
    FinitePMFCompiler.TicketTable.roundedCertificate_bound]
  simp only [FinitePMFCompiler.TicketTable.roundedPointwiseBound, ZMod.card]
  have hdenominator :
      (certificateDenominator securityParameter : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (certificateDenominator_pos securityParameter)
  have hpointwiseFinite :
      ((gaussianModulus securityParameter + 1 : ℕ) /
          (certificateDenominator securityParameter : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hdenominator
  have hleftFinite :
      (gaussianModulus securityParameter : ℝ≥0∞) *
            ((gaussianModulus securityParameter + 1 : ℕ) /
              (certificateDenominator securityParameter : ℝ≥0∞)) /
          2 ≠ ⊤ :=
    ENNReal.div_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hpointwiseFinite) (by norm_num)
  have hrightFinite :
      ((2 : ℝ≥0∞) ^ securityParameter)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (pow_ne_zero _ (by norm_num))
  apply (ENNReal.toReal_le_toReal hleftFinite hrightFinite).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  unfold certificateDenominator
  push_cast
  have hmodulus : (gaussianModulus securityParameter : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (gaussianModulus_pos securityParameter)
  have hmodulusSucc : (gaussianModulus securityParameter : ℝ) + 1 ≠ 0 := by
    positivity
  have hpow : (2 : ℝ) ^ securityParameter ≠ 0 := by positivity
  field_simp
  nlinarith

theorem canonicalCertificate_bound_negligible :
    negligible (fun securityParameter ↦
      (canonicalCertificate securityParameter).bound) :=
  negligible_of_le canonicalCertificate_bound_le
    Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.negligible_inv_two_pow

/-! ### Explicit uniform-ticket implementation -/

/-- The finite table containing every residue once, certified against the same wide modular
Gaussian target.  Its actual sampler is exactly uniform; only the proof certificate uses the
ideal Gaussian law. -/
noncomputable def executableCertificate (securityParameter : ℕ) :
    DiscreteGaussianSampler.ScalarCertificate
      (gaussianModulus securityParameter) (wideAlpha securityParameter)
      (wideAlpha_pos securityParameter) :=
  DiscreteGaussianSampler.uniformResidueCertificate
    (gaussianModulus securityParameter) (wideAlpha securityParameter)
    (wideAlpha_pos securityParameter)

@[simp]
theorem executableCertificate_table (securityParameter : ℕ) :
    (executableCertificate securityParameter).table =
      DiscreteGaussianSampler.uniformResidueTable
        (gaussianModulus securityParameter) := rfl

/-- The executable uniform table's distance certificate against the ideal wide Gaussian is
bounded by the same modulus-scaled inverse-window envelope. -/
theorem executableCertificate_bound_le_windowEnvelope (securityParameter : ℕ) :
    (executableCertificate securityParameter).bound ≤
      ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
        ((gaussianModulus securityParameter / 2 : ℕ) : ℝ≥0∞) *
          ((wideWindow securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [executableCertificate,
    DiscreteGaussianSampler.uniformResidueCertificate_bound]
  calc
    ENNReal.ofReal
        (ModularGaussian.torusUniformBound
          (gaussianModulus securityParameter) (wideAlpha securityParameter)
          (wideAlpha_pos securityParameter)) ≤
      ENNReal.ofReal
        ((gaussianModulus securityParameter / 2 : ℕ) *
          (Real.exp (1 / 2 : ℝ) /
            (wideWindow securityParameter + 1 : ℕ))) := by
      apply ENNReal.ofReal_le_ofReal
      exact ModularGaussian.torusUniformBound_le_exp_half_window
        (gaussianModulus securityParameter) (wideAlpha securityParameter)
        (wideAlpha_pos securityParameter) (wideWindow securityParameter)
        (wideWindow_eq_integerStddev securityParameter).le
    _ = ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          ((gaussianModulus securityParameter / 2 : ℕ) : ℝ≥0∞) *
            ((wideWindow securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) <
          (wideWindow securityParameter + 1 : ℕ))]
      norm_cast
      rw [div_eq_mul_inv]
      ring

/-- The scalar implementation carried by `executableCertificate` is exactly uniform modulo the
concrete coefficient modulus. -/
theorem executableScalarSampler_evalDist_eq_uniform (securityParameter : ℕ) :
    evalDist
        (DiscreteGaussianSampler.scalarSampler
          (executableCertificate securityParameter)) =
      evalDist ($ᵗ (ZMod (gaussianModulus securityParameter))) := by
  simpa only [DiscreteGaussianSampler.scalarSampler, executableCertificate_table] using
    DiscreteGaussianSampler.uniformResidueTable_sampler_evalDist
      (gaussianModulus securityParameter)

/-- Package the concrete Gaussian width and canonical certificate for the generic theorem. -/
def discreteGaussianData : DiscreteGaussianRingErrorData parameters where
  alpha := wideAlpha
  alpha_pos := wideAlpha_pos
  certificate := executableCertificate

/-- The actual coefficientwise ring-error implementation is exactly uniform, not merely close
to uniform. -/
theorem executableRingError_evalDist_eq_uniform (securityParameter : ℕ) :
    evalDist
        ((discreteGaussianRingErrorFamily parameters discreteGaussianData).sampler
          securityParameter) =
      evalDist
        ($ᵗ (RLWE.Rq
          (parameters.q securityParameter)
          (parameters.prefixDimension securityParameter +
            parameters.suffixDimension securityParameter))) := by
  simp only [discreteGaussianRingErrorFamily, discreteGaussianData,
    executableCertificate, parameters]
  convert
    DiscreteGaussianSampler.ringSampler_uniformResidueCertificate_evalDist_eq_uniform
      (gaussianModulus securityParameter)
      (prefixDimension securityParameter + suffixDimension securityParameter)
      (wideAlpha securityParameter) (wideAlpha_pos securityParameter) using 1
  rfl

/-- Consequently, the one-draw implementation-to-uniform replacement gap is exactly zero. -/
theorem ringErrorGap_eq_zero (securityParameter : ℕ) :
    ringErrorGap parameters
        (discreteGaussianRingErrorFamily parameters discreteGaussianData)
        securityParameter = 0 := by
  unfold ringErrorGap
  rw [(tvDist_eq_zero_iff _ _).2 (executableRingError_evalDist_eq_uniform securityParameter)]
  simp

/-- The modulus-scaled inverse window is pointwise at most `2^-lambda`. -/
theorem scaledWindow_le_inv_two_pow (securityParameter : ℕ) :
    ((gaussianModulus securityParameter / 2 : ℕ) : ℝ≥0∞) *
        ((wideWindow securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤
      ((2 : ℝ≥0∞) ^ securityParameter)⁻¹ := by
  have hwindowCastZero :
      ((wideWindow securityParameter + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (wideWindow securityParameter)
  have hleftFinite :
      ((gaussianModulus securityParameter / 2 : ℕ) : ℝ≥0∞) *
          ((wideWindow securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.inv_ne_top.mpr hwindowCastZero)
  have hrightFinite :
      ((2 : ℝ≥0∞) ^ securityParameter)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (pow_ne_zero _ (by norm_num))
  apply (ENNReal.toReal_le_toReal hleftFinite hrightFinite).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  rw [← div_eq_mul_inv, ← one_div]
  have hdenominator :
      0 < ((wideWindow securityParameter + 1 : ℕ) : ℝ) := by positivity
  have hpow : 0 < (2 : ℝ) ^ securityParameter := by positivity
  rw [div_le_div_iff₀ hdenominator hpow]
  have hhalf : gaussianModulus securityParameter / 2 ≤
      gaussianModulus securityParameter := Nat.div_le_self _ _
  have hhalfReal :
      ((gaussianModulus securityParameter / 2 : ℕ) : ℝ) ≤
        gaussianModulus securityParameter := by
    exact_mod_cast hhalf
  unfold wideWindow
  push_cast
  nlinarith [hhalfReal]

theorem scaledWindow_negligible :
    negligible (fun securityParameter ↦
      ((gaussianModulus securityParameter / 2 : ℕ) : ℝ≥0∞) *
        ((wideWindow securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹) :=
  negligible_of_le scaledWindow_le_inv_two_pow
    Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.negligible_inv_two_pow

theorem executableCertificate_bound_negligible :
    negligible (fun securityParameter ↦
      (executableCertificate securityParameter).bound) := by
  apply negligible_of_le executableCertificate_bound_le_windowEnvelope
  have hexp : ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  simpa only [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using
    negligible_const_mul scaledWindow_negligible hexp

/-! ## Polynomial layout -/

/-- Every dimension multiplying the one-draw Gaussian error has a polynomial envelope. -/
def polynomialGrowth : PolynomialCircularSmudgingGrowth parameters where
  prefixDimensionPolynomial := 16 * (Polynomial.X + 1)
  tgswLevelsPolynomial := Polynomial.X + 1
  prefixDimension_le := by
    intro securityParameter
    simpa [parameters, prefixDimension, errorWidth] using
      ringDegree_le_sixteen_mul_errorWidth securityParameter
  tgswLevels_le := by
    intro securityParameter
    simp [parameters, gaussianLevels]
  ringDegreePolynomial := 2 * (16 * (Polynomial.X + 1))
  ringDegree_le := by
    intro securityParameter
    have hdegree := ringDegree_le_sixteen_mul_errorWidth securityParameter
    simp only [parameters, prefixDimension, suffixDimension, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one]
    simp only [errorWidth] at hdegree
    omega

/-! ## Concrete one-circular and FHE security -/

/-- The chosen finite window fits exactly inside the Gaussian integer standard deviation. -/
theorem wideWindow_fits (securityParameter : ℕ) :
    (wideWindow securityParameter : ℝ) ≤
      ModularGaussian.integerStddev
        (parameters.q securityParameter)
        (discreteGaussianData.alpha securityParameter) := by
  simpa [parameters, discreteGaussianData] using
    (wideWindow_eq_integerStddev securityParameter).le

/-- The universal cost of translating one scalar error by an arbitrary centered residue is
negligible for the concrete family. -/
theorem scalarLinearShiftBound_negligible :
    negligible (fun securityParameter ↦
      ENNReal.ofReal
        (DiscreteGaussianSampler.scalarLinearShiftBound
          (discreteGaussianData.certificate securityParameter)
          (parameters.q securityParameter / 2))) := by
  exact scalarLinearShiftBound_negligible_of_window
    parameters discreteGaussianData wideWindow wideWindow_fits
    executableCertificate_bound_negligible scaledWindow_negligible

/-- The complete loss for replacing the actual self-encrypting BRK by its zero-message version
is negligible, including every coefficient of every polynomially many BRK rows. -/
theorem circularSmudgingBound_negligible :
    negligible (fun securityParameter ↦
      ENNReal.ofReal
        (discreteGaussianCircularSmudgingBound
          parameters discreteGaussianData securityParameter)) :=
  discreteGaussianCircularSmudgingBound_negligible
    parameters discreteGaussianData polynomialGrowth scalarLinearShiftBound_negligible

/-- The executable ring Gaussian is negligibly close to exact uniform per BRK error draw. -/
theorem ringErrorGap_negligible :
    negligible
      (ringErrorGap parameters
        (discreteGaussianRingErrorFamily parameters discreteGaussianData)) :=
  ringErrorGap_discreteGaussian_negligible
    parameters discreteGaussianData polynomialGrowth scalarLinearShiftBound_negligible

/-- The literal real-self-BRK versus zero-BRK KDM advantage is pointwise zero for every
continuation.  The real shared-randomness suffix KSK remains present in both experiments. -/
theorem kdmSecurityGame_advantage_eq_zero
    (continuation : ContinuationFamily parameters) (securityParameter : ℕ) :
    (kdmSecurityGame parameters
      (discreteGaussianRingErrorFamily parameters discreteGaussianData)).advantage
        continuation securityParameter = 0 := by
  unfold kdmSecurityGame
  change ENNReal.ofReal
      (Native.SharedRandomnessOneCycle.AuxiliaryInput.kdmAdvantage
        ((discreteGaussianRingErrorFamily parameters discreteGaussianData).sampler
          securityParameter)
        (parameters.scalarErrorSampler securityParameter)
        (parameters.tgswGadget securityParameter)
        (parameters.keySwitchGadget securityParameter)
        (continuation securityParameter)) = 0
  rw [Native.SharedRandomnessOneCycle.AuxiliaryInput.kdmAdvantage_eq_secretContinuationAdvantage]
  have hadvantage :
      Native.SharedRandomnessOneCycle.secretContinuationAdvantage
        (parameters.q securityParameter)
        (parameters.prefixDimension securityParameter)
        (parameters.suffixDimension securityParameter)
        (parameters.tgswLevels securityParameter)
        (parameters.keySwitchLevels securityParameter)
        ((discreteGaussianRingErrorFamily parameters discreteGaussianData).sampler
          securityParameter)
        (parameters.scalarErrorSampler securityParameter)
        (parameters.tgswGadget securityParameter)
        (parameters.keySwitchGadget securityParameter)
        (continuation securityParameter) = 0 := by
    apply le_antisymm
    · have h :=
      Native.SharedRandomnessOneCycle.secretContinuationAdvantage_le_uniformRingError
        (parameters.q securityParameter)
        (parameters.prefixDimension securityParameter)
        (parameters.suffixDimension securityParameter)
        (parameters.tgswLevels securityParameter)
        (parameters.keySwitchLevels securityParameter)
        ((discreteGaussianRingErrorFamily parameters discreteGaussianData).sampler
          securityParameter)
        (parameters.scalarErrorSampler securityParameter)
        (parameters.tgswGadget securityParameter)
        (parameters.keySwitchGadget securityParameter)
        (continuation securityParameter)
      rw [(tvDist_eq_zero_iff _ _).2
        (executableRingError_evalDist_eq_uniform securityParameter)] at h
      simpa using h
    · unfold Native.SharedRandomnessOneCycle.secretContinuationAdvantage
      exact abs_nonneg _
  simp [hadvantage]

/-- Literal one-circular KDM security of the real self-BRK against every selected continuation
family, with pointwise zero advantage rather than merely an asymptotic smudging bound. -/
theorem kdmSecurityGame_secureAgainst
    (isPPT : ContinuationFamily parameters → Prop) :
    (kdmSecurityGame parameters
      (discreteGaussianRingErrorFamily parameters discreteGaussianData)).secureAgainst
        isPPT := by
  intro continuation _
  have hadvantage :
      (kdmSecurityGame parameters
        (discreteGaussianRingErrorFamily parameters discreteGaussianData)).advantage
          continuation = 0 := by
    funext securityParameter
    exact kdmSecurityGame_advantage_eq_zero continuation securityParameter
  rw [hadvantage]
  exact negligible_zero

/-- Adaptive restriction of the same pointwise-zero KDM statement. -/
theorem adaptiveKDMSecurityGame_advantage_eq_zero
    (adversary : PolynomialQueryAdversary parameters) (securityParameter : ℕ) :
    (adaptiveKDMSecurityGame parameters
      (discreteGaussianRingErrorFamily parameters discreteGaussianData)).advantage
        adversary securityParameter = 0 := by
  exact kdmSecurityGame_advantage_eq_zero
    (continuationReduction parameters adversary) securityParameter

/-- Adaptive one-circular KDM security for the same concrete cloud-key distribution. -/
theorem adaptiveKDMSecurityGame_secureAgainst
    (isPPT : PolynomialQueryAdversary parameters → Prop) :
    (adaptiveKDMSecurityGame parameters
      (discreteGaussianRingErrorFamily parameters discreteGaussianData)).secureAgainst
        isPPT := by
  intro adversary _
  have hadvantage :
      (adaptiveKDMSecurityGame parameters
        (discreteGaussianRingErrorFamily parameters discreteGaussianData)).advantage
          adversary = 0 := by
    funext securityParameter
    exact adaptiveKDMSecurityGame_advantage_eq_zero adversary securityParameter
  rw [hadvantage]
  exact negligible_zero

/-- **Concrete adaptive TFHE security without a circular-security premise.**

For this security-only wide-Gaussian family, ordinary query-counted scalar batch-LWE security is
the only cryptographic premise.  The real self-BRK circular term and the zero-BRK auxiliary term
are both removed statistically. -/
theorem secureAgainst_of_batchLWE
    (isPPT : PolynomialQueryAdversary parameters → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily parameters → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction parameters adversary))
    (hBatchLWE : (batchLWESecurityGame parameters).secureAgainst batchLWEIsPPT) :
    (implementationSecurityGame parameters
      (discreteGaussianRingErrorFamily parameters discreteGaussianData)).secureAgainst
        isPPT := by
  exact implementationSecureAgainst_of_discreteGaussianWindow_and_batchLWE
    parameters discreteGaussianData polynomialGrowth wideWindow
    isPPT batchLWEIsPPT hBatchLWEClosed wideWindow_fits
    executableCertificate_bound_negligible scaledWindow_negligible hBatchLWE

/-- Arbitrary public deterministic FHE evaluation preserves the concrete security theorem and
introduces no additional circular-security assumption. -/
theorem evaluationSecureAgainst_of_batchLWE
    {Output : Type}
    (evaluate : PublicEvaluatorFamily (Output := Output) parameters)
    (baseIsPPT : PolynomialQueryAdversary parameters → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) parameters → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily parameters → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary parameters evaluate adversary))
    (hBatchLWEClosed : ∀ adversary, baseIsPPT adversary →
      batchLWEIsPPT (batchLWEReduction parameters adversary))
    (hBatchLWE : (batchLWESecurityGame parameters).secureAgainst batchLWEIsPPT) :
    (implementationEvaluationSecurityGame parameters
      (discreteGaussianRingErrorFamily parameters discreteGaussianData) evaluate).secureAgainst
        evaluationIsPPT := by
  exact implementationEvaluationSecureAgainst_of_discreteGaussianWindow_and_batchLWE
    parameters discreteGaussianData polynomialGrowth wideWindow evaluate
    baseIsPPT evaluationIsPPT batchLWEIsPPT hEvaluationClosed hBatchLWEClosed
    wideWindow_fits executableCertificate_bound_negligible scaledWindow_negligible hBatchLWE

end

end FormalProof4FHE.TFHE.SharedRandomnessOneCycle.ConcreteWideGaussian
