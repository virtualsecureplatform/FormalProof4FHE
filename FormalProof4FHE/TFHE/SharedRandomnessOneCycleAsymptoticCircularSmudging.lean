/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessOneCycleCircularSmudging
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleAsymptoticCircularEncryption

/-!
# Asymptotic Removal of the One-Circular KDM Premise by Gaussian Smudging

For a coefficientwise certified discrete-Gaussian BRK sampler, the complete real self-BRK versus
zero-BRK advantage is bounded statistically by the number of native rows times the universal
ring-translation cost.  This module lifts that finite statement to VCVio's negligible-function
security framework and substitutes it into the reusable adaptive TFHE and public-evaluation
theorems.

The direct real-versus-zero composition retains the non-circular zero-BRK-with-shared-KSK LWE
endpoint and ordinary batch LWE.  A stronger averaging step proves that uniform stability under
all additive shifts makes the executable Gaussian itself close to exact uniform.  It therefore
discharges the zero-BRK endpoint too, and the strongest adaptive and public-evaluation theorems
retain only ordinary batch LWE.  The required Gaussian translation bound is deliberately exposed
as a numerical negligibility condition; satisfying it may require noise too wide for correctness,
so these are security-only theorems.
-/

open ENNReal OracleComp OracleSpec

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle.Asymptotic.CircularSecurity

noncomputable section

open FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.CircularSmudging

/-- Exact real-valued statistical loss for smudging every row of the complete rank-one self-BRK
at one security parameter. -/
noncomputable def discreteGaussianCircularSmudgingBound
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (securityParameter : ℕ) : ℝ :=
  (params.prefixDimension securityParameter : ℝ) *
    (TGSW.rowCount 1 (params.tgswLevels securityParameter) : ℕ) *
      discreteGaussianUniversalRowBound
        (params.q securityParameter)
        (params.prefixDimension securityParameter + params.suffixDimension securityParameter)
        (data.certificate securityParameter)

/-- The statistical smudging loss as a continuation-independent security game. -/
noncomputable def circularSmudgingSecurityGame
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params) :
    SecurityGame (ContinuationFamily params) where
  advantage _continuation securityParameter :=
    ENNReal.ofReal (discreteGaussianCircularSmudgingBound params data securityParameter)

/-! ## Polynomial layout accounting -/

/-- Number of coefficientwise scalar translation costs charged by complete-BRK smudging. -/
def circularSmudgingLayoutCount
    {Message : Type} (params : Parameters Message) (securityParameter : ℕ) : ℕ :=
  SamplerReplacement.bootstrappingErrorCount 1
      (params.tgswLevels securityParameter)
      (params.prefixDimension securityParameter) *
    (params.prefixDimension securityParameter + params.suffixDimension securityParameter)

/-- Polynomial growth witnesses for both the number of BRK rows and the native ring degree. -/
structure PolynomialCircularSmudgingGrowth
    {Message : Type} (params : Parameters Message)
    extends PolynomialBootstrapGrowth params where
  ringDegreePolynomial : Polynomial ℕ
  ringDegree_le : ∀ securityParameter,
    params.prefixDimension securityParameter + params.suffixDimension securityParameter ≤
      ringDegreePolynomial.eval securityParameter

/-- Polynomial envelope for the complete coefficientwise smudging layout. -/
noncomputable def circularSmudgingLayoutPolynomial
    {Message : Type} {params : Parameters Message}
    (growth : PolynomialCircularSmudgingGrowth params) : Polynomial ℕ :=
  bootstrappingDrawPolynomial growth.toPolynomialBootstrapGrowth *
    growth.ringDegreePolynomial

/-- The exact number of charged coefficient translations is polynomial under the declared
dimension growth. -/
theorem circularSmudgingLayoutCount_le_polynomial
    {Message : Type} {params : Parameters Message}
    (growth : PolynomialCircularSmudgingGrowth params)
    (securityParameter : ℕ) :
    circularSmudgingLayoutCount params securityParameter ≤
      (circularSmudgingLayoutPolynomial growth).eval securityParameter := by
  unfold circularSmudgingLayoutCount circularSmudgingLayoutPolynomial
  rw [Polynomial.eval_mul]
  exact Nat.mul_le_mul
    (bootstrappingErrorCount_le_polynomial
      growth.toPolynomialBootstrapGrowth securityParameter)
    (growth.ringDegree_le securityParameter)

/-- The exact real smudging bound is its layout count times one scalar Gaussian translation
bound. -/
theorem discreteGaussianCircularSmudgingBound_eq_layout_mul_scalar
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (securityParameter : ℕ) :
    discreteGaussianCircularSmudgingBound params data securityParameter =
      (circularSmudgingLayoutCount params securityParameter : ℝ) *
        DiscreteGaussianSampler.scalarLinearShiftBound
          (data.certificate securityParameter) (params.q securityParameter / 2) := by
  unfold discreteGaussianCircularSmudgingBound discreteGaussianUniversalRowBound
    circularSmudgingLayoutCount SamplerReplacement.bootstrappingErrorCount
  push_cast
  ring

/-- A negligible one-scalar universal translation cost remains negligible after charging every
coefficient of every polynomially many BRK rows. -/
theorem discreteGaussianCircularSmudgingBound_negligible
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (growth : PolynomialCircularSmudgingGrowth params)
    (hScalar : negligible (fun securityParameter ↦
      ENNReal.ofReal
        (DiscreteGaussianSampler.scalarLinearShiftBound
          (data.certificate securityParameter) (params.q securityParameter / 2)))) :
    negligible (fun securityParameter ↦
      ENNReal.ofReal
        (discreteGaussianCircularSmudgingBound params data securityParameter)) := by
  apply negligible_of_le (g := fun securityParameter ↦
    (((circularSmudgingLayoutPolynomial growth).eval securityParameter : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal
        (DiscreteGaussianSampler.scalarLinearShiftBound
          (data.certificate securityParameter) (params.q securityParameter / 2)))
  · intro securityParameter
    rw [discreteGaussianCircularSmudgingBound_eq_layout_mul_scalar]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (by
        exact_mod_cast
          circularSmudgingLayoutCount_le_polynomial growth securityParameter)
      zero_le
  · exact negligible_polynomial_mul hScalar
      (circularSmudgingLayoutPolynomial growth)

/-! ## Explicit finite-window criterion for the scalar translation cost -/

/-- Real finite-window upper bound for one arbitrary centered modular shift. -/
noncomputable def scalarUniversalFiniteWindowBound
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (window : ℕ → ℕ) (securityParameter : ℕ) : ℝ :=
  2 * (data.certificate securityParameter).bound.toReal +
    (params.q securityParameter / 2 : ℕ) *
      (Real.exp (1 / 2 : ℝ) / (window securityParameter + 1 : ℕ))

/-- ENNReal form separating certificate error from the modulus-scaled inverse Gaussian
window. -/
noncomputable def scalarUniversalWindowEnvelope
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (window : ℕ → ℕ) (securityParameter : ℕ) : ℝ≥0∞ :=
  2 * (data.certificate securityParameter).bound +
    (params.q securityParameter / 2 : ℕ) *
      ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
        ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹

/-- Exact coercion of the real finite-window bound to its separated ENNReal envelope. -/
theorem ofReal_scalarUniversalFiniteWindowBound_eq
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (window : ℕ → ℕ) (securityParameter : ℕ) :
    ENNReal.ofReal
        (scalarUniversalFiniteWindowBound params data window securityParameter) =
      scalarUniversalWindowEnvelope params data window securityParameter := by
  unfold scalarUniversalFiniteWindowBound scalarUniversalWindowEnvelope
  rw [ENNReal.ofReal_add
      (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
      (mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (le_of_lt (Real.exp_pos _)) (Nat.cast_nonneg _))),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_toReal (data.certificate securityParameter).bound_ne_top,
    ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) <
      (window securityParameter + 1 : ℕ))]
  norm_cast
  rw [div_eq_mul_inv]
  push_cast
  ring

/-- A Gaussian integer standard deviation containing the selected finite window bounds the
one-scalar universal translation loss by the separated envelope. -/
theorem ofReal_scalarLinearShiftBound_le_windowEnvelope
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (window : ℕ → ℕ)
    (hwindow : ∀ securityParameter,
      (window securityParameter : ℝ) ≤
        ModularGaussian.integerStddev
          (params.q securityParameter) (data.alpha securityParameter))
    (securityParameter : ℕ) :
    ENNReal.ofReal
        (DiscreteGaussianSampler.scalarLinearShiftBound
          (data.certificate securityParameter) (params.q securityParameter / 2)) ≤
      scalarUniversalWindowEnvelope params data window securityParameter := by
  calc
    ENNReal.ofReal
        (DiscreteGaussianSampler.scalarLinearShiftBound
          (data.certificate securityParameter) (params.q securityParameter / 2)) ≤
      ENNReal.ofReal
        (scalarUniversalFiniteWindowBound params data window securityParameter) := by
      apply ENNReal.ofReal_le_ofReal
      exact DiscreteGaussianSampler.scalarLinearShiftBound_le_exp_half_window
        (data.certificate securityParameter) (params.q securityParameter / 2)
        (window securityParameter) (hwindow securityParameter)
    _ = _ := ofReal_scalarUniversalFiniteWindowBound_eq
      params data window securityParameter

/-- Negligible certificate error and negligible modulus-scaled inverse window make the universal
one-scalar translation bound negligible. -/
theorem scalarLinearShiftBound_negligible_of_window
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (window : ℕ → ℕ)
    (hwindowFits : ∀ securityParameter,
      (window securityParameter : ℝ) ≤
        ModularGaussian.integerStddev
          (params.q securityParameter) (data.alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (data.certificate securityParameter).bound))
    (hscaledWindow : negligible (fun securityParameter ↦
      ((params.q securityParameter / 2 : ℕ) : ℝ≥0∞) *
        ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹)) :
    negligible (fun securityParameter ↦
      ENNReal.ofReal
        (DiscreteGaussianSampler.scalarLinearShiftBound
          (data.certificate securityParameter) (params.q securityParameter / 2))) := by
  apply negligible_of_le
    (ofReal_scalarLinearShiftBound_le_windowEnvelope
      params data window hwindowFits)
  unfold scalarUniversalWindowEnvelope
  apply negligible_add
  · simpa only [Pi.mul_apply] using
      negligible_const_mul hcertificate (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  · have hexp : ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    simpa only [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using
      negligible_const_mul hscaledWindow hexp

/-- Fully explicit asymptotic criterion: polynomial BRK layout, a fitting Gaussian window,
negligible finite-table error, and negligible modulus-over-window ratio make the complete
one-circular smudging loss negligible. -/
theorem discreteGaussianCircularSmudgingBound_negligible_of_window
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (growth : PolynomialCircularSmudgingGrowth params)
    (window : ℕ → ℕ)
    (hwindowFits : ∀ securityParameter,
      (window securityParameter : ℝ) ≤
        ModularGaussian.integerStddev
          (params.q securityParameter) (data.alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (data.certificate securityParameter).bound))
    (hscaledWindow : negligible (fun securityParameter ↦
      ((params.q securityParameter / 2 : ℕ) : ℝ≥0∞) *
        ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹)) :
    negligible (fun securityParameter ↦
      ENNReal.ofReal
        (discreteGaussianCircularSmudgingBound params data securityParameter)) :=
  discreteGaussianCircularSmudgingBound_negligible params data growth
    (scalarLinearShiftBound_negligible_of_window params data window hwindowFits
      hcertificate hscaledWindow)

/-! ## From universal shift invariance to a uniform BRK -/

/-- Pointwise, the one-draw distance of the certified Gaussian ring sampler from exact uniform
is bounded by the same universal ring-translation cost used for circular smudging. -/
theorem ringErrorGap_discreteGaussian_le_universalRowBound
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params) (securityParameter : ℕ) :
    ringErrorGap params (discreteGaussianRingErrorFamily params data) securityParameter ≤
      ENNReal.ofReal
        (discreteGaussianUniversalRowBound
          (params.q securityParameter)
          (params.prefixDimension securityParameter +
            params.suffixDimension securityParameter)
          (data.certificate securityParameter)) := by
  apply ENNReal.ofReal_le_ofReal
  exact tvDist_discreteGaussian_uniform_le_universalRowBound
    (params.q securityParameter)
    (params.prefixDimension securityParameter + params.suffixDimension securityParameter)
    (data.certificate securityParameter)

/-- Polynomial ring degree and negligible one-scalar universal shift cost imply that the
executable coefficientwise Gaussian is negligibly close to exact uniform per ring draw. -/
theorem ringErrorGap_discreteGaussian_negligible
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (growth : PolynomialCircularSmudgingGrowth params)
    (hScalar : negligible (fun securityParameter ↦
      ENNReal.ofReal
        (DiscreteGaussianSampler.scalarLinearShiftBound
          (data.certificate securityParameter) (params.q securityParameter / 2)))) :
    negligible
      (ringErrorGap params (discreteGaussianRingErrorFamily params data)) := by
  apply negligible_of_le (g := fun securityParameter ↦
    (((growth.ringDegreePolynomial.eval securityParameter : ℕ) : ℝ≥0∞)) *
      ENNReal.ofReal
        (DiscreteGaussianSampler.scalarLinearShiftBound
          (data.certificate securityParameter) (params.q securityParameter / 2)))
  · intro securityParameter
    calc
      ringErrorGap params (discreteGaussianRingErrorFamily params data)
          securityParameter ≤
        ENNReal.ofReal
          (discreteGaussianUniversalRowBound
            (params.q securityParameter)
            (params.prefixDimension securityParameter +
              params.suffixDimension securityParameter)
            (data.certificate securityParameter)) :=
        ringErrorGap_discreteGaussian_le_universalRowBound
          params data securityParameter
      _ = ((params.prefixDimension securityParameter +
              params.suffixDimension securityParameter : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal
              (DiscreteGaussianSampler.scalarLinearShiftBound
                (data.certificate securityParameter)
                (params.q securityParameter / 2)) := by
        unfold discreteGaussianUniversalRowBound
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ (((growth.ringDegreePolynomial.eval securityParameter : ℕ) : ℝ≥0∞)) *
            ENNReal.ofReal
              (DiscreteGaussianSampler.scalarLinearShiftBound
                (data.certificate securityParameter)
                (params.q securityParameter / 2)) := by
        apply mul_le_mul_of_nonneg_right
        exact_mod_cast growth.ringDegree_le securityParameter
        exact zero_le
  · exact negligible_polynomial_mul hScalar growth.ringDegreePolynomial

/-- **Complete adaptive TFHE security with no circular or zero-BRK hardness premise.**

Universal Gaussian shift invariance makes each executable ring error negligibly close to exact
uniform.  The existing uniform-BRK hybrid then leaves only the ordinary query-counted scalar
batch-LWE problem.  This theorem is security-only: the required wide noise is not asserted to
preserve TFHE correctness. -/
theorem implementationSecureAgainst_of_discreteGaussianShiftInvariance_and_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (growth : PolynomialCircularSmudgingGrowth params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hScalar : negligible (fun securityParameter ↦
      ENNReal.ofReal
        (DiscreteGaussianSampler.scalarLinearShiftBound
          (data.certificate securityParameter) (params.q securityParameter / 2))))
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (implementationSecurityGame params
      (discreteGaussianRingErrorFamily params data)).secureAgainst isPPT := by
  exact implementationSecureAgainst_of_batchLWE
    params (discreteGaussianRingErrorFamily params data)
    growth.toPolynomialBootstrapGrowth isPPT batchLWEIsPPT hBatchLWEClosed hBatchLWE
    (ringErrorGap_discreteGaussian_negligible params data growth hScalar)

/-- Explicit finite-window corollary of the complete no-circular-assumption theorem. -/
theorem implementationSecureAgainst_of_discreteGaussianWindow_and_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (growth : PolynomialCircularSmudgingGrowth params)
    (window : ℕ → ℕ)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hwindowFits : ∀ securityParameter,
      (window securityParameter : ℝ) ≤
        ModularGaussian.integerStddev
          (params.q securityParameter) (data.alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (data.certificate securityParameter).bound))
    (hscaledWindow : negligible (fun securityParameter ↦
      ((params.q securityParameter / 2 : ℕ) : ℝ≥0∞) *
        ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹))
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (implementationSecurityGame params
      (discreteGaussianRingErrorFamily params data)).secureAgainst isPPT := by
  exact implementationSecureAgainst_of_discreteGaussianShiftInvariance_and_batchLWE
    params data growth isPPT batchLWEIsPPT hBatchLWEClosed
    (scalarLinearShiftBound_negligible_of_window
      params data window hwindowFits hcertificate hscaledWindow)
    hBatchLWE

/-- Public deterministic FHE evaluation adds no assumption or loss to the complete
shift-invariance theorem. -/
theorem implementationEvaluationSecureAgainst_of_discreteGaussianShiftInvariance_and_batchLWE
    {Message Output : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (growth : PolynomialCircularSmudgingGrowth params)
    (evaluate : PublicEvaluatorFamily (Output := Output) params)
    (baseIsPPT : PolynomialQueryAdversary params → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary params evaluate adversary))
    (hBatchLWEClosed : ∀ adversary, baseIsPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hScalar : negligible (fun securityParameter ↦
      ENNReal.ofReal
        (DiscreteGaussianSampler.scalarLinearShiftBound
          (data.certificate securityParameter) (params.q securityParameter / 2))))
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (implementationEvaluationSecurityGame params
      (discreteGaussianRingErrorFamily params data) evaluate).secureAgainst
        evaluationIsPPT := by
  exact implementationEvaluationSecureAgainst_of_security
    params (discreteGaussianRingErrorFamily params data) evaluate
    baseIsPPT evaluationIsPPT hEvaluationClosed
    (implementationSecureAgainst_of_discreteGaussianShiftInvariance_and_batchLWE
      params data growth baseIsPPT batchLWEIsPPT hBatchLWEClosed hScalar hBatchLWE)

/-- Explicit finite-window form of security after arbitrary public deterministic FHE
evaluation. -/
theorem implementationEvaluationSecureAgainst_of_discreteGaussianWindow_and_batchLWE
    {Message Output : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (growth : PolynomialCircularSmudgingGrowth params)
    (window : ℕ → ℕ)
    (evaluate : PublicEvaluatorFamily (Output := Output) params)
    (baseIsPPT : PolynomialQueryAdversary params → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary params evaluate adversary))
    (hBatchLWEClosed : ∀ adversary, baseIsPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hwindowFits : ∀ securityParameter,
      (window securityParameter : ℝ) ≤
        ModularGaussian.integerStddev
          (params.q securityParameter) (data.alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (data.certificate securityParameter).bound))
    (hscaledWindow : negligible (fun securityParameter ↦
      ((params.q securityParameter / 2 : ℕ) : ℝ≥0∞) *
        ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹))
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (implementationEvaluationSecurityGame params
      (discreteGaussianRingErrorFamily params data) evaluate).secureAgainst
        evaluationIsPPT := by
  exact implementationEvaluationSecureAgainst_of_discreteGaussianShiftInvariance_and_batchLWE
    params data growth evaluate baseIsPPT evaluationIsPPT batchLWEIsPPT
    hEvaluationClosed hBatchLWEClosed
    (scalarLinearShiftBound_negligible_of_window
      params data window hwindowFits hcertificate hscaledWindow)
    hBatchLWE

/-- Pointwise, the literal real-versus-zero one-circular KDM game is bounded entirely by the
certified-Gaussian statistical translation loss. -/
theorem kdmSecurityGame_advantage_le_discreteGaussianCircularSmudging
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (continuation : ContinuationFamily params) (securityParameter : ℕ) :
    (kdmSecurityGame params (discreteGaussianRingErrorFamily params data)).advantage
        continuation securityParameter ≤
      (circularSmudgingSecurityGame params data).advantage continuation
        securityParameter := by
  apply ENNReal.ofReal_le_ofReal
  rw [Native.SharedRandomnessOneCycle.AuxiliaryInput.kdmAdvantage_eq_secretContinuationAdvantage]
  exact secretContinuationAdvantage_discreteGaussian_le
    (params.q securityParameter)
    (params.prefixDimension securityParameter)
    (params.suffixDimension securityParameter)
    (params.tgswLevels securityParameter)
    (params.keySwitchLevels securityParameter)
    (data.certificate securityParameter)
    (params.scalarErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    (continuation securityParameter)

/-- A negligible explicit row-smudging bound proves the literal one-circular KDM game secure for
every selected continuation family; no computational circular assumption is used. -/
theorem kdmSecurityGame_secureAgainst_of_discreteGaussianCircularSmudging
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (isPPT : ContinuationFamily params → Prop)
    (hSmudging : negligible (fun securityParameter ↦
      ENNReal.ofReal
        (discreteGaussianCircularSmudgingBound params data securityParameter))) :
    (kdmSecurityGame params (discreteGaussianRingErrorFamily params data)).secureAgainst
      isPPT := by
  intro continuation _hcontinuation
  exact negligible_of_le
    (kdmSecurityGame_advantage_le_discreteGaussianCircularSmudging
      params data continuation)
    hSmudging

/-- Adaptive one-circular KDM security follows from the same numerical smudging condition. -/
theorem adaptiveKDMSecurityGame_secureAgainst_of_discreteGaussianCircularSmudging
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (hSmudging : negligible (fun securityParameter ↦
      ENNReal.ofReal
        (discreteGaussianCircularSmudgingBound params data securityParameter))) :
    (adaptiveKDMSecurityGame params
      (discreteGaussianRingErrorFamily params data)).secureAgainst isPPT := by
  intro adversary _hadversary
  exact negligible_of_le
    (kdmSecurityGame_advantage_le_discreteGaussianCircularSmudging
      params data (continuationReduction params adversary))
    hSmudging

/-- **Reusable adaptive TFHE security with the circular KDM premise discharged
statistically.**

For the certified discrete-Gaussian BRK family, negligible complete-row translation loss,
non-circular zero-BRK auxiliary-input LWE security, and ordinary batch-LWE security imply the
honest adaptive TFHE encryption game. -/
theorem implementationSecureAgainst_of_discreteGaussianSmudging_zeroBootstrapLWE_and_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hSmudging : negligible (fun securityParameter ↦
      ENNReal.ofReal
        (discreteGaussianCircularSmudgingBound params data securityParameter)))
    (hZeroBootstrap :
      (adaptiveZeroBootstrapLWESecurityGame params
        (discreteGaussianRingErrorFamily params data)).secureAgainst isPPT)
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (implementationSecurityGame params
      (discreteGaussianRingErrorFamily params data)).secureAgainst isPPT := by
  exact implementationSecureAgainst_of_oneCircularKDM_zeroBootstrapLWE_and_batchLWE
    params (discreteGaussianRingErrorFamily params data) isPPT batchLWEIsPPT
    hBatchLWEClosed
    (adaptiveKDMSecurityGame_secureAgainst_of_discreteGaussianCircularSmudging
      params data isPPT hSmudging)
    hZeroBootstrap hBatchLWE

/-- Public deterministic FHE evaluation preserves the statistically discharged circular theorem
without introducing another circular assumption. -/
theorem implementationEvaluationSecureAgainst_of_discreteGaussianSmudging_zeroBootstrapLWE_and_batchLWE
    {Message Output : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params)
    (evaluate : PublicEvaluatorFamily (Output := Output) params)
    (baseIsPPT : PolynomialQueryAdversary params → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary params evaluate adversary))
    (hBatchLWEClosed : ∀ adversary, baseIsPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hSmudging : negligible (fun securityParameter ↦
      ENNReal.ofReal
        (discreteGaussianCircularSmudgingBound params data securityParameter)))
    (hZeroBootstrap :
      (adaptiveZeroBootstrapLWESecurityGame params
        (discreteGaussianRingErrorFamily params data)).secureAgainst baseIsPPT)
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (implementationEvaluationSecurityGame params
      (discreteGaussianRingErrorFamily params data) evaluate).secureAgainst
        evaluationIsPPT := by
  exact implementationEvaluationSecureAgainst_of_security
    params (discreteGaussianRingErrorFamily params data) evaluate
    baseIsPPT evaluationIsPPT hEvaluationClosed
    (implementationSecureAgainst_of_discreteGaussianSmudging_zeroBootstrapLWE_and_batchLWE
      params data baseIsPPT batchLWEIsPPT hBatchLWEClosed hSmudging
      hZeroBootstrap hBatchLWE)

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle.Asymptotic.CircularSecurity
