/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AsymptoticSecurity
import FormalProof4FHE.TFHE.SamplerReplacement

/-!
# Asymptotic TFHE Error-Sampler Replacement

`TFHE.SamplerReplacement` proves a pointwise finite bound for replacing the ring, key-switch, and
adaptive-input error samplers.  This module lifts that result to VCVio's negligible-function
framework.  Polynomial witnesses account for every bootstrapping-key and key-switch-key row, while
the adaptive adversary already carries a polynomial query bound.

Consequently, negligible one-draw total-variation gaps remain negligible after all native TFHE
evaluation-key and adaptive-query draws.  The final theorems transfer the existing asymptotic
direct-bilinear circular/KDM plus LWE security theorem from reference samplers to implementation
samplers.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic

/-- A second triple of executable finite error samplers with the same moduli and dimensions as a
reference `Parameters` family. -/
structure ErrorSamplerFamily {Message : Type} (params : Parameters Message) where
  ringErrorSampler : (securityParameter : ℕ) →
    ProbComp (RLWE.Rq (params.q securityParameter) (params.degree securityParameter))
  keySwitchErrorSampler : (securityParameter : ℕ) →
    ProbComp (ZMod (params.q securityParameter))
  inputErrorSampler : (securityParameter : ℕ) →
    ProbComp (ZMod (params.q securityParameter))

/-- The sampler triple already stored in the reference parameter family. -/
def ErrorSamplerFamily.reference {Message : Type} (params : Parameters Message) :
    ErrorSamplerFamily params where
  ringErrorSampler := params.ringErrorSampler
  keySwitchErrorSampler := params.keySwitchErrorSampler
  inputErrorSampler := params.inputErrorSampler

/-- One-draw ring-error total-variation gap between implementation and reference samplers. -/
noncomputable def ringSamplerGap {Message : Type} (params : Parameters Message)
    (implementation : ErrorSamplerFamily params) (securityParameter : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (tvDist
    (implementation.ringErrorSampler securityParameter)
    (params.ringErrorSampler securityParameter))

/-- One-draw key-switch-error total-variation gap. -/
noncomputable def keySwitchSamplerGap {Message : Type} (params : Parameters Message)
    (implementation : ErrorSamplerFamily params) (securityParameter : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (tvDist
    (implementation.keySwitchErrorSampler securityParameter)
    (params.keySwitchErrorSampler securityParameter))

/-- One-draw adaptive-input-error total-variation gap. -/
noncomputable def inputSamplerGap {Message : Type} (params : Parameters Message)
    (implementation : ErrorSamplerFamily params) (securityParameter : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (tvDist
    (implementation.inputErrorSampler securityParameter)
    (params.inputErrorSampler securityParameter))

/-- Honest adaptive TFHE security game using implementation samplers but all dimensions, gadgets,
encodings, and adversary types from the reference parameters. -/
noncomputable def implementationSecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params) :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter := ENNReal.ofReal
    |Encryption.signedAdvantage
      (Adaptive.realGame
        (adversary.queryCount securityParameter)
        (implementation.ringErrorSampler securityParameter)
        (implementation.keySwitchErrorSampler securityParameter)
        (implementation.inputErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))|

/-- The exact finite sampler-replacement cost, viewed as an asymptotic security game. -/
noncomputable def replacementSecurityGame {Message : Type} (params : Parameters Message)
    (implementation : ErrorSamplerFamily params) :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter := ENNReal.ofReal
    (TFHE.SamplerReplacement.adaptiveReplacementCost
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.tgswLevels securityParameter)
      (params.lweDimension securityParameter)
      (params.keySwitchLevels securityParameter)
      (adversary.queryCount securityParameter)
      (implementation.ringErrorSampler securityParameter)
      (params.ringErrorSampler securityParameter)
      (implementation.keySwitchErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (implementation.inputErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter))

/-- Pointwise implementation advantage is at most reference advantage plus the complete sampler
replacement loss. -/
theorem implementationSecurityGame_advantage_le_reference_add_replacement
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (implementationSecurityGame params implementation).advantage adversary securityParameter ≤
      (securityGame params).advantage adversary securityParameter +
        (replacementSecurityGame params implementation).advantage adversary securityParameter := by
  have h := TFHE.SamplerReplacement.abs_signedAdvantage_adaptiveReal_le_reference_add
    (params.q securityParameter)
    (params.degree securityParameter)
    (params.ringRank securityParameter)
    (params.tgswLevels securityParameter)
    (params.lweDimension securityParameter)
    (params.keySwitchLevels securityParameter)
    (adversary.queryCount securityParameter)
    (implementation.ringErrorSampler securityParameter)
    (params.ringErrorSampler securityParameter)
    (implementation.keySwitchErrorSampler securityParameter)
    (params.keySwitchErrorSampler securityParameter)
    (implementation.inputErrorSampler securityParameter)
    (params.inputErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    (params.encode securityParameter)
    (adversary.run securityParameter)
  exact (ENNReal.ofReal_le_ofReal h).trans ENNReal.ofReal_add_le

/-! ## Polynomial native draw counts -/

/-- Polynomial growth witnesses for every evaluation-key error draw.  The inherited fields cover
the KSK dimensions; the additional fields cover the outer BRK coordinate count and TGSW levels. -/
structure PolynomialEvaluationKeyGrowth {Message : Type} (params : Parameters Message)
    extends PolynomialKeySwitchGrowth params where
  tgswLevelsPolynomial : Polynomial ℕ
  lweDimensionPolynomial : Polynomial ℕ
  tgswLevels_le : ∀ securityParameter,
    params.tgswLevels securityParameter ≤ tgswLevelsPolynomial.eval securityParameter
  lweDimension_le : ∀ securityParameter,
    params.lweDimension securityParameter ≤ lweDimensionPolynomial.eval securityParameter

/-- Polynomial upper bound for all ring-error draws in the native bootstrapping key. -/
noncomputable def bootstrappingDrawPolynomial {Message : Type} {params : Parameters Message}
    (growth : PolynomialEvaluationKeyGrowth params) : Polynomial ℕ :=
  growth.lweDimensionPolynomial *
    ((growth.ringRankPolynomial + 1) * growth.tgswLevelsPolynomial)

/-- Polynomial upper bound for all scalar-error draws in the native key-switch key. -/
noncomputable def keySwitchDrawPolynomial {Message : Type} {params : Parameters Message}
    (growth : PolynomialEvaluationKeyGrowth params) : Polynomial ℕ :=
  (growth.ringRankPolynomial * growth.degreePolynomial) *
    growth.keySwitchLevelsPolynomial

/-- Exact BRK draw accounting is bounded by `bootstrappingDrawPolynomial`. -/
theorem bootstrappingErrorCount_le_polynomial
    {Message : Type} {params : Parameters Message}
    (growth : PolynomialEvaluationKeyGrowth params) (securityParameter : ℕ) :
    TFHE.SamplerReplacement.bootstrappingErrorCount
        (params.ringRank securityParameter)
        (params.tgswLevels securityParameter)
        (params.lweDimension securityParameter) ≤
      (bootstrappingDrawPolynomial growth).eval securityParameter := by
  simp only [TFHE.SamplerReplacement.bootstrappingErrorCount, TGSW.rowCount,
    bootstrappingDrawPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_one]
  exact Nat.mul_le_mul
    (growth.lweDimension_le securityParameter)
    (Nat.mul_le_mul
      (Nat.add_le_add (growth.ringRank_le securityParameter) le_rfl)
      (growth.tgswLevels_le securityParameter))

/-- Exact KSK draw accounting is bounded by `keySwitchDrawPolynomial`. -/
theorem keySwitchErrorCount_le_polynomial
    {Message : Type} {params : Parameters Message}
    (growth : PolynomialEvaluationKeyGrowth params) (securityParameter : ℕ) :
    TFHE.SamplerReplacement.keySwitchErrorCount
        (params.ringRank securityParameter)
        (params.degree securityParameter)
        (params.keySwitchLevels securityParameter) ≤
      (keySwitchDrawPolynomial growth).eval securityParameter := by
  simp only [TFHE.SamplerReplacement.keySwitchErrorCount, keySwitchDrawPolynomial,
    Polynomial.eval_mul]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul
      (growth.ringRank_le securityParameter)
      (growth.degree_le securityParameter))
    (growth.keySwitchLevels_le securityParameter)

/-- The replacement game is exactly the three native draw counts multiplied by their respective
one-draw total-variation gaps. -/
theorem replacementSecurityGame_advantage_eq_draws_mul_gaps
    {Message : Type} (params : Parameters Message)
    (implementation : ErrorSamplerFamily params)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (replacementSecurityGame params implementation).advantage adversary securityParameter =
      (TFHE.SamplerReplacement.bootstrappingErrorCount
          (params.ringRank securityParameter)
          (params.tgswLevels securityParameter)
          (params.lweDimension securityParameter) : ℝ≥0∞) *
          ringSamplerGap params implementation securityParameter +
        (TFHE.SamplerReplacement.keySwitchErrorCount
          (params.ringRank securityParameter)
          (params.degree securityParameter)
          (params.keySwitchLevels securityParameter) : ℝ≥0∞) *
          keySwitchSamplerGap params implementation securityParameter +
        (adversary.queryCount securityParameter : ℝ≥0∞) *
          inputSamplerGap params implementation securityParameter := by
  have hRingTV : 0 ≤ tvDist
      (implementation.ringErrorSampler securityParameter)
      (params.ringErrorSampler securityParameter) :=
    tvDist_nonneg (m := ProbComp) _ _
  have hSwitchTV : 0 ≤ tvDist
      (implementation.keySwitchErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter) :=
    tvDist_nonneg (m := ProbComp) _ _
  have hInputTV : 0 ≤ tvDist
      (implementation.inputErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter) :=
    tvDist_nonneg (m := ProbComp) _ _
  have hBoot : 0 ≤
      (TFHE.SamplerReplacement.bootstrappingErrorCount
        (params.ringRank securityParameter)
        (params.tgswLevels securityParameter)
        (params.lweDimension securityParameter) : ℝ) *
        tvDist (implementation.ringErrorSampler securityParameter)
          (params.ringErrorSampler securityParameter) :=
    mul_nonneg (Nat.cast_nonneg _) hRingTV
  have hSwitch : 0 ≤
      (TFHE.SamplerReplacement.keySwitchErrorCount
        (params.ringRank securityParameter)
        (params.degree securityParameter)
        (params.keySwitchLevels securityParameter) : ℝ) *
        tvDist (implementation.keySwitchErrorSampler securityParameter)
          (params.keySwitchErrorSampler securityParameter) :=
    mul_nonneg (Nat.cast_nonneg _) hSwitchTV
  have hInput : 0 ≤ (adversary.queryCount securityParameter : ℝ) *
      tvDist (implementation.inputErrorSampler securityParameter)
        (params.inputErrorSampler securityParameter) :=
    mul_nonneg (Nat.cast_nonneg _) hInputTV
  simp only [replacementSecurityGame, TFHE.SamplerReplacement.adaptiveReplacementCost,
    ringSamplerGap, keySwitchSamplerGap, inputSamplerGap]
  rw [ENNReal.ofReal_add (add_nonneg hBoot hSwitch) hInput,
    ENNReal.ofReal_add hBoot hSwitch,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- Polynomial growth of all native draw counts bounds the replacement game by three polynomial
multiples of the one-draw gaps. -/
theorem replacementSecurityGame_advantage_le_polynomial_gaps
    {Message : Type} (params : Parameters Message)
    (implementation : ErrorSamplerFamily params)
    (growth : PolynomialEvaluationKeyGrowth params)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (replacementSecurityGame params implementation).advantage adversary securityParameter ≤
      (((bootstrappingDrawPolynomial growth).eval securityParameter : ℕ) : ℝ≥0∞) *
          ringSamplerGap params implementation securityParameter +
        (((keySwitchDrawPolynomial growth).eval securityParameter : ℕ) : ℝ≥0∞) *
          keySwitchSamplerGap params implementation securityParameter +
        ((adversary.queryPolynomial.eval securityParameter : ℕ) : ℝ≥0∞) *
          inputSamplerGap params implementation securityParameter := by
  rw [replacementSecurityGame_advantage_eq_draws_mul_gaps]
  have hBoot :
      (TFHE.SamplerReplacement.bootstrappingErrorCount
        (params.ringRank securityParameter)
        (params.tgswLevels securityParameter)
        (params.lweDimension securityParameter) : ℝ≥0∞) ≤
      (((bootstrappingDrawPolynomial growth).eval securityParameter : ℕ) : ℝ≥0∞) := by
    exact_mod_cast bootstrappingErrorCount_le_polynomial growth securityParameter
  have hSwitch :
      (TFHE.SamplerReplacement.keySwitchErrorCount
        (params.ringRank securityParameter)
        (params.degree securityParameter)
        (params.keySwitchLevels securityParameter) : ℝ≥0∞) ≤
      (((keySwitchDrawPolynomial growth).eval securityParameter : ℕ) : ℝ≥0∞) := by
    exact_mod_cast keySwitchErrorCount_le_polynomial growth securityParameter
  have hQuery :
      (adversary.queryCount securityParameter : ℝ≥0∞) ≤
      ((adversary.queryPolynomial.eval securityParameter : ℕ) : ℝ≥0∞) := by
    exact_mod_cast adversary.queryCount_le securityParameter
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_right hBoot zero_le)
      (mul_le_mul_of_nonneg_right hSwitch zero_le))
    (mul_le_mul_of_nonneg_right hQuery zero_le)

/-! ## Negligible replacement and security transfer -/

/-- Negligible one-draw gaps remain negligible after every polynomially many BRK, KSK, and
adaptive-input draw. -/
theorem replacementSecurityGame_advantage_negligible
    {Message : Type} (params : Parameters Message)
    (implementation : ErrorSamplerFamily params)
    (growth : PolynomialEvaluationKeyGrowth params)
    (hRing : negligible (ringSamplerGap params implementation))
    (hKeySwitch : negligible (keySwitchSamplerGap params implementation))
    (hInput : negligible (inputSamplerGap params implementation))
    (adversary : PolynomialQueryAdversary params) :
    negligible ((replacementSecurityGame params implementation).advantage adversary) := by
  have hPolynomialLoss : negligible (fun securityParameter ↦
      (((bootstrappingDrawPolynomial growth).eval securityParameter : ℕ) : ℝ≥0∞) *
          ringSamplerGap params implementation securityParameter +
        (((keySwitchDrawPolynomial growth).eval securityParameter : ℕ) : ℝ≥0∞) *
          keySwitchSamplerGap params implementation securityParameter +
        ((adversary.queryPolynomial.eval securityParameter : ℕ) : ℝ≥0∞) *
          inputSamplerGap params implementation securityParameter) := by
    exact negligible_add
      (negligible_add
        (negligible_polynomial_mul hRing (bootstrappingDrawPolynomial growth))
        (negligible_polynomial_mul hKeySwitch (keySwitchDrawPolynomial growth)))
      (negligible_polynomial_mul hInput adversary.queryPolynomial)
  exact negligible_of_le
    (replacementSecurityGame_advantage_le_polynomial_gaps
      params implementation growth adversary)
    hPolynomialLoss

/-- Any reference-sampler asymptotic TFHE security theorem transfers to implementation samplers
when all three one-draw gaps are negligible and evaluation-key dimensions grow polynomially. -/
theorem implementationSecurityGame_secureAgainst_of_reference
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (growth : PolynomialEvaluationKeyGrowth params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (hReference : (securityGame params).secureAgainst isPPT)
    (hRing : negligible (ringSamplerGap params implementation))
    (hKeySwitch : negligible (keySwitchSamplerGap params implementation))
    (hInput : negligible (inputSamplerGap params implementation)) :
    (implementationSecurityGame params implementation).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (implementationSecurityGame_advantage_le_reference_add_replacement
      params implementation adversary)
    (negligible_add
      (hReference adversary hadversary)
      (replacementSecurityGame_advantage_negligible
        params implementation growth hRing hKeySwitch hInput adversary))

/-- Pointwise asymptotic implementation bound with the reference circular/KDM and heterogeneous
joint-LWE terms exposed. -/
theorem implementationSecurityGame_advantage_le_directBilinear_add_jointLWE_add_replacement
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (implementationSecurityGame params implementation).advantage adversary securityParameter ≤
      (directBilinearSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter +
        (replacementSecurityGame params implementation).advantage
          adversary securityParameter := by
  calc
    (implementationSecurityGame params implementation).advantage adversary
        securityParameter ≤
      (securityGame params).advantage adversary securityParameter +
        (replacementSecurityGame params implementation).advantage adversary
          securityParameter :=
      implementationSecurityGame_advantage_le_reference_add_replacement
        params implementation adversary securityParameter
    _ ≤
      ((directBilinearSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter) +
        (replacementSecurityGame params implementation).advantage adversary
          securityParameter :=
      add_le_add
        (securityGame_advantage_le_directBilinear_add_jointLWE
          params adversary securityParameter)
        le_rfl

/-- Pointwise equal-reference-noise specialization using ordinary query-counted batch LWE. -/
theorem implementationSecurityGame_advantage_le_directBilinear_add_batchLWE_add_replacement
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (hEqualReferenceNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (implementationSecurityGame params implementation).advantage adversary securityParameter ≤
      (directBilinearSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter +
        (replacementSecurityGame params implementation).advantage
          adversary securityParameter := by
  calc
    (implementationSecurityGame params implementation).advantage adversary
        securityParameter ≤
      (securityGame params).advantage adversary securityParameter +
        (replacementSecurityGame params implementation).advantage adversary
          securityParameter :=
      implementationSecurityGame_advantage_le_reference_add_replacement
        params implementation adversary securityParameter
    _ ≤
      ((directBilinearSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter) +
        (replacementSecurityGame params implementation).advantage adversary
          securityParameter :=
      add_le_add
        (securityGame_advantage_le_directBilinear_add_batchLWE
          params hEqualReferenceNoise adversary securityParameter)
        le_rfl

/-- **Asymptotic implementation security with distinct reference scalar noises.**

Negligible native direct-bilinear circular/KDM advantage, negligible reference joint-LWE
advantage, and negligible one-draw implementation/reference sampler gaps imply negligible honest
adaptive TFHE implementation advantage. -/
theorem implementationSecurityGame_secureAgainst_of_directBilinear_and_jointLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (growth : PolynomialEvaluationKeyGrowth params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (continuationIsPPT : ContinuationFamily params → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily params → Prop)
    (hContinuationClosed : ∀ adversary, isPPT adversary →
      continuationIsPPT (continuationReduction params adversary))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction params adversary))
    (hCircular : (directBilinearSecurityGame params).secureAgainst continuationIsPPT)
    (hJointLWE : (jointLWESecurityGame params).secureAgainst jointLWEIsPPT)
    (hRing : negligible (ringSamplerGap params implementation))
    (hKeySwitch : negligible (keySwitchSamplerGap params implementation))
    (hInput : negligible (inputSamplerGap params implementation)) :
    (implementationSecurityGame params implementation).secureAgainst isPPT := by
  exact implementationSecurityGame_secureAgainst_of_reference
    params implementation growth isPPT
    (secureAgainst_of_directBilinear_and_jointLWE
      params isPPT continuationIsPPT jointLWEIsPPT
      hContinuationClosed hJointLWEClosed hCircular hJointLWE)
    hRing hKeySwitch hInput

/-- **Asymptotic implementation security from native circular/KDM and ordinary batch LWE.**

Only the reference scalar samplers must coincide.  The implementation KSK and input samplers may
differ, provided that each is negligibly close to the corresponding reference sampler. -/
theorem implementationSecurityGame_secureAgainst_of_directBilinear_and_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (growth : PolynomialEvaluationKeyGrowth params)
    (hEqualReferenceNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (continuationIsPPT : ContinuationFamily params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hContinuationClosed : ∀ adversary, isPPT adversary →
      continuationIsPPT (continuationReduction params adversary))
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hCircular : (directBilinearSecurityGame params).secureAgainst continuationIsPPT)
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT)
    (hRing : negligible (ringSamplerGap params implementation))
    (hKeySwitch : negligible (keySwitchSamplerGap params implementation))
    (hInput : negligible (inputSamplerGap params implementation)) :
    (implementationSecurityGame params implementation).secureAgainst isPPT := by
  exact implementationSecurityGame_secureAgainst_of_reference
    params implementation growth isPPT
    (secureAgainst_of_directBilinear_and_batchLWE
      params hEqualReferenceNoise isPPT continuationIsPPT batchLWEIsPPT
      hContinuationClosed hBatchLWEClosed hCircular hBatchLWE)
    hRing hKeySwitch hInput

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic
