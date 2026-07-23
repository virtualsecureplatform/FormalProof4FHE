/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessOneCycleAdaptiveEncryption
import VCVio.CryptoFoundations.Asymptotics.Security

/-!
# Asymptotic Security of Shared-Randomness One-Cycle TFHE

This module packages the exact uniform-BRK finite theorem as a conventional asymptotic security
result.  A single master ring key is split into the scalar encryption-key prefix and the
key-switch-message suffix.  The suffix-only KSK and every adaptive input ciphertext then reduce
to one ordinary binary-secret batch-LWE instance.

The BRK is still the genuine self-circular native TGSW key.  Exactly uniform ring-row error makes
it statistically independent of its secret-dependent messages, so the resulting reusable-key
security theorem assumes only ordinary batch LWE and no circular/KDM game.
-/

open ENNReal OracleComp OracleSpec

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle.Asymptotic

noncomputable section

/-- Security-parameter-indexed parameters for the uniform-BRK shared-randomness construction. -/
structure Parameters (Message : Type) where
  q : ℕ → ℕ
  prefixDimension : ℕ → ℕ
  suffixDimension : ℕ → ℕ
  tgswLevels : ℕ → ℕ
  keySwitchLevels : ℕ → ℕ
  scalarErrorSampler : (securityParameter : ℕ) → ProbComp (ZMod (q securityParameter))
  tgswGadget : (securityParameter : ℕ) →
    Fin (tgswLevels securityParameter) →
      RLWE.Rq (q securityParameter)
        (prefixDimension securityParameter + suffixDimension securityParameter)
  keySwitchGadget : (securityParameter : ℕ) →
    Fin (keySwitchLevels securityParameter) → ZMod (q securityParameter)
  encode : (securityParameter : ℕ) → Message → ZMod (q securityParameter)

/-- A family of adaptive adversaries for the shared cloud-key layout. -/
abbrev NativeAdversaryFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :=
  (securityParameter : ℕ) →
    SharedAdversary Message
      (params.q securityParameter)
      (params.prefixDimension securityParameter)
      (params.suffixDimension securityParameter)
      (params.tgswLevels securityParameter)
      (params.keySwitchLevels securityParameter)

/-- An adaptive adversary family carrying an explicit polynomial encryption-query bound. -/
structure PolynomialQueryAdversary {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] where
  run : NativeAdversaryFamily params
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  isQueryBound : ∀ securityParameter,
    Adaptive.IsQueryBound (run securityParameter) (queryCount securityParameter)

/-- The ordinary binary-secret batch-LWE adversary type at one security parameter. -/
abbrev BatchLWEAdversaryAt {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :=
  LearningWithErrors.Adversary
    (Native.KeySwitchSecurity.binaryLweProblem
      (params.q securityParameter)
      (params.prefixDimension securityParameter)
      (keySwitchSamples
          (params.suffixDimension securityParameter)
          (params.keySwitchLevels securityParameter) +
        queryCount securityParameter)
      (params.scalarErrorSampler securityParameter))

/-- A query-counted batch-LWE adversary family produced by the exact finite reduction. -/
structure BatchLWEAdversaryFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  run : (securityParameter : ℕ) →
    BatchLWEAdversaryAt params queryCount securityParameter

/-- Query-counted ordinary binary-secret batch-LWE security game. -/
noncomputable def batchLWESecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (BatchLWEAdversaryFamily params) where
  advantage adversary securityParameter := ENNReal.ofReal
    (LearningWithErrors.advantage
      (Native.KeySwitchSecurity.binaryLweProblem
        (params.q securityParameter)
        (params.prefixDimension securityParameter)
        (keySwitchSamples
            (params.suffixDimension securityParameter)
            (params.keySwitchLevels securityParameter) +
          adversary.queryCount securityParameter)
        (params.scalarErrorSampler securityParameter))
      (adversary.run securityParameter))

/-- Pointwise ordinary batch-LWE reduction for the complete suffix KSK and adaptive input tape. -/
noncomputable def batchLWEReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) : BatchLWEAdversaryFamily params where
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  run securityParameter :=
    FormalProof4FHE.LWE.TwoBlock.reduction
      (jointLweReduction
        (params.scalarErrorSampler securityParameter)
        (params.scalarErrorSampler securityParameter)
        (params.keySwitchGadget securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))

/-- Honest reusable-key adaptive security game with a genuinely generated self-circular BRK and
exactly uniform ring-row errors. -/
noncomputable def securityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter := ENNReal.ofReal
    |Encryption.signedAdvantage
      (realGame
        (adversary.queryCount securityParameter)
        ($ᵗ (RLWE.Rq
          (params.q securityParameter)
          (params.prefixDimension securityParameter +
            params.suffixDimension securityParameter)))
        (params.scalarErrorSampler securityParameter)
        (params.scalarErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))|

/-- The full adaptive shared-key TFHE advantage equals the reduced ordinary batch-LWE advantage
at every security parameter. -/
theorem securityGame_advantage_eq_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (securityGame params).advantage adversary securityParameter =
      (batchLWESecurityGame params).advantage
        (batchLWEReduction params adversary) securityParameter := by
  exact congrArg ENNReal.ofReal
    (abs_signedAdvantage_real_uniformRingError_eq_batchLwe_of_same_noise
      (adversary.queryCount securityParameter)
      (params.scalarErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)
      (adversary.isQueryBound securityParameter))

/-- **Reusable-key adaptive security from ordinary LWE alone.**

If the exact query-counted batch-LWE game is secure for every reduced efficient family, then the
uniform-BRK shared-randomness TFHE game has negligible advantage.  There is no circular/KDM
security premise. -/
theorem secureAgainst_of_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : PolynomialQueryAdversary params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  rw [show (securityGame params).advantage adversary =
      (batchLWESecurityGame params).advantage
        (batchLWEReduction params adversary) from
    funext (securityGame_advantage_eq_batchLWE params adversary)]
  exact hBatchLWE _ (hBatchLWEClosed adversary hadversary)

/-! ## Near-uniform executable ring errors -/

/-- An executable ring-error family replacing the exact uniform BRK row error. -/
structure RingErrorFamily {Message : Type} (params : Parameters Message) where
  sampler : (securityParameter : ℕ) →
    ProbComp
      (RLWE.Rq
        (params.q securityParameter)
        (params.prefixDimension securityParameter +
          params.suffixDimension securityParameter))

/-- One-draw total-variation distance between an executable ring error and exact uniform. -/
noncomputable def ringErrorGap {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params) (securityParameter : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (tvDist
      (implementation.sampler securityParameter)
      ($ᵗ (RLWE.Rq
        (params.q securityParameter)
        (params.prefixDimension securityParameter +
          params.suffixDimension securityParameter))))

/-- Honest adaptive security game using the executable ring-error family. -/
noncomputable def implementationSecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params) :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter := ENNReal.ofReal
    |Encryption.signedAdvantage
      (realGame
        (adversary.queryCount securityParameter)
        (implementation.sampler securityParameter)
        (params.scalarErrorSampler securityParameter)
        (params.scalarErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))|

/-- Exact statistical replacement charge for all rows of the one self-circular BRK. -/
noncomputable def ringReplacementSecurityGame {Message : Type} (params : Parameters Message)
    (implementation : RingErrorFamily params)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage _ securityParameter :=
    (TFHE.SamplerReplacement.bootstrappingErrorCount
      1
      (params.tgswLevels securityParameter)
      (params.prefixDimension securityParameter) : ℝ≥0∞) *
        ringErrorGap params implementation securityParameter

/-- Pointwise implementation advantage is bounded by ordinary batch LWE plus the exact
one-draw ring-error replacement charge. -/
theorem implementationSecurityGame_advantage_le_batchLWE_add_replacement
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (implementationSecurityGame params implementation).advantage adversary securityParameter ≤
      (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter +
        (ringReplacementSecurityGame params implementation).advantage
          adversary securityParameter := by
  have h := abs_signedAdvantage_real_le_ringErrorDistance_add_batchLwe_of_same_noise
    (adversary.queryCount securityParameter)
    (implementation.sampler securityParameter)
    (params.scalarErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    (params.encode securityParameter)
    (adversary.run securityParameter)
    (adversary.isQueryBound securityParameter)
  have hTV : 0 ≤ tvDist
      (implementation.sampler securityParameter)
      ($ᵗ (RLWE.Rq
        (params.q securityParameter)
        (params.prefixDimension securityParameter +
          params.suffixDimension securityParameter))) :=
    tvDist_nonneg (m := ProbComp) _ _
  have hReplacement : 0 ≤
      (TFHE.SamplerReplacement.bootstrappingErrorCount
          1
          (params.tgswLevels securityParameter)
          (params.prefixDimension securityParameter) : ℝ) *
        tvDist
          (implementation.sampler securityParameter)
          ($ᵗ (RLWE.Rq
            (params.q securityParameter)
            (params.prefixDimension securityParameter +
              params.suffixDimension securityParameter))) :=
    mul_nonneg (Nat.cast_nonneg _) hTV
  have hLWE : 0 ≤ LearningWithErrors.advantage
      (Native.KeySwitchSecurity.binaryLweProblem
        (params.q securityParameter)
        (params.prefixDimension securityParameter)
        (keySwitchSamples
            (params.suffixDimension securityParameter)
            (params.keySwitchLevels securityParameter) +
          adversary.queryCount securityParameter)
        (params.scalarErrorSampler securityParameter))
      (FormalProof4FHE.LWE.TwoBlock.reduction
        (jointLweReduction
          (params.scalarErrorSampler securityParameter)
          (params.scalarErrorSampler securityParameter)
          (params.keySwitchGadget securityParameter)
          (params.encode securityParameter)
          (adversary.run securityParameter))) :=
    FormalProof4FHE.LWE.advantage_nonneg _ _
  have hLift := ENNReal.ofReal_le_ofReal h
  calc
    (implementationSecurityGame params implementation).advantage adversary
        securityParameter ≤
      ENNReal.ofReal
        ((TFHE.SamplerReplacement.bootstrappingErrorCount
            1
            (params.tgswLevels securityParameter)
            (params.prefixDimension securityParameter) : ℝ) *
          tvDist
            (implementation.sampler securityParameter)
            ($ᵗ (RLWE.Rq
              (params.q securityParameter)
              (params.prefixDimension securityParameter +
                params.suffixDimension securityParameter))) +
          LearningWithErrors.advantage
            (Native.KeySwitchSecurity.binaryLweProblem
              (params.q securityParameter)
              (params.prefixDimension securityParameter)
              (keySwitchSamples
                  (params.suffixDimension securityParameter)
                  (params.keySwitchLevels securityParameter) +
                adversary.queryCount securityParameter)
              (params.scalarErrorSampler securityParameter))
            (FormalProof4FHE.LWE.TwoBlock.reduction
              (jointLweReduction
                (params.scalarErrorSampler securityParameter)
                (params.scalarErrorSampler securityParameter)
                (params.keySwitchGadget securityParameter)
                (params.encode securityParameter)
                (adversary.run securityParameter)))) := hLift
    _ = (ringReplacementSecurityGame params implementation).advantage adversary
          securityParameter +
        (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter := by
      rw [ENNReal.ofReal_add hReplacement hLWE,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      simp only [ringReplacementSecurityGame, ringErrorGap, batchLWESecurityGame,
        batchLWEReduction]
    _ = (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter +
        (ringReplacementSecurityGame params implementation).advantage adversary
          securityParameter := add_comm _ _

/-- Polynomial growth witnesses for the dimensions determining the number of BRK rows. -/
structure PolynomialBootstrapGrowth {Message : Type} (params : Parameters Message) where
  prefixDimensionPolynomial : Polynomial ℕ
  tgswLevelsPolynomial : Polynomial ℕ
  prefixDimension_le : ∀ securityParameter,
    params.prefixDimension securityParameter ≤
      prefixDimensionPolynomial.eval securityParameter
  tgswLevels_le : ∀ securityParameter,
    params.tgswLevels securityParameter ≤
      tgswLevelsPolynomial.eval securityParameter

/-- Polynomial upper bound for every ring-error draw in the rank-one BRK. -/
noncomputable def bootstrappingDrawPolynomial
    {Message : Type} {params : Parameters Message}
    (growth : PolynomialBootstrapGrowth params) : Polynomial ℕ :=
  growth.prefixDimensionPolynomial * (2 * growth.tgswLevelsPolynomial)

/-- Exact rank-one BRK row accounting is bounded by the declared polynomial growth. -/
theorem bootstrappingErrorCount_le_polynomial
    {Message : Type} {params : Parameters Message}
    (growth : PolynomialBootstrapGrowth params) (securityParameter : ℕ) :
    TFHE.SamplerReplacement.bootstrappingErrorCount
        1
        (params.tgswLevels securityParameter)
        (params.prefixDimension securityParameter) ≤
      (bootstrappingDrawPolynomial growth).eval securityParameter := by
  simp only [TFHE.SamplerReplacement.bootstrappingErrorCount, TGSW.rowCount,
    bootstrappingDrawPolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat]
  exact Nat.mul_le_mul
    (growth.prefixDimension_le securityParameter)
    (Nat.mul_le_mul le_rfl (growth.tgswLevels_le securityParameter))

/-- Polynomially many BRK rows preserve negligibility of the one-draw distance from uniform. -/
theorem ringReplacementSecurityGame_advantage_negligible
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (growth : PolynomialBootstrapGrowth params)
    (hGap : negligible (ringErrorGap params implementation))
    (adversary : PolynomialQueryAdversary params) :
    negligible
      ((ringReplacementSecurityGame params implementation).advantage adversary) := by
  apply negligible_of_le (g := fun securityParameter ↦
    (((bootstrappingDrawPolynomial growth).eval securityParameter : ℕ) : ℝ≥0∞) *
      ringErrorGap params implementation securityParameter)
  · intro securityParameter
    exact mul_le_mul_of_nonneg_right
      (by
        exact_mod_cast
          bootstrappingErrorCount_le_polynomial growth securityParameter)
      zero_le
  · exact negligible_polynomial_mul hGap (bootstrappingDrawPolynomial growth)

/-- **Near-uniform reusable-key security from ordinary batch LWE.**

If the executable ring error is negligibly close to uniform per draw and the BRK has polynomially
many rows, then ordinary batch-LWE security still implies negligible full adaptive advantage. -/
theorem implementationSecureAgainst_of_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (growth : PolynomialBootstrapGrowth params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT)
    (hGap : negligible (ringErrorGap params implementation)) :
    (implementationSecurityGame params implementation).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (implementationSecurityGame_advantage_le_batchLWE_add_replacement
      params implementation adversary)
    (negligible_add
      (hBatchLWE _ (hBatchLWEClosed adversary hadversary))
      (ringReplacementSecurityGame_advantage_negligible
        params implementation growth hGap adversary))

/-! ## Public homomorphic evaluation -/

/-- A parameter-indexed public evaluator using the shared cloud key. -/
abbrev PublicEvaluatorFamily {Message Output : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :=
  (securityParameter : ℕ) →
    CloudKey
      (params.q securityParameter)
      (params.prefixDimension securityParameter)
      (params.suffixDimension securityParameter)
      (params.tgswLevels securityParameter)
      (params.keySwitchLevels securityParameter) →
    TLWE.Ciphertext
      (ZMod (params.q securityParameter))
      (params.prefixDimension securityParameter) → Output

/-- Polynomial-query adversary observing the result of a public homomorphic evaluator. -/
structure PolynomialQueryEvaluationAdversary {Message Output : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] where
  run : (securityParameter : ℕ) →
    Adaptive.Adversary Message
      (CloudKey
        (params.q securityParameter)
        (params.prefixDimension securityParameter)
        (params.suffixDimension securityParameter)
        (params.tgswLevels securityParameter)
        (params.keySwitchLevels securityParameter)) Output
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  isQueryBound : ∀ securityParameter,
    Adaptive.IsQueryBound (run securityParameter) (queryCount securityParameter)

/-- Compile public evaluation into the base shared-key adaptive adversary family without changing
the encryption-query bound. -/
def compileEvaluationAdversary {Message Output : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (evaluate : PublicEvaluatorFamily (Output := Output) params)
    (adversary : PolynomialQueryEvaluationAdversary (Output := Output) params) :
    PolynomialQueryAdversary params where
  run securityParameter :=
    Adaptive.compilePublicEvaluation
      (evaluate securityParameter) (adversary.run securityParameter)
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  isQueryBound securityParameter := by
    letI : IsUniformSpec
        ((Message × Message) →ₒ
          TLWE.Ciphertext
            (ZMod (params.q securityParameter))
            (params.prefixDimension securityParameter)) :=
      IsUniformSpec.ofFintypeInhabited _
    exact Adaptive.compilePublicEvaluation_isQueryBound
      (evaluate securityParameter) (adversary.run securityParameter)
      (adversary.queryCount securityParameter)
      (adversary.isQueryBound securityParameter)

/-- Security game after arbitrary deterministic public evaluation of each returned ciphertext. -/
noncomputable def evaluationSecurityGame {Message Output : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (evaluate : PublicEvaluatorFamily (Output := Output) params) :
    SecurityGame (PolynomialQueryEvaluationAdversary (Output := Output) params) where
  advantage adversary securityParameter :=
    (securityGame params).advantage
      (compileEvaluationAdversary params evaluate adversary) securityParameter

/-- Public homomorphic evaluation inherits security from the base game with exactly zero
additional cryptographic loss. -/
theorem evaluationSecureAgainst_of_security
    {Message Output : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (evaluate : PublicEvaluatorFamily (Output := Output) params)
    (baseIsPPT : PolynomialQueryAdversary params → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) params → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary params evaluate adversary))
    (hSecurity : (securityGame params).secureAgainst baseIsPPT) :
    (evaluationSecurityGame params evaluate).secureAgainst evaluationIsPPT := by
  intro adversary hadversary
  exact hSecurity _ (hEvaluationClosed adversary hadversary)

/-- Publicly evaluated reusable-key TFHE security follows directly from ordinary batch LWE. -/
theorem evaluationSecureAgainst_of_batchLWE
    {Message Output : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (evaluate : PublicEvaluatorFamily (Output := Output) params)
    (baseIsPPT : PolynomialQueryAdversary params → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary params evaluate adversary))
    (hBatchLWEClosed : ∀ adversary, baseIsPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (evaluationSecurityGame params evaluate).secureAgainst evaluationIsPPT := by
  exact evaluationSecureAgainst_of_security params evaluate baseIsPPT evaluationIsPPT
    hEvaluationClosed
    (secureAgainst_of_batchLWE params baseIsPPT batchLWEIsPPT
      hBatchLWEClosed hBatchLWE)

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle.Asymptotic
