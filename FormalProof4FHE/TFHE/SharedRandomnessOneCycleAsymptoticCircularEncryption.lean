/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessOneCycleAsymptoticEncryption
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleCircularEncryption
import FormalProof4FHE.RLWE.CenteredBinomial
import FormalProof4FHE.TFHE.DiscreteGaussianSampler

/-!
# Asymptotic Narrow-Noise Security for Shared-Randomness One-Cycle TFHE

This module lifts the exact finite one-cycle theorem to negligible-function security.  The BRK
may use any finite executable ring-error family, including narrow centered-binomial or discrete-
Gaussian errors.  Its native self-circular distribution is retained rather than statistically
replaced by a wide uniform error.

The resulting reusable-key adaptive TFHE advantage is bounded pointwise by:

* one auxiliary-input CircLWE advantage for the native rank-one self-circular BRK, retaining the
  real suffix-only KSK; and
* one ordinary binary-secret batch-LWE advantage containing every suffix-KSK row and every
  charged input-encryption row.

Consequently, negligible one-cycle CircLWE and ordinary batch-LWE advantage imply negligible
adaptive TFHE advantage.  The same result survives arbitrary public deterministic FHE evaluation.
This is a conditional theorem for the exact native quadratic object, not a derivation of its
hardness from ordinary LWE or RLWE.
-/

open ENNReal OracleComp OracleSpec

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle.Asymptotic.CircularSecurity

noncomputable section

/-! ## Concrete narrow ring-error families -/

/-- Executable coefficientwise centered-binomial ring errors for the one-cycle BRK. -/
def centeredBinomialRingErrorFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (eta : ℕ → ℕ) : RingErrorFamily params where
  sampler securityParameter :=
    RLWE.CenteredBinomial.sampler
      (params.q securityParameter)
      (params.prefixDimension securityParameter +
        params.suffixDimension securityParameter)
      (eta securityParameter)

/-- Certified finite discrete-Gaussian data at every security parameter. -/
structure DiscreteGaussianRingErrorData {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] where
  alpha : ℕ → ℝ
  alpha_pos : ∀ securityParameter, 0 < alpha securityParameter
  certificate : (securityParameter : ℕ) →
    DiscreteGaussianSampler.ScalarCertificate
      (params.q securityParameter)
      (alpha securityParameter)
      (alpha_pos securityParameter)

/-- Executable coefficientwise certified discrete-Gaussian ring errors for the one-cycle BRK. -/
def discreteGaussianRingErrorFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (data : DiscreteGaussianRingErrorData params) : RingErrorFamily params where
  sampler securityParameter :=
    DiscreteGaussianSampler.ringSampler
      (params.prefixDimension securityParameter +
        params.suffixDimension securityParameter)
      (data.certificate securityParameter)

/-- Security-parameter-indexed secret continuations for the exact one-cycle cloud-key problem. -/
abbrev ContinuationFamily {Message : Type} (params : Parameters Message) :=
  (securityParameter : ℕ) →
    Native.SharedRandomnessOneCycle.SecretContinuation
      (params.q securityParameter)
      (params.prefixDimension securityParameter)
      (params.suffixDimension securityParameter)
      (params.tgswLevels securityParameter)
      (params.keySwitchLevels securityParameter)

/-- Native real-versus-zero one-key KDM game for an arbitrary continuation family. -/
noncomputable def kdmSecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params) :
    SecurityGame (ContinuationFamily params) where
  advantage continuation securityParameter := ENNReal.ofReal
    (Native.SharedRandomnessOneCycle.AuxiliaryInput.kdmAdvantage
      (implementation.sampler securityParameter)
      (params.scalarErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (continuation securityParameter))

/-- Exact native self-circular BRK versus uniform, with the real suffix KSK retained. -/
noncomputable def circularLWESecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params) :
    SecurityGame (ContinuationFamily params) where
  advantage continuation securityParameter := ENNReal.ofReal
    (Native.SharedRandomnessOneCycle.AuxiliaryInput.circularLweAdvantage
      (implementation.sampler securityParameter)
      (params.scalarErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (continuation securityParameter))

/-- Native zero-message BRK versus uniform, retaining the same real suffix KSK. -/
noncomputable def zeroLWESecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params) :
    SecurityGame (ContinuationFamily params) where
  advantage continuation securityParameter := ENNReal.ofReal
    (Native.SharedRandomnessOneCycle.AuxiliaryInput.zeroLweAdvantage
      (implementation.sampler securityParameter)
      (params.scalarErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (continuation securityParameter))

/-- Pointwise one-cycle KDM is bounded by one-cycle CircLWE plus the explicit zero branch. -/
theorem kdmSecurityGame_advantage_le_circularLWE_add_zeroLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (continuation : ContinuationFamily params) (securityParameter : ℕ) :
    (kdmSecurityGame params implementation).advantage continuation securityParameter ≤
      (circularLWESecurityGame params implementation).advantage continuation
          securityParameter +
        (zeroLWESecurityGame params implementation).advantage continuation
          securityParameter := by
  have h :=
    Native.SharedRandomnessOneCycle.AuxiliaryInput.secretContinuationAdvantage_le_circularLwe_add_zeroLwe
      (implementation.sampler securityParameter)
      (params.scalarErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (continuation securityParameter)
  rw [← Native.SharedRandomnessOneCycle.AuxiliaryInput.kdmAdvantage_eq_secretContinuationAdvantage]
    at h
  exact (ENNReal.ofReal_le_ofReal h).trans ENNReal.ofReal_add_le

/-- Conversely, one-cycle CircLWE is bounded by native KDM plus the same zero branch. -/
theorem circularLWESecurityGame_advantage_le_kdm_add_zeroLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (continuation : ContinuationFamily params) (securityParameter : ℕ) :
    (circularLWESecurityGame params implementation).advantage continuation securityParameter ≤
      (kdmSecurityGame params implementation).advantage continuation securityParameter +
        (zeroLWESecurityGame params implementation).advantage continuation
          securityParameter := by
  have h :=
    Native.SharedRandomnessOneCycle.AuxiliaryInput.circularLweAdvantage_le_secretContinuation_add_zeroLwe
      (implementation.sampler securityParameter)
      (params.scalarErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (continuation securityParameter)
  rw [← Native.SharedRandomnessOneCycle.AuxiliaryInput.kdmAdvantage_eq_secretContinuationAdvantage]
    at h
  exact (ENNReal.ofReal_le_ofReal h).trans ENNReal.ofReal_add_le

/-- CircLWE and zero-message security imply native one-cycle KDM security. -/
theorem kdmSecurityGame_secureAgainst_of_circularLWE_and_zeroLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (isPPT : ContinuationFamily params → Prop)
    (hCircular : (circularLWESecurityGame params implementation).secureAgainst isPPT)
    (hZero : (zeroLWESecurityGame params implementation).secureAgainst isPPT) :
    (kdmSecurityGame params implementation).secureAgainst isPPT := by
  intro continuation hcontinuation
  exact negligible_of_le
    (kdmSecurityGame_advantage_le_circularLWE_add_zeroLWE
      params implementation continuation)
    (negligible_add
      (hCircular continuation hcontinuation)
      (hZero continuation hcontinuation))

/-- With the zero branch fixed, one-cycle KDM and one-cycle CircLWE security are equivalent. -/
theorem kdmSecurityGame_secureAgainst_iff_circularLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (isPPT : ContinuationFamily params → Prop)
    (hZero : (zeroLWESecurityGame params implementation).secureAgainst isPPT) :
    (kdmSecurityGame params implementation).secureAgainst isPPT ↔
      (circularLWESecurityGame params implementation).secureAgainst isPPT := by
  constructor
  · intro hKDM continuation hcontinuation
    exact negligible_of_le
      (circularLWESecurityGame_advantage_le_kdm_add_zeroLWE
        params implementation continuation)
      (negligible_add
        (hKDM continuation hcontinuation)
        (hZero continuation hcontinuation))
  · intro hCircular
    exact kdmSecurityGame_secureAgainst_of_circularLWE_and_zeroLWE
      params implementation isPPT hCircular hZero

/-! ## Continuations induced by reusable-key adaptive TFHE adversaries -/

/-- Compile a polynomial-query adaptive TFHE adversary into its exact one-cycle continuation. -/
def continuationReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) : ContinuationFamily params :=
  fun securityParameter ↦
    continuation
      (adversary.queryCount securityParameter)
      (params.scalarErrorSampler securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)

/-- One-cycle auxiliary-input CircLWE restricted to adaptive TFHE continuations. -/
noncomputable def adaptiveCircularLWESecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params) :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter :=
    (circularLWESecurityGame params implementation).advantage
      (continuationReduction params adversary) securityParameter

/-- Native one-cycle KDM restricted to adaptive TFHE continuations. -/
noncomputable def adaptiveKDMSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params) :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter :=
    (kdmSecurityGame params implementation).advantage
      (continuationReduction params adversary) securityParameter

/-- The non-circular zero-message-BRK versus uniform-BRK branch restricted to adaptive TFHE
continuations.  This is kept separate from the literal real-versus-zero one-circular game. -/
noncomputable def adaptiveZeroBootstrapLWESecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params) :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter :=
    (zeroLWESecurityGame params implementation).advantage
      (continuationReduction params adversary) securityParameter

/-- Pointwise narrow-noise adaptive TFHE security from one-cycle CircLWE and ordinary batch
LWE. -/
theorem implementationSecurityGame_advantage_le_circularLWE_add_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (implementationSecurityGame params implementation).advantage adversary
        securityParameter ≤
      (adaptiveCircularLWESecurityGame params implementation).advantage adversary
          securityParameter +
        (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter := by
  have h :=
    FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle.CircularSecurity.abs_signedAdvantage_real_le_circularLwe_add_batchLwe_of_same_noise
      (adversary.queryCount securityParameter)
      (implementation.sampler securityParameter)
      (params.scalarErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)
      (adversary.isQueryBound securityParameter)
  exact (ENNReal.ofReal_le_ofReal h).trans ENNReal.ofReal_add_le

/-- **Pointwise adaptive TFHE security from the literal one-circular KDM game.**

The first term is exactly `BRK_S(prefix(S))` versus `BRK_S(0)`.  The second is the distinct
zero-message encryption branch, and the third is conventional scalar batch LWE.  Thus no
current-to-shifted full-master transport is used as the definition of circular security. -/
theorem implementationSecurityGame_advantage_le_oneCircularKDM_add_zeroBootstrapLWE_add_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (implementationSecurityGame params implementation).advantage adversary
        securityParameter ≤
      ((adaptiveKDMSecurityGame params implementation).advantage adversary
          securityParameter +
        (adaptiveZeroBootstrapLWESecurityGame params implementation).advantage adversary
          securityParameter) +
        (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter := by
  calc
    (implementationSecurityGame params implementation).advantage adversary
        securityParameter ≤
      (adaptiveCircularLWESecurityGame params implementation).advantage adversary
          securityParameter +
        (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter :=
      implementationSecurityGame_advantage_le_circularLWE_add_batchLWE
        params implementation adversary securityParameter
    _ ≤ _ := add_le_add
      (circularLWESecurityGame_advantage_le_kdm_add_zeroLWE
        params implementation (continuationReduction params adversary)
        securityParameter)
      le_rfl

/-- **Asymptotic reusable-key narrow-noise TFHE security.**

If the exact one-cycle auxiliary-input CircLWE game and the reduced ordinary batch-LWE game are
secure for the selected efficient families, the complete adaptive TFHE advantage is negligible. -/
theorem implementationSecureAgainst_of_circularLWE_and_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hCircular :
      (adaptiveCircularLWESecurityGame params implementation).secureAgainst isPPT)
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (implementationSecurityGame params implementation).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (implementationSecurityGame_advantage_le_circularLWE_add_batchLWE
      params implementation adversary)
    (negligible_add
      (hCircular adversary hadversary)
      (hBatchLWE _ (hBatchLWEClosed adversary hadversary)))

/-- **Asymptotic reusable-key TFHE security from actual one-circular KDM.**

Negligible literal `BRK_S(prefix(S))`-versus-`BRK_S(0)` advantage, negligible non-circular
zero-BRK encryption advantage, and ordinary batch-LWE security imply negligible adaptive TFHE
advantage for arbitrary finite narrow ring-noise families. -/
theorem implementationSecureAgainst_of_oneCircularKDM_zeroBootstrapLWE_and_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hOneCircular :
      (adaptiveKDMSecurityGame params implementation).secureAgainst isPPT)
    (hZeroBootstrap :
      (adaptiveZeroBootstrapLWESecurityGame params implementation).secureAgainst isPPT)
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (implementationSecurityGame params implementation).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (implementationSecurityGame_advantage_le_oneCircularKDM_add_zeroBootstrapLWE_add_batchLWE
      params implementation adversary)
    (negligible_add
      (negligible_add
        (hOneCircular adversary hadversary)
        (hZeroBootstrap adversary hadversary))
      (hBatchLWE _ (hBatchLWEClosed adversary hadversary)))

/-! ## Public deterministic FHE evaluation -/

/-- Narrow-noise security game after public deterministic evaluation of returned ciphertexts. -/
noncomputable def implementationEvaluationSecurityGame {Message Output : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (evaluate : PublicEvaluatorFamily (Output := Output) params) :
    SecurityGame (PolynomialQueryEvaluationAdversary (Output := Output) params) where
  advantage adversary securityParameter :=
    (implementationSecurityGame params implementation).advantage
      (compileEvaluationAdversary params evaluate adversary) securityParameter

/-- Public deterministic evaluation adds no security loss to the narrow-noise base theorem. -/
theorem implementationEvaluationSecureAgainst_of_security
    {Message Output : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (evaluate : PublicEvaluatorFamily (Output := Output) params)
    (baseIsPPT : PolynomialQueryAdversary params → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) params → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary params evaluate adversary))
    (hSecurity :
      (implementationSecurityGame params implementation).secureAgainst baseIsPPT) :
    (implementationEvaluationSecurityGame params implementation evaluate).secureAgainst
      evaluationIsPPT := by
  intro adversary hadversary
  exact hSecurity _ (hEvaluationClosed adversary hadversary)

/-- Publicly evaluated narrow-noise TFHE security from one-cycle CircLWE and ordinary batch
LWE. -/
theorem implementationEvaluationSecureAgainst_of_circularLWE_and_batchLWE
    {Message Output : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (evaluate : PublicEvaluatorFamily (Output := Output) params)
    (baseIsPPT : PolynomialQueryAdversary params → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary params evaluate adversary))
    (hBatchLWEClosed : ∀ adversary, baseIsPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hCircular :
      (adaptiveCircularLWESecurityGame params implementation).secureAgainst baseIsPPT)
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (implementationEvaluationSecurityGame params implementation evaluate).secureAgainst
      evaluationIsPPT := by
  exact implementationEvaluationSecureAgainst_of_security
    params implementation evaluate baseIsPPT evaluationIsPPT hEvaluationClosed
    (implementationSecureAgainst_of_circularLWE_and_batchLWE
      params implementation baseIsPPT batchLWEIsPPT hBatchLWEClosed
      hCircular hBatchLWE)

/-- Public deterministic FHE evaluation preserves the literal one-circular KDM security
endpoint and adds no further assumption or loss. -/
theorem implementationEvaluationSecureAgainst_of_oneCircularKDM_zeroBootstrapLWE_and_batchLWE
    {Message Output : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (evaluate : PublicEvaluatorFamily (Output := Output) params)
    (baseIsPPT : PolynomialQueryAdversary params → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary params evaluate adversary))
    (hBatchLWEClosed : ∀ adversary, baseIsPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hOneCircular :
      (adaptiveKDMSecurityGame params implementation).secureAgainst baseIsPPT)
    (hZeroBootstrap :
      (adaptiveZeroBootstrapLWESecurityGame params implementation).secureAgainst baseIsPPT)
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (implementationEvaluationSecurityGame params implementation evaluate).secureAgainst
      evaluationIsPPT := by
  exact implementationEvaluationSecureAgainst_of_security
    params implementation evaluate baseIsPPT evaluationIsPPT hEvaluationClosed
    (implementationSecureAgainst_of_oneCircularKDM_zeroBootstrapLWE_and_batchLWE
      params implementation baseIsPPT batchLWEIsPPT hBatchLWEClosed
      hOneCircular hZeroBootstrap hBatchLWE)

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle.Asymptotic.CircularSecurity
