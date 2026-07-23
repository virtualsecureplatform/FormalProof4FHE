/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AsymptoticMonomialKDM
import FormalProof4FHE.TFHE.AsymptoticSamplerReplacement

/-!
# Asymptotic Implementation Security from Native Monomial KDM

This module is the final asymptotic composition for the BRK-first proof.  It replaces the opaque
`directBilinearSecurityGame` name by the exact degree-two monomial-KDM game already proved equal
to the native normalized TFHE bootstrapping-key distribution.

For polynomial-query adaptive adversaries, negligible advantage in that fixed-hint monomial-KDM
game, ordinary LWE (or the heterogeneous joint-LWE form), and negligible certified sampler gaps
imply negligible advantage in the implementation-level TFHE game.  The monomial-KDM premise is
the native circular-security assumption; no reduction from ordinary LWE is claimed.
-/

open ENNReal

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.MonomialSamplerReplacement

/-- Pointwise implementation bound with the exact native degree-two monomial-KDM and
heterogeneous joint-LWE terms exposed. -/
theorem implementationSecurityGame_advantage_le_monomialKDM_add_jointLWE_add_replacement
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (implementationSecurityGame params implementation).advantage adversary securityParameter ≤
      (MonomialKDM.adaptiveSecurityGame params).advantage adversary securityParameter +
        (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter +
        (replacementSecurityGame params implementation).advantage
          adversary securityParameter := by
  calc
    (implementationSecurityGame params implementation).advantage adversary
        securityParameter ≤
      (directBilinearSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter +
        (replacementSecurityGame params implementation).advantage
          adversary securityParameter :=
      implementationSecurityGame_advantage_le_directBilinear_add_jointLWE_add_replacement
        params implementation adversary securityParameter
    _ = (MonomialKDM.adaptiveSecurityGame params).advantage adversary securityParameter +
        (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter +
        (replacementSecurityGame params implementation).advantage
          adversary securityParameter := by
      rw [MonomialKDM.adaptiveSecurityGame_advantage_eq_directBilinear]
      rfl

/-- Pointwise equal-reference-noise specialization using one conventional query-counted
binary-secret batch-LWE problem. -/
theorem implementationSecurityGame_advantage_le_monomialKDM_add_batchLWE_add_replacement
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (hEqualReferenceNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (implementationSecurityGame params implementation).advantage adversary securityParameter ≤
      (MonomialKDM.adaptiveSecurityGame params).advantage adversary securityParameter +
        (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter +
        (replacementSecurityGame params implementation).advantage
          adversary securityParameter := by
  calc
    (implementationSecurityGame params implementation).advantage adversary
        securityParameter ≤
      (directBilinearSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter +
        (replacementSecurityGame params implementation).advantage
          adversary securityParameter :=
      implementationSecurityGame_advantage_le_directBilinear_add_batchLWE_add_replacement
        params implementation hEqualReferenceNoise adversary securityParameter
    _ = (MonomialKDM.adaptiveSecurityGame params).advantage adversary securityParameter +
        (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter +
        (replacementSecurityGame params implementation).advantage
          adversary securityParameter := by
      rw [MonomialKDM.adaptiveSecurityGame_advantage_eq_directBilinear]
      rfl

/-- **Adaptive implementation TFHE security from native degree-two monomial KDM and joint LWE.**

Using the induced adaptive monomial game removes a redundant continuation-efficiency closure
obligation: its adversary is already routed through the exact native continuation reduction. -/
theorem implementationSecurityGame_secureAgainst_of_monomialKDM_and_jointLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (growth : PolynomialEvaluationKeyGrowth params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily params → Prop)
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction params adversary))
    (hMonomialKDM : (MonomialKDM.adaptiveSecurityGame params).secureAgainst isPPT)
    (hJointLWE : (jointLWESecurityGame params).secureAgainst jointLWEIsPPT)
    (hRing : negligible (ringSamplerGap params implementation))
    (hKeySwitch : negligible (keySwitchSamplerGap params implementation))
    (hInput : negligible (inputSamplerGap params implementation)) :
    (implementationSecurityGame params implementation).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (implementationSecurityGame_advantage_le_monomialKDM_add_jointLWE_add_replacement
      params implementation adversary)
    (negligible_add
      (negligible_add
        (hMonomialKDM adversary hadversary)
        (hJointLWE (jointLWEReduction params adversary)
          (hJointLWEClosed adversary hadversary)))
      (replacementSecurityGame_advantage_negligible
        params implementation growth hRing hKeySwitch hInput adversary))

/-- **Adaptive implementation TFHE security from native degree-two monomial KDM and ordinary
batch LWE.**

This is the compact paper-facing theorem when the reference KSK and input errors coincide.  The
implementation samplers may differ, provided each one-draw gap is negligible. -/
theorem implementationSecurityGame_secureAgainst_of_monomialKDM_and_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (growth : PolynomialEvaluationKeyGrowth params)
    (hEqualReferenceNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hMonomialKDM : (MonomialKDM.adaptiveSecurityGame params).secureAgainst isPPT)
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT)
    (hRing : negligible (ringSamplerGap params implementation))
    (hKeySwitch : negligible (keySwitchSamplerGap params implementation))
    (hInput : negligible (inputSamplerGap params implementation)) :
    (implementationSecurityGame params implementation).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (implementationSecurityGame_advantage_le_monomialKDM_add_batchLWE_add_replacement
      params implementation hEqualReferenceNoise adversary)
    (negligible_add
      (negligible_add
        (hMonomialKDM adversary hadversary)
        (hBatchLWE (batchLWEReduction params adversary)
          (hBatchLWEClosed adversary hadversary)))
      (replacementSecurityGame_advantage_negligible
        params implementation growth hRing hKeySwitch hInput adversary))

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.MonomialSamplerReplacement
