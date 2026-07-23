/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AsymptoticCutCycleSecurity
import FormalProof4FHE.TFHE.AsymptoticSamplerReplacement

/-!
# Sampler Replacement for the Asymptotic TFHE Cut-Cycle Proof

This module connects the KSK-first cut-cycle theorem to executable implementation samplers.  The
reference family supplies the exact native intact-cycle KDM and post-cut LWE problems; the
implementation family may use different ring, KSK, and adaptive-input error samplers.  Their
complete finite total-variation replacement cost is paid once and is negligible whenever the
three one-draw gaps are negligible and all native draw counts grow polynomially.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.CutCycleSamplerReplacement

/-! ## Pointwise implementation bounds -/

/-- The implementation advantage is bounded by the four reference KSK-first cut-cycle terms plus
the exact complete sampler-replacement loss. -/
theorem
    implementationSecurityGame_advantage_le_keySwitchFirst_add_two_ringBatchLWE_add_jointLWE_add_replacement
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (implementationSecurityGame params implementation).advantage adversary securityParameter ≤
      (CutCycleSecurity.keySwitchFirstSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (CutCycleSecurity.realRingBatchReduction params adversary) securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (CutCycleSecurity.zeroRingBatchReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (CutCycleSecurity.zeroCloudJointLWEReduction params adversary) securityParameter +
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
      ((CutCycleSecurity.keySwitchFirstSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (CutCycleSecurity.realRingBatchReduction params adversary) securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (CutCycleSecurity.zeroRingBatchReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (CutCycleSecurity.zeroCloudJointLWEReduction params adversary) securityParameter) +
        (replacementSecurityGame params implementation).advantage
          adversary securityParameter :=
      add_le_add
        (CutCycleSecurity.securityGame_advantage_le_keySwitchFirst_add_two_ringBatchLWE_add_jointLWE
          params adversary securityParameter)
        le_rfl

/-- Equal reference scalar noises replace the joint endpoint above by one ordinary scalar
batch-LWE term; implementation scalar samplers may still differ negligibly from the reference. -/
theorem
    implementationSecurityGame_advantage_le_keySwitchFirst_add_two_ringBatchLWE_add_batchLWE_add_replacement
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (hEqualReferenceNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (implementationSecurityGame params implementation).advantage adversary securityParameter ≤
      (CutCycleSecurity.keySwitchFirstSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (CutCycleSecurity.realRingBatchReduction params adversary) securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (CutCycleSecurity.zeroRingBatchReduction params adversary) securityParameter +
        (batchLWESecurityGame params).advantage
          (CutCycleSecurity.zeroCloudBatchLWEReduction params adversary) securityParameter +
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
      ((CutCycleSecurity.keySwitchFirstSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (CutCycleSecurity.realRingBatchReduction params adversary) securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (CutCycleSecurity.zeroRingBatchReduction params adversary) securityParameter +
        (batchLWESecurityGame params).advantage
          (CutCycleSecurity.zeroCloudBatchLWEReduction params adversary) securityParameter) +
        (replacementSecurityGame params implementation).advantage
          adversary securityParameter :=
      add_le_add
        (CutCycleSecurity.securityGame_advantage_le_keySwitchFirst_add_two_ringBatchLWE_add_batchLWE
          params hEqualReferenceNoise adversary securityParameter)
        le_rfl

/-! ## Negligible implementation security -/

/-- **Implementation-level KSK-first TFHE security with distinct reference scalar noises.**
Negligible native intact-cycle KDM, both post-cut ring batch-LWE games, the zero-cloud joint-LWE
game, and the three one-draw implementation/reference sampler gaps imply negligible honest
adaptive implementation advantage. -/
theorem
    implementationSecurityGame_secureAgainst_of_keySwitchFirst_and_two_ringBatchLWE_and_jointLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (growth : PolynomialEvaluationKeyGrowth params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (continuationIsPPT : ContinuationFamily params → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      CutCycleSecurity.RingBatchLWEAdversaryFamily params → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily params → Prop)
    (hContinuationClosed : ∀ adversary, isPPT adversary →
      continuationIsPPT (continuationReduction params adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (CutCycleSecurity.realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (CutCycleSecurity.zeroRingBatchReduction params adversary))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (CutCycleSecurity.zeroCloudJointLWEReduction params adversary))
    (hCircular :
      (CutCycleSecurity.keySwitchFirstSecurityGame params).secureAgainst continuationIsPPT)
    (hRealRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hJointLWE : (jointLWESecurityGame params).secureAgainst jointLWEIsPPT)
    (hRing : negligible (ringSamplerGap params implementation))
    (hKeySwitch : negligible (keySwitchSamplerGap params implementation))
    (hInput : negligible (inputSamplerGap params implementation)) :
    (implementationSecurityGame params implementation).secureAgainst isPPT := by
  exact implementationSecurityGame_secureAgainst_of_reference
    params implementation growth isPPT
    (CutCycleSecurity.secureAgainst_of_keySwitchFirst_and_two_ringBatchLWE_and_jointLWE
      params isPPT continuationIsPPT realRingBatchIsPPT zeroRingBatchIsPPT jointLWEIsPPT
      hContinuationClosed hRealRingBatchClosed hZeroRingBatchClosed hJointLWEClosed
      hCircular hRealRingBatch hZeroRingBatch hJointLWE)
    hRing hKeySwitch hInput

/-- **Equal-reference-noise implementation theorem.** The only nonstandard computational
premise is native KSK-first intact-cycle KDM; every other reference computational premise is an
ordinary binary-secret batch-LWE game, and the implementation/reference sampler loss is
negligible. -/
theorem implementationSecurityGame_secureAgainst_of_keySwitchFirst_and_three_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : ErrorSamplerFamily params)
    (growth : PolynomialEvaluationKeyGrowth params)
    (hEqualReferenceNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (continuationIsPPT : ContinuationFamily params → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      CutCycleSecurity.RingBatchLWEAdversaryFamily params → Prop)
    (scalarBatchIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hContinuationClosed : ∀ adversary, isPPT adversary →
      continuationIsPPT (continuationReduction params adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (CutCycleSecurity.realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (CutCycleSecurity.zeroRingBatchReduction params adversary))
    (hScalarBatchClosed : ∀ adversary, isPPT adversary →
      scalarBatchIsPPT (CutCycleSecurity.zeroCloudBatchLWEReduction params adversary))
    (hCircular :
      (CutCycleSecurity.keySwitchFirstSecurityGame params).secureAgainst continuationIsPPT)
    (hRealRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hScalarBatch : (batchLWESecurityGame params).secureAgainst scalarBatchIsPPT)
    (hRing : negligible (ringSamplerGap params implementation))
    (hKeySwitch : negligible (keySwitchSamplerGap params implementation))
    (hInput : negligible (inputSamplerGap params implementation)) :
    (implementationSecurityGame params implementation).secureAgainst isPPT := by
  exact implementationSecurityGame_secureAgainst_of_reference
    params implementation growth isPPT
    (CutCycleSecurity.secureAgainst_of_keySwitchFirst_and_three_batchLWE
      params hEqualReferenceNoise isPPT continuationIsPPT realRingBatchIsPPT
      zeroRingBatchIsPPT scalarBatchIsPPT hContinuationClosed hRealRingBatchClosed
      hZeroRingBatchClosed hScalarBatchClosed hCircular hRealRingBatch hZeroRingBatch
      hScalarBatch)
    hRing hKeySwitch hInput

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.CutCycleSamplerReplacement
