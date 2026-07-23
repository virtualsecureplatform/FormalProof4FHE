/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.MonomialKDM
import FormalProof4FHE.TFHE.AsymptoticCutCycleSecurity

/-!
# Asymptotic Degree-Two Monomial KDM for Native TFHE

`TFHE.MonomialKDM` proves that the normalized native TFHE bootstrapping-key phase is non-affine in
the two native key coordinates but becomes linear after adding their degree-two cross monomials.
It also proves exact equality of that presentation with the finite direct-bilinear intact-cycle
game.

This file lifts the equality pointwise to the asymptotic framework.  It records both the generic
continuation game and the game induced by polynomial-query sequential TFHE adversaries.  Under the
already-checked post-cut LWE premises, the latter is also equivalent to the KSK-first intact-cycle
assumption.

These equivalences classify the precise KDM function family needed by native TFHE.  They do not
identify it with the security theorem of a construction whose secret key was changed to contain
monomials.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.MonomialKDM

/-- Security game for the exact degree-two monomial presentation of the native intact-cycle
distribution. -/
noncomputable def securityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (ContinuationFamily params) where
  advantage continuation securityParameter := ENNReal.ofReal
    (Native.BootstrapSecurity.MonomialKDM.advantage
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (continuation securityParameter))

/-- Pointwise equality between the monomial-KDM and direct-bilinear security games. -/
theorem securityGame_advantage_eq_directBilinear
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (continuation : ContinuationFamily params) (securityParameter : ℕ) :
    (securityGame params).advantage continuation securityParameter =
      (directBilinearSecurityGame params).advantage continuation securityParameter := by
  change ENNReal.ofReal
      (Native.BootstrapSecurity.MonomialKDM.advantage
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (continuation securityParameter)) =
    ENNReal.ofReal
      (Native.BootstrapSecurity.directBilinearAdvantage
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (continuation securityParameter))
  rw [Native.BootstrapSecurity.MonomialKDM.advantage_eq_directBilinear]

/-- For any selected continuation class, asymptotic monomial-KDM security is exactly equivalent
to the existing native direct-bilinear circular/KDM assumption. -/
theorem securityGame_secureAgainst_iff_directBilinear
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : ContinuationFamily params → Prop) :
    (securityGame params).secureAgainst isPPT ↔
      (directBilinearSecurityGame params).secureAgainst isPPT := by
  constructor
  · intro h continuation hcontinuation
    have heq :
        (securityGame params).advantage continuation =
          (directBilinearSecurityGame params).advantage continuation := by
      funext securityParameter
      exact securityGame_advantage_eq_directBilinear
        params continuation securityParameter
    rw [← heq]
    exact h continuation hcontinuation
  · intro h continuation hcontinuation
    have heq :
        (securityGame params).advantage continuation =
          (directBilinearSecurityGame params).advantage continuation := by
      funext securityParameter
      exact securityGame_advantage_eq_directBilinear
        params continuation securityParameter
    rw [heq]
    exact h continuation hcontinuation

/-- Degree-two monomial-KDM game restricted to continuations induced by polynomial-query
sequential TFHE adversaries. -/
noncomputable def adaptiveSecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter :=
    (securityGame params).advantage
      (continuationReduction params adversary) securityParameter

/-- The induced adaptive monomial game and the induced adaptive direct-bilinear game have equal
advantage at every security parameter. -/
theorem adaptiveSecurityGame_advantage_eq_directBilinear
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (adaptiveSecurityGame params).advantage adversary securityParameter =
      (CutCycleSecurity.adaptiveDirectBilinearSecurityGame params).advantage
        adversary securityParameter := by
  change (securityGame params).advantage
      (continuationReduction params adversary) securityParameter =
    (directBilinearSecurityGame params).advantage
      (continuationReduction params adversary) securityParameter
  exact securityGame_advantage_eq_directBilinear
    params (continuationReduction params adversary) securityParameter

/-- Exact asymptotic equivalence for polynomial-query adaptive TFHE adversaries. -/
theorem adaptiveSecurityGame_secureAgainst_iff_directBilinear
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : PolynomialQueryAdversary params → Prop) :
    (adaptiveSecurityGame params).secureAgainst isPPT ↔
      (CutCycleSecurity.adaptiveDirectBilinearSecurityGame params).secureAgainst isPPT := by
  constructor
  · intro h adversary hadversary
    have heq :
        (adaptiveSecurityGame params).advantage adversary =
          (CutCycleSecurity.adaptiveDirectBilinearSecurityGame params).advantage adversary := by
      funext securityParameter
      exact adaptiveSecurityGame_advantage_eq_directBilinear
        params adversary securityParameter
    rw [← heq]
    exact h adversary hadversary
  · intro h adversary hadversary
    have heq :
        (adaptiveSecurityGame params).advantage adversary =
          (CutCycleSecurity.adaptiveDirectBilinearSecurityGame params).advantage adversary := by
      funext securityParameter
      exact adaptiveSecurityGame_advantage_eq_directBilinear
        params adversary securityParameter
    rw [heq]
    exact h adversary hadversary

/-- Under security of all four checked post-cut LWE reductions, the exact degree-two monomial-KDM
presentation is equivalent to the KSK-first native intact-cycle assumption for polynomial-query
adaptive TFHE adversaries. -/
theorem adaptiveSecurityGame_secureAgainst_iff_keySwitchFirst
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : PolynomialQueryAdversary params → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      CutCycleSecurity.RingBatchLWEAdversaryFamily params → Prop)
    (nativeJointLWEIsPPT zeroJointLWEIsPPT : JointLWEAdversaryFamily params → Prop)
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (CutCycleSecurity.realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (CutCycleSecurity.zeroRingBatchReduction params adversary))
    (hNativeJointLWEClosed : ∀ adversary, isPPT adversary →
      nativeJointLWEIsPPT (jointLWEReduction params adversary))
    (hZeroJointLWEClosed : ∀ adversary, isPPT adversary →
      zeroJointLWEIsPPT (CutCycleSecurity.zeroCloudJointLWEReduction params adversary))
    (hRealRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hNativeJointLWE : (jointLWESecurityGame params).secureAgainst nativeJointLWEIsPPT)
    (hZeroJointLWE : (jointLWESecurityGame params).secureAgainst zeroJointLWEIsPPT) :
    (adaptiveSecurityGame params).secureAgainst isPPT ↔
      (CutCycleSecurity.adaptiveKeySwitchFirstSecurityGame params).secureAgainst isPPT := by
  exact (adaptiveSecurityGame_secureAgainst_iff_directBilinear params isPPT).trans
    (CutCycleSecurity.adaptiveFirstHop_secureAgainst_iff
      params isPPT realRingBatchIsPPT zeroRingBatchIsPPT nativeJointLWEIsPPT
      zeroJointLWEIsPPT hRealRingBatchClosed hZeroRingBatchClosed hNativeJointLWEClosed
      hZeroJointLWEClosed hRealRingBatch hZeroRingBatch hNativeJointLWE hZeroJointLWE).symm

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.MonomialKDM
