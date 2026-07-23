/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveCutCycleSecurity
import FormalProof4FHE.TFHE.AsymptoticSecurity

/-!
# Asymptotic Adaptive TFHE Security after Cutting the Evaluation-Key Cycle

This file lifts the alternative KSK-first finite reduction to security-parameter-indexed
adversary families.  The honest adaptive TFHE advantage is bounded by four games:

1. the explicitly named native intact-cycle KSK-first game;
2. an ordinary binary-secret ring batch-LWE game for the real BRK messages;
3. the same ordinary ring batch-LWE game for the zero BRK messages; and
4. the exact query-counted shared-secret joint-LWE endpoint.

Thus negligibility of those games implies negligible adaptive TFHE advantage.  The native
circular/KDM premise is neither hidden nor identified with a theorem for a modified encryption
scheme.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.CutCycleSecurity

/-! ## Security games and pointwise reductions -/

/-- The security game for the exact native KSK-first intact-cycle hop. -/
noncomputable def keySwitchFirstSecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (ContinuationFamily params) where
  advantage continuation securityParameter := ENNReal.ofReal
    (Circular.continuationKeySwitchFirstReplacementAdvantage
      (Native.nativeCycleSpec
        (params.q securityParameter)
        (params.degree securityParameter)
        (params.ringRank securityParameter)
        (params.tgswLevels securityParameter)
        (params.lweDimension securityParameter)
        (params.keySwitchLevels securityParameter)
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter))
      (continuation securityParameter))

/-- The KSK-first intact-cycle game restricted to continuations induced by polynomial-query
adaptive TFHE adversaries. -/
noncomputable def adaptiveKeySwitchFirstSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter :=
    (keySwitchFirstSecurityGame params).advantage
      (continuationReduction params adversary) securityParameter

/-- The BRK-first direct-bilinear game restricted to the same adaptive continuation family. -/
noncomputable def adaptiveDirectBilinearSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter :=
    (directBilinearSecurityGame params).advantage
      (continuationReduction params adversary) securityParameter

/-- The conventional binary-secret ring batch-LWE adversary type at one parameter. -/
abbrev RingBatchLWEAdversaryAt {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] (securityParameter : ℕ) :=
  LearningWithErrors.Adversary
    (Native.BootstrapCutSecurity.batchModuleLweProblem
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.tgswLevels securityParameter)
      (params.lweDimension securityParameter)
      (params.ringErrorSampler securityParameter))

/-- A parameter-indexed family of attacks on the post-cut ring batch-LWE problem. -/
abbrev RingBatchLWEAdversaryFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :=
  (securityParameter : ℕ) → RingBatchLWEAdversaryAt params securityParameter

/-- The exact ordinary ring batch-LWE security game used by both post-cut reductions. -/
noncomputable def ringBatchLWESecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (RingBatchLWEAdversaryFamily params) where
  advantage adversary securityParameter := ENNReal.ofReal
    (LearningWithErrors.advantage
      (Native.BootstrapCutSecurity.batchModuleLweProblem
        (params.q securityParameter)
        (params.degree securityParameter)
        (params.ringRank securityParameter)
        (params.tgswLevels securityParameter)
        (params.lweDimension securityParameter)
        (params.ringErrorSampler securityParameter))
      (adversary securityParameter))

/-! ## Rank-one post-cut game in explicit RLWE vocabulary -/

/-- The adversary type for finite binary-secret rank-one RLWE at one security parameter. -/
abbrev BinarySecretRLWEAdversaryAt {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] (securityParameter : ℕ) :=
  LearningWithErrors.Adversary
    (Native.BootstrapCutSecurity.binarySecretRLWEProblem
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.lweDimension securityParameter *
        TGSW.rowCount 1 (params.tgswLevels securityParameter))
      (params.ringErrorSampler securityParameter))

/-- Parameter-indexed attacks on binary-secret rank-one RLWE with exactly the number of rows
used by the native post-cut BRK batch. -/
abbrev BinarySecretRLWEAdversaryFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :=
  (securityParameter : ℕ) → BinarySecretRLWEAdversaryAt params securityParameter

/-- The exact binary-secret decisional-RLWE game matching a rank-one native post-cut BRK.
Unlike `RLWE.uniformSecretProblem`, its ring secret has independently uniform Boolean
coefficients. -/
noncomputable def binarySecretRLWESecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (BinarySecretRLWEAdversaryFamily params) where
  advantage adversary securityParameter := ENNReal.ofReal
    (LearningWithErrors.advantage
      (Native.BootstrapCutSecurity.binarySecretRLWEProblem
        (params.q securityParameter)
        (params.degree securityParameter)
        (params.lweDimension securityParameter *
          TGSW.rowCount 1 (params.tgswLevels securityParameter))
        (params.ringErrorSampler securityParameter))
      (adversary securityParameter))

/-- The real-message post-cut ring batch-LWE reduction at every security parameter. -/
noncomputable def realRingBatchReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) : RingBatchLWEAdversaryFamily params :=
  fun securityParameter ↦
    Native.BootstrapCutSecurity.realBatchReduction
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (Adaptive.CutCycleSecurity.cutContinuation
        (adversary.queryCount securityParameter)
        (params.inputErrorSampler securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))

/-- The zero-message post-cut ring batch-LWE reduction at every security parameter. -/
noncomputable def zeroRingBatchReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) : RingBatchLWEAdversaryFamily params :=
  fun securityParameter ↦
    Native.BootstrapCutSecurity.zeroBatchReduction
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (Adaptive.CutCycleSecurity.cutContinuation
        (adversary.queryCount securityParameter)
        (params.inputErrorSampler securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))

/-- The query-counted joint-LWE reduction for the all-zero cloud endpoint. -/
noncomputable def zeroCloudJointLWEReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) : JointLWEAdversaryFamily params where
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  run securityParameter :=
    Adaptive.zeroCloudReduction
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)

/-- Equal-noise flattening of the zero-cloud endpoint to one ordinary scalar batch-LWE
adversary family. -/
noncomputable def zeroCloudBatchLWEReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) : BatchLWEAdversaryFamily params where
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  run securityParameter :=
    FormalProof4FHE.LWE.TwoBlock.reduction
      (Adaptive.zeroCloudReduction
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))

/-! ## Pointwise and negligible-advantage theorems -/

private theorem ofReal_add_four (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ENNReal.ofReal (a + b + c + d) =
      ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d := by
  rw [ENNReal.ofReal_add (add_nonneg (add_nonneg ha hb) hc) hd,
    ENNReal.ofReal_add (add_nonneg ha hb) hc,
    ENNReal.ofReal_add ha hb]

private theorem ofReal_add_five_le (a b c d e : ℝ) :
    ENNReal.ofReal (a + b + c + d + e) ≤
      ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c +
        ENNReal.ofReal d + ENNReal.ofReal e := by
  calc
    ENNReal.ofReal (a + b + c + d + e) ≤
        ENNReal.ofReal (a + b + c + d) + ENNReal.ofReal e := ENNReal.ofReal_add_le
    _ ≤ (ENNReal.ofReal (a + b + c) + ENNReal.ofReal d) +
        ENNReal.ofReal e := add_le_add ENNReal.ofReal_add_le le_rfl
    _ ≤ ((ENNReal.ofReal (a + b) + ENNReal.ofReal c) + ENNReal.ofReal d) +
        ENNReal.ofReal e := add_le_add (add_le_add ENNReal.ofReal_add_le le_rfl) le_rfl
    _ ≤ (((ENNReal.ofReal a + ENNReal.ofReal b) + ENNReal.ofReal c) +
        ENNReal.ofReal d) + ENNReal.ofReal e :=
      add_le_add (add_le_add (add_le_add ENNReal.ofReal_add_le le_rfl) le_rfl) le_rfl

/-- The finite alternative-order theorem lifted pointwise to `ℝ≥0∞`. -/
theorem securityGame_advantage_le_keySwitchFirst_add_two_ringBatchLWE_add_jointLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (securityGame params).advantage adversary securityParameter ≤
      (keySwitchFirstSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (ringBatchLWESecurityGame params).advantage
          (realRingBatchReduction params adversary) securityParameter +
        (ringBatchLWESecurityGame params).advantage
          (zeroRingBatchReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (zeroCloudJointLWEReduction params adversary) securityParameter := by
  have h :=
    Adaptive.CutCycleSecurity.abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_jointLwe
      (adversary.queryCount securityParameter)
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)
      (adversary.isQueryBound securityParameter)
  rw [Adaptive.CutCycleSecurity.keySwitchFirstReplacementAdvantage_eq_abstract] at h
  have hCircularNonneg : 0 ≤
      Circular.continuationKeySwitchFirstReplacementAdvantage
        (Native.nativeCycleSpec
          (params.q securityParameter)
          (params.degree securityParameter)
          (params.ringRank securityParameter)
          (params.tgswLevels securityParameter)
          (params.lweDimension securityParameter)
          (params.keySwitchLevels securityParameter)
          (params.ringErrorSampler securityParameter)
          (params.keySwitchErrorSampler securityParameter)
          (params.tgswGadget securityParameter)
          (params.keySwitchGadget securityParameter))
        (Adaptive.continuation
          (adversary.queryCount securityParameter)
          (params.inputErrorSampler securityParameter)
          (params.encode securityParameter)
          (adversary.run securityParameter)) := by
    unfold Circular.continuationKeySwitchFirstReplacementAdvantage
      ProbComp.boolDistAdvantage
    exact abs_nonneg _
  have hRealNonneg : 0 ≤
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          (params.q securityParameter)
          (params.degree securityParameter)
          (params.ringRank securityParameter)
          (params.tgswLevels securityParameter)
          (params.lweDimension securityParameter)
          (params.ringErrorSampler securityParameter))
        (Native.BootstrapCutSecurity.realBatchReduction
          (params.ringErrorSampler securityParameter)
          (params.keySwitchErrorSampler securityParameter)
          (params.tgswGadget securityParameter)
          (Adaptive.CutCycleSecurity.cutContinuation
            (adversary.queryCount securityParameter)
            (params.inputErrorSampler securityParameter)
            (params.encode securityParameter)
            (adversary.run securityParameter))) :=
    FormalProof4FHE.LWE.advantage_nonneg _ _
  have hZeroNonneg : 0 ≤
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          (params.q securityParameter)
          (params.degree securityParameter)
          (params.ringRank securityParameter)
          (params.tgswLevels securityParameter)
          (params.lweDimension securityParameter)
          (params.ringErrorSampler securityParameter))
        (Native.BootstrapCutSecurity.zeroBatchReduction
          (params.ringErrorSampler securityParameter)
          (params.keySwitchErrorSampler securityParameter)
          (Adaptive.CutCycleSecurity.cutContinuation
            (adversary.queryCount securityParameter)
            (params.inputErrorSampler securityParameter)
            (params.encode securityParameter)
            (adversary.run securityParameter))) :=
    FormalProof4FHE.LWE.advantage_nonneg _ _
  have hJointNonneg : 0 ≤
      LearningWithErrors.advantage
        (Adaptive.jointLweProblem
          (params.q securityParameter)
          (params.lweDimension securityParameter)
          (Encryption.Security.keySwitchSamples
            (params.ringRank securityParameter)
            (params.degree securityParameter)
            (params.keySwitchLevels securityParameter))
          (adversary.queryCount securityParameter)
          (params.keySwitchErrorSampler securityParameter)
          (params.inputErrorSampler securityParameter))
        (Adaptive.zeroCloudReduction
          (params.ringErrorSampler securityParameter)
          (params.keySwitchErrorSampler securityParameter)
          (params.inputErrorSampler securityParameter)
          (params.tgswGadget securityParameter)
          (params.encode securityParameter)
          (adversary.run securityParameter)) :=
    FormalProof4FHE.LWE.advantage_nonneg _ _
  have hLift := ENNReal.ofReal_le_ofReal h
  have hSum : ENNReal.ofReal
      (Circular.continuationKeySwitchFirstReplacementAdvantage
          (Native.nativeCycleSpec
            (params.q securityParameter)
            (params.degree securityParameter)
            (params.ringRank securityParameter)
            (params.tgswLevels securityParameter)
            (params.lweDimension securityParameter)
            (params.keySwitchLevels securityParameter)
            (params.ringErrorSampler securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (params.tgswGadget securityParameter)
            (params.keySwitchGadget securityParameter))
          (Adaptive.continuation
            (adversary.queryCount securityParameter)
            (params.inputErrorSampler securityParameter)
            (params.encode securityParameter)
            (adversary.run securityParameter)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem
            (params.q securityParameter)
            (params.degree securityParameter)
            (params.ringRank securityParameter)
            (params.tgswLevels securityParameter)
            (params.lweDimension securityParameter)
            (params.ringErrorSampler securityParameter))
          (Native.BootstrapCutSecurity.realBatchReduction
            (params.ringErrorSampler securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (params.tgswGadget securityParameter)
            (Adaptive.CutCycleSecurity.cutContinuation
              (adversary.queryCount securityParameter)
              (params.inputErrorSampler securityParameter)
              (params.encode securityParameter)
              (adversary.run securityParameter))) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem
            (params.q securityParameter)
            (params.degree securityParameter)
            (params.ringRank securityParameter)
            (params.tgswLevels securityParameter)
            (params.lweDimension securityParameter)
            (params.ringErrorSampler securityParameter))
          (Native.BootstrapCutSecurity.zeroBatchReduction
            (params.ringErrorSampler securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (Adaptive.CutCycleSecurity.cutContinuation
              (adversary.queryCount securityParameter)
              (params.inputErrorSampler securityParameter)
              (params.encode securityParameter)
              (adversary.run securityParameter))) +
        LearningWithErrors.advantage
          (Adaptive.jointLweProblem
            (params.q securityParameter)
            (params.lweDimension securityParameter)
            (Encryption.Security.keySwitchSamples
              (params.ringRank securityParameter)
              (params.degree securityParameter)
              (params.keySwitchLevels securityParameter))
            (adversary.queryCount securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (params.inputErrorSampler securityParameter))
          (Adaptive.zeroCloudReduction
            (params.ringErrorSampler securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (params.inputErrorSampler securityParameter)
            (params.tgswGadget securityParameter)
            (params.encode securityParameter)
            (adversary.run securityParameter))) =
      ENNReal.ofReal
          (Circular.continuationKeySwitchFirstReplacementAdvantage
            (Native.nativeCycleSpec
              (params.q securityParameter)
              (params.degree securityParameter)
              (params.ringRank securityParameter)
              (params.tgswLevels securityParameter)
              (params.lweDimension securityParameter)
              (params.keySwitchLevels securityParameter)
              (params.ringErrorSampler securityParameter)
              (params.keySwitchErrorSampler securityParameter)
              (params.tgswGadget securityParameter)
              (params.keySwitchGadget securityParameter))
            (Adaptive.continuation
              (adversary.queryCount securityParameter)
              (params.inputErrorSampler securityParameter)
              (params.encode securityParameter)
              (adversary.run securityParameter))) +
        ENNReal.ofReal
          (LearningWithErrors.advantage
            (Native.BootstrapCutSecurity.batchModuleLweProblem
              (params.q securityParameter)
              (params.degree securityParameter)
              (params.ringRank securityParameter)
              (params.tgswLevels securityParameter)
              (params.lweDimension securityParameter)
              (params.ringErrorSampler securityParameter))
            (Native.BootstrapCutSecurity.realBatchReduction
              (params.ringErrorSampler securityParameter)
              (params.keySwitchErrorSampler securityParameter)
              (params.tgswGadget securityParameter)
              (Adaptive.CutCycleSecurity.cutContinuation
                (adversary.queryCount securityParameter)
                (params.inputErrorSampler securityParameter)
                (params.encode securityParameter)
                (adversary.run securityParameter)))) +
        ENNReal.ofReal
          (LearningWithErrors.advantage
            (Native.BootstrapCutSecurity.batchModuleLweProblem
              (params.q securityParameter)
              (params.degree securityParameter)
              (params.ringRank securityParameter)
              (params.tgswLevels securityParameter)
              (params.lweDimension securityParameter)
              (params.ringErrorSampler securityParameter))
            (Native.BootstrapCutSecurity.zeroBatchReduction
              (params.ringErrorSampler securityParameter)
              (params.keySwitchErrorSampler securityParameter)
              (Adaptive.CutCycleSecurity.cutContinuation
                (adversary.queryCount securityParameter)
                (params.inputErrorSampler securityParameter)
                (params.encode securityParameter)
                (adversary.run securityParameter)))) +
        ENNReal.ofReal
          (LearningWithErrors.advantage
            (Adaptive.jointLweProblem
              (params.q securityParameter)
              (params.lweDimension securityParameter)
              (Encryption.Security.keySwitchSamples
                (params.ringRank securityParameter)
                (params.degree securityParameter)
                (params.keySwitchLevels securityParameter))
              (adversary.queryCount securityParameter)
              (params.keySwitchErrorSampler securityParameter)
              (params.inputErrorSampler securityParameter))
            (Adaptive.zeroCloudReduction
              (params.ringErrorSampler securityParameter)
              (params.keySwitchErrorSampler securityParameter)
              (params.inputErrorSampler securityParameter)
              (params.tgswGadget securityParameter)
              (params.encode securityParameter)
              (adversary.run securityParameter))) := by
    rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hCircularNonneg hRealNonneg) hZeroNonneg)
        hJointNonneg,
      ENNReal.ofReal_add (add_nonneg hCircularNonneg hRealNonneg) hZeroNonneg,
      ENNReal.ofReal_add hCircularNonneg hRealNonneg]
  have hFinal := hLift.trans_eq hSum
  simpa only [securityGame, keySwitchFirstSecurityGame, continuationReduction,
    ringBatchLWESecurityGame, realRingBatchReduction, zeroRingBatchReduction,
    jointLWESecurityGame, zeroCloudJointLWEReduction] using hFinal

/-- Equal-noise pointwise form.  Every non-circular term is now an ordinary binary-secret batch
LWE advantage: two ring batches and one scalar batch containing all KSK and adaptive input rows. -/
theorem securityGame_advantage_le_keySwitchFirst_add_two_ringBatchLWE_add_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hEqualNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (securityGame params).advantage adversary securityParameter ≤
      (keySwitchFirstSecurityGame params).advantage
          (continuationReduction params adversary) securityParameter +
        (ringBatchLWESecurityGame params).advantage
          (realRingBatchReduction params adversary) securityParameter +
        (ringBatchLWESecurityGame params).advantage
          (zeroRingBatchReduction params adversary) securityParameter +
        (batchLWESecurityGame params).advantage
          (zeroCloudBatchLWEReduction params adversary) securityParameter := by
  have h :=
    Adaptive.CutCycleSecurity.abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_batchLwe_of_same_noise
      (adversary.queryCount securityParameter)
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)
      (adversary.isQueryBound securityParameter)
  rw [Adaptive.CutCycleSecurity.keySwitchFirstReplacementAdvantage_eq_abstract] at h
  have hCircularNonneg : 0 ≤
      Circular.continuationKeySwitchFirstReplacementAdvantage
        (Native.nativeCycleSpec
          (params.q securityParameter)
          (params.degree securityParameter)
          (params.ringRank securityParameter)
          (params.tgswLevels securityParameter)
          (params.lweDimension securityParameter)
          (params.keySwitchLevels securityParameter)
          (params.ringErrorSampler securityParameter)
          (params.keySwitchErrorSampler securityParameter)
          (params.tgswGadget securityParameter)
          (params.keySwitchGadget securityParameter))
        (Adaptive.continuation
          (adversary.queryCount securityParameter)
          (params.keySwitchErrorSampler securityParameter)
          (params.encode securityParameter)
          (adversary.run securityParameter)) := by
    unfold Circular.continuationKeySwitchFirstReplacementAdvantage
      ProbComp.boolDistAdvantage
    exact abs_nonneg _
  have hRealNonneg : 0 ≤
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          (params.q securityParameter)
          (params.degree securityParameter)
          (params.ringRank securityParameter)
          (params.tgswLevels securityParameter)
          (params.lweDimension securityParameter)
          (params.ringErrorSampler securityParameter))
        (Native.BootstrapCutSecurity.realBatchReduction
          (params.ringErrorSampler securityParameter)
          (params.keySwitchErrorSampler securityParameter)
          (params.tgswGadget securityParameter)
          (Adaptive.CutCycleSecurity.cutContinuation
            (adversary.queryCount securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (params.encode securityParameter)
            (adversary.run securityParameter))) :=
    FormalProof4FHE.LWE.advantage_nonneg _ _
  have hZeroNonneg : 0 ≤
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          (params.q securityParameter)
          (params.degree securityParameter)
          (params.ringRank securityParameter)
          (params.tgswLevels securityParameter)
          (params.lweDimension securityParameter)
          (params.ringErrorSampler securityParameter))
        (Native.BootstrapCutSecurity.zeroBatchReduction
          (params.ringErrorSampler securityParameter)
          (params.keySwitchErrorSampler securityParameter)
          (Adaptive.CutCycleSecurity.cutContinuation
            (adversary.queryCount securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (params.encode securityParameter)
            (adversary.run securityParameter))) :=
    FormalProof4FHE.LWE.advantage_nonneg _ _
  have hScalarNonneg : 0 ≤
      LearningWithErrors.advantage
        (Native.KeySwitchSecurity.binaryLweProblem
          (params.q securityParameter)
          (params.lweDimension securityParameter)
          (Encryption.Security.keySwitchSamples
              (params.ringRank securityParameter)
              (params.degree securityParameter)
              (params.keySwitchLevels securityParameter) +
            adversary.queryCount securityParameter)
          (params.keySwitchErrorSampler securityParameter))
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (Adaptive.zeroCloudReduction
            (params.ringErrorSampler securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (params.tgswGadget securityParameter)
            (params.encode securityParameter)
            (adversary.run securityParameter))) :=
    FormalProof4FHE.LWE.advantage_nonneg _ _
  have hLift := ENNReal.ofReal_le_ofReal h
  have hFinal := hLift.trans_eq
    (ofReal_add_four _ _ _ _ hCircularNonneg hRealNonneg hZeroNonneg hScalarNonneg)
  simpa only [securityGame, keySwitchFirstSecurityGame, continuationReduction,
    ringBatchLWESecurityGame, realRingBatchReduction, zeroRingBatchReduction,
    batchLWESecurityGame, zeroCloudBatchLWEReduction, hEqualNoise securityParameter] using hFinal

/-- **Asymptotic adaptive native TFHE security in KSK-first order.** If the exact intact-cycle
game and all three ordinary post-cut games are secure for the reduced efficient families, then
the honest adaptive TFHE game has negligible advantage. -/
theorem secureAgainst_of_keySwitchFirst_and_two_ringBatchLWE_and_jointLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : PolynomialQueryAdversary params → Prop)
    (continuationIsPPT : ContinuationFamily params → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT : RingBatchLWEAdversaryFamily params → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily params → Prop)
    (hContinuationClosed : ∀ adversary, isPPT adversary →
      continuationIsPPT (continuationReduction params adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (zeroCloudJointLWEReduction params adversary))
    (hCircular : (keySwitchFirstSecurityGame params).secureAgainst continuationIsPPT)
    (hRealRingBatch : (ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch : (ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hJointLWE : (jointLWESecurityGame params).secureAgainst jointLWEIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (securityGame_advantage_le_keySwitchFirst_add_two_ringBatchLWE_add_jointLWE
      params adversary)
    (negligible_add
      (negligible_add
        (negligible_add
          (hCircular _ (hContinuationClosed adversary hadversary))
          (hRealRingBatch _ (hRealRingBatchClosed adversary hadversary)))
        (hZeroRingBatch _ (hZeroRingBatchClosed adversary hadversary)))
      (hJointLWE _ (hJointLWEClosed adversary hadversary)))

/-- **Equal-noise asymptotic cut-cycle theorem.** Negligibility of the one native intact-cycle
game and three ordinary batch-LWE games implies negligible adaptive TFHE advantage. -/
theorem secureAgainst_of_keySwitchFirst_and_three_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hEqualNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (continuationIsPPT : ContinuationFamily params → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT : RingBatchLWEAdversaryFamily params → Prop)
    (scalarBatchIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hContinuationClosed : ∀ adversary, isPPT adversary →
      continuationIsPPT (continuationReduction params adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hScalarBatchClosed : ∀ adversary, isPPT adversary →
      scalarBatchIsPPT (zeroCloudBatchLWEReduction params adversary))
    (hCircular : (keySwitchFirstSecurityGame params).secureAgainst continuationIsPPT)
    (hRealRingBatch : (ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch : (ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hScalarBatch : (batchLWESecurityGame params).secureAgainst scalarBatchIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (securityGame_advantage_le_keySwitchFirst_add_two_ringBatchLWE_add_batchLWE
      params hEqualNoise adversary)
    (negligible_add
      (negligible_add
        (negligible_add
          (hCircular _ (hContinuationClosed adversary hadversary))
          (hRealRingBatch _ (hRealRingBatchClosed adversary hadversary)))
        (hZeroRingBatch _ (hZeroRingBatchClosed adversary hadversary)))
      (hScalarBatch _ (hScalarBatchClosed adversary hadversary)))

/-! ## Equivalence of the two intact-cycle assumptions -/

/-- Pointwise KSK-first cost is bounded by BRK-first direct-bilinear cost plus only the four
checked post-cut LWE reductions. -/
theorem adaptiveKeySwitchFirst_advantage_le_directBilinear_add_postCutLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (adaptiveKeySwitchFirstSecurityGame params).advantage adversary securityParameter ≤
      (adaptiveDirectBilinearSecurityGame params).advantage adversary securityParameter +
        (ringBatchLWESecurityGame params).advantage
          (realRingBatchReduction params adversary) securityParameter +
        (ringBatchLWESecurityGame params).advantage
          (zeroRingBatchReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (zeroCloudJointLWEReduction params adversary) securityParameter := by
  have h :=
    Adaptive.CutCycleSecurity.keySwitchFirstReplacementAdvantage_le_directBilinear_add_postCutLwe
      (adversary.queryCount securityParameter)
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)
  rw [Adaptive.CutCycleSecurity.keySwitchFirstReplacementAdvantage_eq_abstract] at h
  have hLift := ENNReal.ofReal_le_ofReal h
  have hFinal := hLift.trans (ofReal_add_five_le _ _ _ _ _)
  simpa only [adaptiveKeySwitchFirstSecurityGame, keySwitchFirstSecurityGame,
    adaptiveDirectBilinearSecurityGame, directBilinearSecurityGame, continuationReduction,
    ringBatchLWESecurityGame, realRingBatchReduction, zeroRingBatchReduction,
    jointLWESecurityGame, jointLWEReduction, zeroCloudJointLWEReduction] using hFinal

/-- Pointwise BRK-first direct-bilinear cost is bounded by KSK-first cost plus exactly the same
four checked post-cut LWE reductions. -/
theorem adaptiveDirectBilinear_advantage_le_keySwitchFirst_add_postCutLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (adaptiveDirectBilinearSecurityGame params).advantage adversary securityParameter ≤
      (adaptiveKeySwitchFirstSecurityGame params).advantage adversary securityParameter +
        (ringBatchLWESecurityGame params).advantage
          (realRingBatchReduction params adversary) securityParameter +
        (ringBatchLWESecurityGame params).advantage
          (zeroRingBatchReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (zeroCloudJointLWEReduction params adversary) securityParameter := by
  have h :=
    Adaptive.CutCycleSecurity.directBilinearAdvantage_le_keySwitchFirst_add_postCutLwe
      (adversary.queryCount securityParameter)
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)
  rw [Adaptive.CutCycleSecurity.keySwitchFirstReplacementAdvantage_eq_abstract] at h
  have hLift := ENNReal.ofReal_le_ofReal h
  have hFinal := hLift.trans (ofReal_add_five_le _ _ _ _ _)
  simpa only [adaptiveKeySwitchFirstSecurityGame, keySwitchFirstSecurityGame,
    adaptiveDirectBilinearSecurityGame, directBilinearSecurityGame, continuationReduction,
    ringBatchLWESecurityGame, realRingBatchReduction, zeroRingBatchReduction,
    jointLWESecurityGame, jointLWEReduction, zeroCloudJointLWEReduction] using hFinal

/-- Negligible BRK-first direct-bilinear advantage implies negligible KSK-first advantage for the
same adaptive adversary class whenever all four checked post-cut reductions preserve efficiency
and target secure LWE classes. -/
theorem adaptiveKeySwitchFirst_secureAgainst_of_directBilinear_and_postCutLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : PolynomialQueryAdversary params → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT : RingBatchLWEAdversaryFamily params → Prop)
    (nativeJointLWEIsPPT zeroJointLWEIsPPT : JointLWEAdversaryFamily params → Prop)
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hNativeJointLWEClosed : ∀ adversary, isPPT adversary →
      nativeJointLWEIsPPT (jointLWEReduction params adversary))
    (hZeroJointLWEClosed : ∀ adversary, isPPT adversary →
      zeroJointLWEIsPPT (zeroCloudJointLWEReduction params adversary))
    (hDirect : (adaptiveDirectBilinearSecurityGame params).secureAgainst isPPT)
    (hRealRingBatch : (ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch : (ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hNativeJointLWE : (jointLWESecurityGame params).secureAgainst nativeJointLWEIsPPT)
    (hZeroJointLWE : (jointLWESecurityGame params).secureAgainst zeroJointLWEIsPPT) :
    (adaptiveKeySwitchFirstSecurityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (adaptiveKeySwitchFirst_advantage_le_directBilinear_add_postCutLWE params adversary)
    (negligible_add
      (negligible_add
        (negligible_add
          (negligible_add
            (hDirect adversary hadversary)
            (hRealRingBatch _ (hRealRingBatchClosed adversary hadversary)))
          (hZeroRingBatch _ (hZeroRingBatchClosed adversary hadversary)))
        (hNativeJointLWE _ (hNativeJointLWEClosed adversary hadversary)))
      (hZeroJointLWE _ (hZeroJointLWEClosed adversary hadversary)))

/-- The converse asymptotic transfer: negligible KSK-first advantage implies negligible
BRK-first direct-bilinear advantage under the same checked post-cut LWE hypotheses. -/
theorem adaptiveDirectBilinear_secureAgainst_of_keySwitchFirst_and_postCutLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : PolynomialQueryAdversary params → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT : RingBatchLWEAdversaryFamily params → Prop)
    (nativeJointLWEIsPPT zeroJointLWEIsPPT : JointLWEAdversaryFamily params → Prop)
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hNativeJointLWEClosed : ∀ adversary, isPPT adversary →
      nativeJointLWEIsPPT (jointLWEReduction params adversary))
    (hZeroJointLWEClosed : ∀ adversary, isPPT adversary →
      zeroJointLWEIsPPT (zeroCloudJointLWEReduction params adversary))
    (hKeySwitchFirst : (adaptiveKeySwitchFirstSecurityGame params).secureAgainst isPPT)
    (hRealRingBatch : (ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch : (ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hNativeJointLWE : (jointLWESecurityGame params).secureAgainst nativeJointLWEIsPPT)
    (hZeroJointLWE : (jointLWESecurityGame params).secureAgainst zeroJointLWEIsPPT) :
    (adaptiveDirectBilinearSecurityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (adaptiveDirectBilinear_advantage_le_keySwitchFirst_add_postCutLWE params adversary)
    (negligible_add
      (negligible_add
        (negligible_add
          (negligible_add
            (hKeySwitchFirst adversary hadversary)
            (hRealRingBatch _ (hRealRingBatchClosed adversary hadversary)))
          (hZeroRingBatch _ (hZeroRingBatchClosed adversary hadversary)))
        (hNativeJointLWE _ (hNativeJointLWEClosed adversary hadversary)))
      (hZeroJointLWE _ (hZeroJointLWEClosed adversary hadversary)))

/-- Under ordinary security of all checked post-cut reductions, the two native intact-cycle
assumptions are equivalent for polynomial-query adaptive TFHE adversaries. -/
theorem adaptiveFirstHop_secureAgainst_iff
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : PolynomialQueryAdversary params → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT : RingBatchLWEAdversaryFamily params → Prop)
    (nativeJointLWEIsPPT zeroJointLWEIsPPT : JointLWEAdversaryFamily params → Prop)
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hNativeJointLWEClosed : ∀ adversary, isPPT adversary →
      nativeJointLWEIsPPT (jointLWEReduction params adversary))
    (hZeroJointLWEClosed : ∀ adversary, isPPT adversary →
      zeroJointLWEIsPPT (zeroCloudJointLWEReduction params adversary))
    (hRealRingBatch : (ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch : (ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hNativeJointLWE : (jointLWESecurityGame params).secureAgainst nativeJointLWEIsPPT)
    (hZeroJointLWE : (jointLWESecurityGame params).secureAgainst zeroJointLWEIsPPT) :
    (adaptiveKeySwitchFirstSecurityGame params).secureAgainst isPPT ↔
      (adaptiveDirectBilinearSecurityGame params).secureAgainst isPPT := by
  constructor
  · intro hKeySwitchFirst
    exact adaptiveDirectBilinear_secureAgainst_of_keySwitchFirst_and_postCutLWE
      params isPPT realRingBatchIsPPT zeroRingBatchIsPPT nativeJointLWEIsPPT
      zeroJointLWEIsPPT hRealRingBatchClosed hZeroRingBatchClosed hNativeJointLWEClosed
      hZeroJointLWEClosed hKeySwitchFirst hRealRingBatch hZeroRingBatch hNativeJointLWE
      hZeroJointLWE
  · intro hDirect
    exact adaptiveKeySwitchFirst_secureAgainst_of_directBilinear_and_postCutLWE
      params isPPT realRingBatchIsPPT zeroRingBatchIsPPT nativeJointLWEIsPPT
      zeroJointLWEIsPPT hRealRingBatchClosed hZeroRingBatchClosed hNativeJointLWEClosed
      hZeroJointLWEClosed hDirect hRealRingBatch hZeroRingBatch hNativeJointLWE
      hZeroJointLWE

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.CutCycleSecurity
