/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CenteredBinomialCharacteristicTwo
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleAdaptiveEncryption

set_option autoImplicit false

/-!
# Concrete Characteristic-Two Circular-Security Endpoint

A positive-width centered-binomial coefficient is exactly uniform modulo two.  The independent
coefficient sampler is therefore uniform on the complete native negacyclic ring.  This file
connects that executable error law to the reusable-key shared-randomness TFHE theorem.

The resulting security statement has no circular/KDM premise: adaptive confidentiality, and the
same statement after arbitrary deterministic public ciphertext evaluation, reduce to one
ordinary binary-secret batch-LWE problem modulo two.

This is deliberately a security-only endpoint.  The ring error is uniform, so it destroys the
noise margin required for TFHE decryption and bootstrapping correctness.  It is a concrete
centered-binomial realization of the exact-uniform theorem, not a proof for standard narrow-noise
TFHE parameters.
-/

open Matrix OracleComp OracleSpec

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle.CenteredBinomialTwo

noncomputable section

/-- Positive-width centered-binomial ring error has zero total-variation distance from uniform
at coefficient modulus two. -/
theorem ringError_tvDist_uniform_eq_zero (degree eta : ℕ) :
    tvDist (RLWE.CenteredBinomial.sampler 2 degree (eta + 1))
      ($ᵗ (RLWE.Rq 2 degree)) = 0 := by
  unfold tvDist
  rw [RLWE.CenteredBinomial.sampler_two_evalDist_eq_uniform degree eta]
  exact SPMF.tvDist_self _

/-- **Concrete adaptive confidentiality bound.**  With positive-width centered-binomial BRK
errors modulo two, the complete reusable-key TFHE advantage is bounded by one ordinary
query-counted binary-secret batch-LWE advantage; no circular term remains. -/
theorem abs_signedAdvantage_real_le_batchLwe_of_same_noise
    {Message : Type}
    {prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (queryCount eta : ℕ)
    (errorSampler : ProbComp (ZMod 2))
    (tgswGadget : Fin tgswLevels →
      RLWE.Rq 2 (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod 2)
    (encode : Message → ZMod 2)
    (adversary : SharedAdversary Message 2 prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount
        (RLWE.CenteredBinomial.sampler 2
          (prefixDimension + suffixDimension) (eta + 1))
        errorSampler errorSampler tgswGadget keySwitchGadget encode adversary)| ≤
      LearningWithErrors.advantage
        (Native.KeySwitchSecurity.binaryLweProblem 2 prefixDimension
          (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (jointLweReduction errorSampler errorSampler keySwitchGadget
            encode adversary)) := by
  have h :=
    abs_signedAdvantage_real_le_ringErrorDistance_add_batchLwe_of_same_noise
      (q := 2) queryCount
      (RLWE.CenteredBinomial.sampler 2
        (prefixDimension + suffixDimension) (eta + 1))
      errorSampler tgswGadget keySwitchGadget encode adversary hbound
  rw [ringError_tvDist_uniform_eq_zero
    (prefixDimension + suffixDimension) eta] at h
  simpa using h

/-- Arbitrary deterministic public evaluation preserves the same concrete no-circular-assumption
bound and query count. -/
theorem abs_signedAdvantage_publicEvaluation_le_batchLwe_of_same_noise
    {Message Output : Type}
    {prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (queryCount eta : ℕ)
    (errorSampler : ProbComp (ZMod 2))
    (tgswGadget : Fin tgswLevels →
      RLWE.Rq 2 (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod 2)
    (encode : Message → ZMod 2)
    (evaluate : CloudKey 2 prefixDimension suffixDimension tgswLevels keySwitchLevels →
      TLWE.Ciphertext (ZMod 2) prefixDimension → Output)
    (adversary : Adaptive.Adversary Message
      (CloudKey 2 prefixDimension suffixDimension tgswLevels keySwitchLevels) Output)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount
        (RLWE.CenteredBinomial.sampler 2
          (prefixDimension + suffixDimension) (eta + 1))
        errorSampler errorSampler tgswGadget keySwitchGadget encode
        (Adaptive.compilePublicEvaluation evaluate adversary))| ≤
      LearningWithErrors.advantage
        (Native.KeySwitchSecurity.binaryLweProblem 2 prefixDimension
          (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode
            (Adaptive.compilePublicEvaluation evaluate adversary))) := by
  have h :=
    abs_signedAdvantage_publicEvaluation_le_ringErrorDistance_add_batchLwe
      (q := 2) queryCount
      (RLWE.CenteredBinomial.sampler 2
        (prefixDimension + suffixDimension) (eta + 1))
      errorSampler tgswGadget keySwitchGadget encode evaluate adversary hbound
  rw [ringError_tvDist_uniform_eq_zero
    (prefixDimension + suffixDimension) eta] at h
  simpa using h

/-- Adversary-class form: ordinary batch-LWE hardness alone proves reusable-key adaptive
confidentiality for the concrete characteristic-two centered-binomial ring-error variant. -/
theorem hardAgainst_of_batchLwe_same_noise
    {Message : Type}
    {prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (queryCount eta : ℕ)
    (errorSampler : ProbComp (ZMod 2))
    (tgswGadget : Fin tgswLevels →
      RLWE.Rq 2 (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod 2)
    (encode : Message → ZMod 2)
    (allowed : SharedAdversary Message 2 prefixDimension suffixDimension
      tgswLevels keySwitchLevels → Prop)
    (batchLweAllowed : LearningWithErrors.Adversary
      (Native.KeySwitchSecurity.binaryLweProblem 2 prefixDimension
        (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler) → Prop)
    (batchLweBound : ℝ)
    (hBatchLweClosed : ∀ adversary, allowed adversary →
      batchLweAllowed
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary)))
    (hBatchLwe : FormalProof4FHE.LWE.HardAgainst
      (Native.KeySwitchSecurity.binaryLweProblem 2 prefixDimension
        (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
      batchLweAllowed batchLweBound) :
    HardAgainst queryCount
      (RLWE.CenteredBinomial.sampler 2
        (prefixDimension + suffixDimension) (eta + 1))
      errorSampler errorSampler tgswGadget keySwitchGadget encode allowed batchLweBound := by
  intro adversary hadversary hbound
  exact (abs_signedAdvantage_real_le_batchLwe_of_same_noise
    queryCount eta errorSampler tgswGadget keySwitchGadget encode adversary hbound).trans
      (hBatchLwe _ (hBatchLweClosed adversary hadversary))

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle.CenteredBinomialTwo
