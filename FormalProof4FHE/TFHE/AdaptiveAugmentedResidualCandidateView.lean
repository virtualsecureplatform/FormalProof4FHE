/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveAugmentedCandidateView
import FormalProof4FHE.TFHE.NativeResidualCandidateView

/-!
# Residual Normal Forms for Augmented Adaptive TFHE Candidate Views

This module threads the bounded zero-message input tape through the native residual/smudging
interface.  For each fresh scalar/ring secret pair, the tape is sampled under the same scalar
secret as the BRK and KSK.  Because candidate transport of the tape is exact, the only statistical
cost remains the existing BRK/KSK residual-smudging cost.

Correct and wrong shifted-evaluator normal forms are required only after averaging over the full
augmented source `(BRK, KSK, tape)`.  The correct side also supports residuals sampled from
evaluator coins, with explicit zero-failure and support-wise cost hypotheses.  The adapters
discharge the augmented candidate-view distances and then invoke the checked thresholded
amplification, scalar union bound, and centered-binomial paired-key completion.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual

open Native
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery

variable
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]

/-- One complete native BRK/KSK residual value.  A homomorphic evaluator may sample such a value
through its own coins, so the sampled-residual interface below does not force it to be a
deterministic function of the public source context. -/
abbrev EvaluationKeyResidual
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  ConditionalSmudging.BootstrappingResidual
      q degree ringRank tgswLevels lweDimension ×
    ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels

/-- Fresh-secret correct-candidate residual view with a same-secret zero-message input tape. -/
noncomputable def freshResidualRealView
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringResidual : Secret lweDimension ringRank degree →
      ConditionalSmudging.BootstrappingResidual
        q degree ringRank tgswLevels lweDimension)
    (keySwitchResidual : Secret lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels) :
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let secrets ← Native.ResidualCandidateView.sampleSecretPair
    lweDimension ringRank degree
  let evaluationKeys ← ConditionalSmudging.generateResidualEvaluationKeyPair
    q degree ringRank tgswLevels lweDimension keySwitchLevels
    ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
    secrets.1 secrets.2 (ringResidual secrets) (keySwitchResidual secrets)
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret secrets.1) 0
  return (evaluationKeys.1, evaluationKeys.2, tape)

/-- Fresh-secret exact monomial target with its same-secret input tape. -/
noncomputable def freshMonomialRealView
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let secrets ← Native.ResidualCandidateView.sampleSecretPair
    lweDimension ringRank degree
  let evaluationKeys ← ConditionalSmudging.generateMonomialEvaluationKeyPair
    q degree ringRank tgswLevels lweDimension keySwitchLevels
    ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
    secrets.1 secrets.2
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret secrets.1) 0
  return (evaluationKeys.1, evaluationKeys.2, tape)

/-- The factored augmented monomial view is exactly the public real target. -/
theorem freshMonomialRealView_eq_realPublicView
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    freshMonomialRealView (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) ringWideNoise keySwitchWideNoise
        inputErrorSampler tgswGadget keySwitchGadget =
      realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) ringWideNoise keySwitchWideNoise
        inputErrorSampler tgswGadget keySwitchGadget := by
  simp [freshMonomialRealView, Native.ResidualCandidateView.sampleSecretPair,
    realPublicView, KeySwitchFirstFiniteView.augmentedCircularProblem,
    KeySwitchFirstFiniteView.secretSampler,
    ConditionalSmudging.generateMonomialEvaluationKeyPair, monad_norm]

/-- Adding the exact same tape to both conditional endpoints introduces no smudging loss. -/
theorem tvDist_freshResidualRealView_realPublicView_le
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringResidual : Secret lweDimension ringRank degree →
      ConditionalSmudging.BootstrappingResidual
        q degree ringRank tgswLevels lweDimension)
    (keySwitchResidual : Secret lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels)
    (bound : ℝ)
    (hbound : ∀ secrets,
      ConditionalSmudging.evaluationKeySmudgingCost ringWideNoise keySwitchWideNoise
        (ringResidual secrets) (keySwitchResidual secrets) ≤ bound) :
    tvDist
        (freshResidualRealView (ringRank := ringRank) (queryCount := queryCount)
          ringWideNoise keySwitchWideNoise inputErrorSampler tgswGadget keySwitchGadget
          ringResidual keySwitchResidual)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) ringWideNoise keySwitchWideNoise
          inputErrorSampler tgswGadget keySwitchGadget) ≤ bound := by
  let secrets := Native.ResidualCandidateView.sampleSecretPair
    lweDimension ringRank degree
  let residualContinuation := fun secretPair : Secret lweDimension ringRank degree ↦
    TFHE.SamplerReplacement.independentPair
      (ConditionalSmudging.generateResidualEvaluationKeyPair
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
        secretPair.1 secretPair.2 (ringResidual secretPair)
        (keySwitchResidual secretPair))
      (TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
        (embedBinarySecret secretPair.1) 0)
      (fun evaluationKeys tape ↦ (evaluationKeys.1, evaluationKeys.2, tape))
  let targetContinuation := fun secretPair : Secret lweDimension ringRank degree ↦
    TFHE.SamplerReplacement.independentPair
      (ConditionalSmudging.generateMonomialEvaluationKeyPair
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
        secretPair.1 secretPair.2)
      (TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
        (embedBinarySecret secretPair.1) 0)
      (fun evaluationKeys tape ↦ (evaluationKeys.1, evaluationKeys.2, tape))
  have hcontinuation : ∀ secretPair,
      tvDist (residualContinuation secretPair) (targetContinuation secretPair) ≤ bound := by
    intro secretPair
    have hpair := TFHE.SamplerReplacement.tvDist_independentPair_le
      (ConditionalSmudging.generateResidualEvaluationKeyPair
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
        secretPair.1 secretPair.2 (ringResidual secretPair)
        (keySwitchResidual secretPair))
      (ConditionalSmudging.generateMonomialEvaluationKeyPair
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
        secretPair.1 secretPair.2)
      (TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
        (embedBinarySecret secretPair.1) 0)
      (TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
        (embedBinarySecret secretPair.1) 0)
      (fun evaluationKeys tape ↦ (evaluationKeys.1, evaluationKeys.2, tape))
    have hkeys :=
      ConditionalSmudging.tvDist_generateResidualEvaluationKeyPair_generateMonomial_le
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
        secretPair.1 secretPair.2 (ringResidual secretPair)
        (keySwitchResidual secretPair)
    exact hpair.trans (by
      rw [tvDist_self, add_zero]
      exact hkeys.trans (hbound secretPair))
  have h := tvDist_bind_left_le_const' secrets residualContinuation
    targetContinuation bound hcontinuation
  rw [← freshMonomialRealView_eq_realPublicView
    (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
    ringWideNoise keySwitchWideNoise inputErrorSampler tgswGadget keySwitchGadget]
  simpa [freshResidualRealView, freshMonomialRealView, secrets,
    residualContinuation, targetContinuation,
    TFHE.SamplerReplacement.independentPair] using h

/-! ## Sampled correct residuals -/

/-- Fixed-secret augmented public view with one supplied BRK/KSK residual value. -/
noncomputable def residualRealViewAtSecret
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Secret lweDimension ringRank degree)
    (residual : EvaluationKeyResidual q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let evaluationKeys ← ConditionalSmudging.generateResidualEvaluationKeyPair
    q degree ringRank tgswLevels lweDimension keySwitchLevels
    ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
    secrets.1 secrets.2 residual.1 residual.2
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret secrets.1) 0
  return (evaluationKeys.1, evaluationKeys.2, tape)

/-- Fixed-secret exact monomial public view used as the comparison for sampled residuals. -/
noncomputable def monomialRealViewAtSecret
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Secret lweDimension ringRank degree) :
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let evaluationKeys ← ConditionalSmudging.generateMonomialEvaluationKeyPair
    q degree ringRank tgswLevels lweDimension keySwitchLevels
    ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
    secrets.1 secrets.2
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret secrets.1) 0
  return (evaluationKeys.1, evaluationKeys.2, tape)

/-- Conditional smudging for one fixed secret pair and one sampled residual value. -/
theorem tvDist_residualRealViewAtSecret_monomialRealViewAtSecret_le
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Secret lweDimension ringRank degree)
    (residual : EvaluationKeyResidual q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    tvDist
        (residualRealViewAtSecret (queryCount := queryCount)
          ringWideNoise keySwitchWideNoise inputErrorSampler tgswGadget
          keySwitchGadget secrets residual)
        (monomialRealViewAtSecret (queryCount := queryCount)
          ringWideNoise keySwitchWideNoise inputErrorSampler tgswGadget
          keySwitchGadget secrets) ≤
      ConditionalSmudging.evaluationKeySmudgingCost
        ringWideNoise keySwitchWideNoise residual.1 residual.2 := by
  let residualKeys := ConditionalSmudging.generateResidualEvaluationKeyPair
    q degree ringRank tgswLevels lweDimension keySwitchLevels
    ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
    secrets.1 secrets.2 residual.1 residual.2
  let targetKeys := ConditionalSmudging.generateMonomialEvaluationKeyPair
    q degree ringRank tgswLevels lweDimension keySwitchLevels
    ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
    secrets.1 secrets.2
  let tape := TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret secrets.1) 0
  have hpair := TFHE.SamplerReplacement.tvDist_independentPair_le
    residualKeys targetKeys tape tape
    (fun evaluationKeys inputTape ↦
      (evaluationKeys.1, evaluationKeys.2, inputTape))
  have hkeys :=
    ConditionalSmudging.tvDist_generateResidualEvaluationKeyPair_generateMonomial_le
      q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringWideNoise keySwitchWideNoise tgswGadget keySwitchGadget
      secrets.1 secrets.2 residual.1 residual.2
  have hcost : tvDist residualKeys targetKeys + tvDist tape tape ≤
      ConditionalSmudging.evaluationKeySmudgingCost
        ringWideNoise keySwitchWideNoise residual.1 residual.2 := by
    rw [tvDist_self, add_zero]
    exact hkeys
  have h := hpair.trans hcost
  simpa [residualRealViewAtSecret, monomialRealViewAtSecret,
    residualKeys, targetKeys, tape, TFHE.SamplerReplacement.independentPair,
    monad_norm] using h

/-- Fresh-secret correct view whose residual is sampled after the secret pair.  The explicit
totality premise in the theorem below prevents a failing residual sampler from being silently
identified with the probability-one target experiment. -/
noncomputable def freshSampledResidualRealView
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (residualSampler : Secret lweDimension ringRank degree →
      ProbComp (EvaluationKeyResidual q degree ringRank tgswLevels
        lweDimension keySwitchLevels)) :
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let secrets ← Native.ResidualCandidateView.sampleSecretPair
    lweDimension ringRank degree
  let residual ← residualSampler secrets
  residualRealViewAtSecret (queryCount := queryCount)
    ringWideNoise keySwitchWideNoise inputErrorSampler tgswGadget
    keySwitchGadget secrets residual

/-- Sampled conditional residuals are absorbed by the same support-wise smudging bound as fixed
residuals.  No independence between the residual and the fresh secret pair is required. -/
theorem tvDist_freshSampledResidualRealView_realPublicView_le
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (residualSampler : Secret lweDimension ringRank degree →
      ProbComp (EvaluationKeyResidual q degree ringRank tgswLevels
        lweDimension keySwitchLevels))
    (bound : ℝ)
    (hTotal : ∀ secrets, probFailure (residualSampler secrets) = 0)
    (hbound : ∀ secrets residual,
      residual ∈ support (residualSampler secrets) →
      ConditionalSmudging.evaluationKeySmudgingCost
          ringWideNoise keySwitchWideNoise residual.1 residual.2 ≤ bound) :
    tvDist
        (freshSampledResidualRealView (queryCount := queryCount)
          ringWideNoise keySwitchWideNoise inputErrorSampler tgswGadget
          keySwitchGadget residualSampler)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) ringWideNoise keySwitchWideNoise
          inputErrorSampler tgswGadget keySwitchGadget) ≤ bound := by
  let secrets := Native.ResidualCandidateView.sampleSecretPair
    lweDimension ringRank degree
  let residualContinuation := fun secretPair : Secret lweDimension ringRank degree ↦
    residualSampler secretPair >>= fun residual ↦
      residualRealViewAtSecret (queryCount := queryCount)
        ringWideNoise keySwitchWideNoise inputErrorSampler tgswGadget
        keySwitchGadget secretPair residual
  let targetContinuation := fun secretPair : Secret lweDimension ringRank degree ↦
    monomialRealViewAtSecret (queryCount := queryCount)
      ringWideNoise keySwitchWideNoise inputErrorSampler tgswGadget
      keySwitchGadget secretPair
  have hcontinuation : ∀ secretPair,
      tvDist (residualContinuation secretPair) (targetContinuation secretPair) ≤ bound := by
    intro secretPair
    have hmix := tvDist_bind_left_le_const (residualSampler secretPair)
      (fun residual ↦ residualRealViewAtSecret (queryCount := queryCount)
        ringWideNoise keySwitchWideNoise inputErrorSampler tgswGadget
        keySwitchGadget secretPair residual)
      (fun _ ↦ targetContinuation secretPair) bound
      (fun residual hsupport ↦
        (tvDist_residualRealViewAtSecret_monomialRealViewAtSecret_le
          (queryCount := queryCount) ringWideNoise keySwitchWideNoise
          inputErrorSampler tgswGadget keySwitchGadget secretPair residual).trans
            (hbound secretPair residual hsupport))
    have htarget :
        evalDist (residualSampler secretPair >>= fun _ ↦ targetContinuation secretPair) =
          evalDist (targetContinuation secretPair) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        (residualSampler secretPair) (hTotal secretPair) (targetContinuation secretPair)
    unfold tvDist at hmix ⊢
    rw [htarget] at hmix
    exact hmix
  have h := tvDist_bind_left_le_const' secrets residualContinuation
    targetContinuation bound hcontinuation
  rw [← freshMonomialRealView_eq_realPublicView
    (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
    ringWideNoise keySwitchWideNoise inputErrorSampler tgswGadget keySwitchGadget]
  simpa [freshSampledResidualRealView, freshMonomialRealView, secrets,
    residualContinuation, targetContinuation, residualRealViewAtSecret,
    monomialRealViewAtSecret] using h

/-! ## Uniform-BRK residual endpoint -/

/-- Wrong-candidate residual view: uniform BRK, residual KSK, and same-secret input tape. -/
noncomputable def freshResidualUniformView
    (keySwitchWideNoise inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (keySwitchResidual : Secret lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels) :
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let secrets ← Native.ResidualCandidateView.sampleSecretPair
    lweDimension ringRank degree
  let bootstrappingKey ← $ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)
  let keySwitchKey ← ConditionalSmudging.generateResidualKeySwitchKey
    q degree ringRank lweDimension keySwitchLevels keySwitchWideNoise keySwitchGadget
    secrets.2 secrets.1 (keySwitchResidual secrets)
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret secrets.1) 0
  return (bootstrappingKey, keySwitchKey, tape)

/-- Exact uniform-BRK target with real KSK and same-secret input tape. -/
noncomputable def freshUniformView
    (keySwitchWideNoise inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let secrets ← Native.ResidualCandidateView.sampleSecretPair
    lweDimension ringRank degree
  let bootstrappingKey ← $ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)
  let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
    keySwitchLevels keySwitchWideNoise keySwitchGadget
    (keyExtract secrets.2) secrets.1
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret secrets.1) 0
  return (bootstrappingKey, keySwitchKey, tape)

/-- The factored uniform target is exactly the augmented public uniform endpoint. -/
theorem freshUniformView_eq_uniformPublicView
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    freshUniformView (ringRank := ringRank) (tgswLevels := tgswLevels)
        (queryCount := queryCount) keySwitchWideNoise inputErrorSampler keySwitchGadget =
      uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) ringWideNoise keySwitchWideNoise inputErrorSampler
        tgswGadget keySwitchGadget := by
  simp [freshUniformView, Native.ResidualCandidateView.sampleSecretPair,
    uniformPublicView, KeySwitchFirstFiniteView.augmentedCircularProblem,
    KeySwitchFirstFiniteView.secretSampler, monad_norm]

/-- At the uniform-BRK endpoint only the KSK residual is charged; the tape is exact. -/
theorem tvDist_freshResidualUniformView_uniformPublicView_le
    (ringWideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchWideNoise inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (keySwitchResidual : Secret lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels)
    (bound : ℝ)
    (hbound : ∀ secrets,
      ConditionalSmudging.keySwitchSmudgingCost keySwitchWideNoise
        (keySwitchResidual secrets) ≤ bound) :
    tvDist
        (freshResidualUniformView (ringRank := ringRank) (tgswLevels := tgswLevels)
          (queryCount := queryCount) keySwitchWideNoise inputErrorSampler
          keySwitchGadget keySwitchResidual)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) ringWideNoise keySwitchWideNoise
          inputErrorSampler tgswGadget keySwitchGadget) ≤ bound := by
  let secrets := Native.ResidualCandidateView.sampleSecretPair
    lweDimension ringRank degree
  let residualContinuation := fun secretPair : Secret lweDimension ringRank degree ↦ do
    let bootstrappingKey ← $ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)
    let keySwitchKey ← ConditionalSmudging.generateResidualKeySwitchKey
      q degree ringRank lweDimension keySwitchLevels keySwitchWideNoise keySwitchGadget
      secretPair.2 secretPair.1 (keySwitchResidual secretPair)
    let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
      (embedBinarySecret secretPair.1) 0
    return (bootstrappingKey, keySwitchKey, tape)
  let targetContinuation := fun secretPair : Secret lweDimension ringRank degree ↦ do
    let bootstrappingKey ← $ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)
    let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
      keySwitchLevels keySwitchWideNoise keySwitchGadget
      (keyExtract secretPair.2) secretPair.1
    let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
      (embedBinarySecret secretPair.1) 0
    return (bootstrappingKey, keySwitchKey, tape)
  have hcontinuation : ∀ secretPair,
      tvDist (residualContinuation secretPair) (targetContinuation secretPair) ≤ bound := by
    intro secretPair
    let uniformBootstrap : ProbComp
        (BootstrappingKey q degree ringRank tgswLevels lweDimension) :=
      $ᵗ (BootstrappingKey q degree ringRank tgswLevels lweDimension)
    let residualSwitch := ConditionalSmudging.generateResidualKeySwitchKey
      q degree ringRank lweDimension keySwitchLevels keySwitchWideNoise keySwitchGadget
      secretPair.2 secretPair.1 (keySwitchResidual secretPair)
    let targetSwitch := generateKeySwitchKey q lweDimension (ringRank * degree)
      keySwitchLevels keySwitchWideNoise keySwitchGadget
      (keyExtract secretPair.2) secretPair.1
    let tape := TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
      (embedBinarySecret secretPair.1) 0
    let residualAux := TFHE.SamplerReplacement.independentPair residualSwitch tape
      (fun keySwitchKey inputTape ↦ (keySwitchKey, inputTape))
    let targetAux := TFHE.SamplerReplacement.independentPair targetSwitch tape
      (fun keySwitchKey inputTape ↦ (keySwitchKey, inputTape))
    have haux : tvDist residualAux targetAux ≤ bound := by
      have hpair := TFHE.SamplerReplacement.tvDist_independentPair_le
        residualSwitch targetSwitch tape tape
        (fun keySwitchKey inputTape ↦ (keySwitchKey, inputTape))
      have hswitch :=
        ConditionalSmudging.tvDist_generateResidualKeySwitchKey_generateKeySwitchKey_le
          q degree ringRank lweDimension keySwitchLevels keySwitchWideNoise
          keySwitchGadget secretPair.2 secretPair.1 (keySwitchResidual secretPair)
      exact hpair.trans (by
        rw [tvDist_self, add_zero]
        exact hswitch.trans (hbound secretPair))
    have hview := TFHE.SamplerReplacement.tvDist_independentPair_le
      uniformBootstrap uniformBootstrap residualAux targetAux
      (fun bootstrappingKey auxiliary ↦ (bootstrappingKey, auxiliary))
    have hview' := hview.trans (by
      simpa only [tvDist_self, zero_add] using haux)
    simpa [residualContinuation, targetContinuation, uniformBootstrap,
      residualSwitch, targetSwitch, tape, residualAux, targetAux,
      TFHE.SamplerReplacement.independentPair, monad_norm] using hview'
  have h := tvDist_bind_left_le_const' secrets residualContinuation
    targetContinuation bound hcontinuation
  rw [← freshUniformView_eq_uniformPublicView
    (ringRank := ringRank) (lweDimension := lweDimension)
    (tgswLevels := tgswLevels) (queryCount := queryCount)
    ringWideNoise keySwitchWideNoise inputErrorSampler tgswGadget keySwitchGadget]
  simpa [freshResidualUniformView, freshUniformView, secrets,
    residualContinuation, targetContinuation] using h

/-! ## Averaged residual normal forms over the augmented source -/

/-- Correct residual endpoint averaged over the original augmented coordinate source. -/
noncomputable def averagedResidualRealView
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (ringResidual : Bool →
      Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
      Secret lweDimension ringRank degree →
      ConditionalSmudging.BootstrappingResidual
        q degree ringRank tgswLevels lweDimension)
    (keySwitchResidual : Bool →
      Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
      Secret lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels) :
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let hiddenAndContext ← coordinateSource (ringRank := ringRank) (queryCount := queryCount)
    sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget coordinate
  freshResidualRealView (ringRank := ringRank) (queryCount := queryCount)
    targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget
    (ringResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
    (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)

/-- Sampled correct residual endpoint averaged over the original augmented coordinate source. -/
noncomputable def averagedSampledResidualRealView
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (residualSampler : Bool →
      Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
      Secret lweDimension ringRank degree →
      ProbComp (EvaluationKeyResidual q degree ringRank tgswLevels
        lweDimension keySwitchLevels)) :
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let hiddenAndContext ← coordinateSource (ringRank := ringRank) (queryCount := queryCount)
    sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget coordinate
  freshSampledResidualRealView (ringRank := ringRank) (queryCount := queryCount)
    targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget
    (residualSampler hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)

/-- Wrong residual endpoint averaged over the original augmented coordinate source. -/
noncomputable def averagedResidualUniformView
    (sourceRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (keySwitchResidual : Bool →
      Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
      Secret lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels) :
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let hiddenAndContext ← coordinateSource (ringRank := ringRank) (queryCount := queryCount)
    sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget coordinate
  freshResidualUniformView (ringRank := ringRank) (tgswLevels := tgswLevels)
    (queryCount := queryCount) targetKeySwitchErrorSampler inputErrorSampler
    keySwitchGadget
    (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)

/-- Averaged correct residual form is close to the augmented target real endpoint. -/
theorem tvDist_averagedResidualRealView_realPublicView_le
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (ringResidual : Bool →
      Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
      Secret lweDimension ringRank degree →
      ConditionalSmudging.BootstrappingResidual
        q degree ringRank tgswLevels lweDimension)
    (keySwitchResidual : Bool →
      Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
      Secret lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels)
    (bound : ℝ)
    (hbound : ∀ hiddenAndContext,
      hiddenAndContext ∈ support
        (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
          sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget coordinate) →
      ∀ secrets,
        ConditionalSmudging.evaluationKeySmudgingCost
            targetRingErrorSampler targetKeySwitchErrorSampler
            (ringResidual hiddenAndContext.1 hiddenAndContext.2.1
              hiddenAndContext.2.2 secrets)
            (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1
              hiddenAndContext.2.2 secrets) ≤ bound) :
    tvDist
        (averagedResidualRealView (ringRank := ringRank) (queryCount := queryCount)
          sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
          targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
          coordinate ringResidual keySwitchResidual)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler targetKeySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget) ≤ bound := by
  let source := coordinateSource (ringRank := ringRank) (queryCount := queryCount)
    sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget coordinate
  let target := realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) targetRingErrorSampler targetKeySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget
  let residualView := fun hiddenAndContext : Bool ×
      PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount ↦
    freshResidualRealView (ringRank := ringRank) (queryCount := queryCount)
      targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget
      (ringResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
      (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
  have hmix := tvDist_bind_left_le_const source residualView (fun _ ↦ target) bound
    (fun hiddenAndContext hsupport ↦
      tvDist_freshResidualRealView_realPublicView_le
        (ringRank := ringRank) (queryCount := queryCount)
        targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget
        (ringResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
        (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
        bound (hbound hiddenAndContext hsupport))
  have htarget : evalDist (source >>= fun _ ↦ target) = evalDist target :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      source (by simp [source, coordinateSource, scalarSource]) target
  unfold tvDist at hmix ⊢
  rw [htarget] at hmix
  simpa [averagedResidualRealView, source, residualView, target] using hmix

/-- Averaged sampled residuals are close to the augmented target real endpoint. -/
theorem tvDist_averagedSampledResidualRealView_realPublicView_le
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (residualSampler : Bool →
      Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
      Secret lweDimension ringRank degree →
      ProbComp (EvaluationKeyResidual q degree ringRank tgswLevels
        lweDimension keySwitchLevels))
    (bound : ℝ)
    (hTotal : ∀ hiddenAndContext,
      hiddenAndContext ∈ support
        (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
          sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget coordinate) →
      ∀ secrets,
        probFailure (residualSampler hiddenAndContext.1 hiddenAndContext.2.1
          hiddenAndContext.2.2 secrets) = 0)
    (hbound : ∀ hiddenAndContext,
      hiddenAndContext ∈ support
        (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
          sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget coordinate) →
      ∀ secrets residual,
        residual ∈ support
          (residualSampler hiddenAndContext.1 hiddenAndContext.2.1
            hiddenAndContext.2.2 secrets) →
        ConditionalSmudging.evaluationKeySmudgingCost
            targetRingErrorSampler targetKeySwitchErrorSampler
            residual.1 residual.2 ≤ bound) :
    tvDist
        (averagedSampledResidualRealView (ringRank := ringRank)
          (queryCount := queryCount) sourceRingErrorSampler targetRingErrorSampler
          sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget coordinate residualSampler)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler targetKeySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget) ≤ bound := by
  let source := coordinateSource (ringRank := ringRank) (queryCount := queryCount)
    sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget coordinate
  let target := realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) targetRingErrorSampler targetKeySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget
  let residualView := fun hiddenAndContext : Bool ×
      PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount ↦
    freshSampledResidualRealView (ringRank := ringRank) (queryCount := queryCount)
      targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget
      (residualSampler hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
  have hmix := tvDist_bind_left_le_const source residualView (fun _ ↦ target) bound
    (fun hiddenAndContext hsupport ↦
      tvDist_freshSampledResidualRealView_realPublicView_le
        (ringRank := ringRank) (queryCount := queryCount)
        targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget
        (residualSampler hiddenAndContext.1 hiddenAndContext.2.1
          hiddenAndContext.2.2)
        bound (hTotal hiddenAndContext hsupport)
        (hbound hiddenAndContext hsupport))
  have htarget : evalDist (source >>= fun _ ↦ target) = evalDist target :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      source (by simp [source, coordinateSource, scalarSource]) target
  unfold tvDist at hmix ⊢
  rw [htarget] at hmix
  simpa [averagedSampledResidualRealView, source, residualView, target] using hmix

/-- Averaged wrong residual form is close to the augmented uniform-BRK endpoint. -/
theorem tvDist_averagedResidualUniformView_uniformPublicView_le
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (keySwitchResidual : Bool →
      Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
      Secret lweDimension ringRank degree →
      ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels)
    (bound : ℝ)
    (hbound : ∀ hiddenAndContext,
      hiddenAndContext ∈ support
        (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
          sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget coordinate) →
      ∀ secrets,
        ConditionalSmudging.keySwitchSmudgingCost targetKeySwitchErrorSampler
          (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1
            hiddenAndContext.2.2 secrets) ≤ bound) :
    tvDist
        (averagedResidualUniformView (ringRank := ringRank)
          (lweDimension := lweDimension) (queryCount := queryCount)
          sourceRingErrorSampler sourceKeySwitchErrorSampler targetKeySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget coordinate keySwitchResidual)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler targetKeySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget) ≤ bound := by
  let source := coordinateSource (ringRank := ringRank) (queryCount := queryCount)
    sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget coordinate
  let target := uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) targetRingErrorSampler targetKeySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget
  let residualView := fun hiddenAndContext : Bool ×
      PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount ↦
    freshResidualUniformView (ringRank := ringRank) (tgswLevels := tgswLevels)
      (queryCount := queryCount) targetKeySwitchErrorSampler inputErrorSampler
      keySwitchGadget
      (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
  have hmix := tvDist_bind_left_le_const source residualView (fun _ ↦ target) bound
    (fun hiddenAndContext hsupport ↦
      tvDist_freshResidualUniformView_uniformPublicView_le
        (ringRank := ringRank) (lweDimension := lweDimension)
        (tgswLevels := tgswLevels) (queryCount := queryCount)
        targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget
        (keySwitchResidual hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2)
        bound (hbound hiddenAndContext hsupport))
  have htarget : evalDist (source >>= fun _ ↦ target) = evalDist target :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      source (by simp [source, coordinateSource, scalarSource]) target
  unfold tvDist at hmix ⊢
  rw [htarget] at hmix
  simpa [averagedResidualUniformView, source, residualView, target] using hmix

/-! ## Adapter to augmented candidate recovery -/

/-- Scheme-specific shifted evaluator whose residual normal forms hold after averaging over the
complete augmented coordinate source, including the same-secret input tape. -/
structure AveragedResidualCandidateViewTransformer
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler :
      ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  transform : Fin lweDimension → Bool →
    Challenge q degree ringRank tgswLevels lweDimension →
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)
  correctRingResidual : Fin lweDimension → Bool →
    Challenge q degree ringRank tgswLevels lweDimension →
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
    Secret lweDimension ringRank degree →
    ConditionalSmudging.BootstrappingResidual
      q degree ringRank tgswLevels lweDimension
  correctKeySwitchResidual : Fin lweDimension → Bool →
    Challenge q degree ringRank tgswLevels lweDimension →
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
    Secret lweDimension ringRank degree →
    ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels
  wrongKeySwitchResidual : Fin lweDimension → Bool →
    Challenge q degree ringRank tgswLevels lweDimension →
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
    Secret lweDimension ringRank degree →
    ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels
  correctError : Fin lweDimension → ℝ
  wrongError : Fin lweDimension → ℝ
  correctError_nonneg : ∀ coordinate, 0 ≤ correctError coordinate
  wrongError_nonneg : ∀ coordinate, 0 ≤ wrongError coordinate
  correctNormalForm : ∀ coordinate,
    evalDist (do
        let hiddenAndContext ← coordinateSource (ringRank := ringRank)
          (queryCount := queryCount) sourceRingErrorSampler sourceKeySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget coordinate
        transform coordinate hiddenAndContext.1 hiddenAndContext.2.1
          hiddenAndContext.2.2) =
      evalDist
        (averagedResidualRealView (ringRank := ringRank) (queryCount := queryCount)
          sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
          targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
          coordinate (correctRingResidual coordinate)
          (correctKeySwitchResidual coordinate))
  wrongNormalForm : ∀ coordinate,
    evalDist (do
        let hiddenAndContext ← coordinateSource (ringRank := ringRank)
          (queryCount := queryCount) sourceRingErrorSampler sourceKeySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget coordinate
        transform coordinate (!hiddenAndContext.1) hiddenAndContext.2.1
          hiddenAndContext.2.2) =
      evalDist
        (averagedResidualUniformView (ringRank := ringRank)
          (lweDimension := lweDimension) (queryCount := queryCount)
          sourceRingErrorSampler sourceKeySwitchErrorSampler targetKeySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget coordinate
          (wrongKeySwitchResidual coordinate))
  correctCost_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget coordinate) →
    ∀ secrets,
      ConditionalSmudging.evaluationKeySmudgingCost
          targetRingErrorSampler targetKeySwitchErrorSampler
          (correctRingResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets)
          (correctKeySwitchResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets) ≤
        correctError coordinate
  wrongCost_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget coordinate) →
    ∀ secrets,
      ConditionalSmudging.keySwitchSmudgingCost targetKeySwitchErrorSampler
          (wrongKeySwitchResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets) ≤
        wrongError coordinate

namespace AveragedResidualCandidateViewTransformer

/-- Residual normal forms discharge the generic averaged augmented-view distance contract. -/
noncomputable def toAveraged
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler :
      ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedResidualCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget) :
    AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget where
  transform := transformer.transform
  correctError := transformer.correctError
  wrongError := transformer.wrongError
  correctError_nonneg := transformer.correctError_nonneg
  wrongError_nonneg := transformer.wrongError_nonneg
  correctDistance := by
    intro coordinate
    unfold tvDist
    rw [transformer.correctNormalForm coordinate]
    simpa only [tvDist] using
      (tvDist_averagedResidualRealView_realPublicView_le
        (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
        targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
        coordinate (transformer.correctRingResidual coordinate)
        (transformer.correctKeySwitchResidual coordinate)
        (transformer.correctError coordinate)
        (transformer.correctCost_le coordinate))
  wrongDistance := by
    intro coordinate
    unfold tvDist
    rw [transformer.wrongNormalForm coordinate]
    simpa only [tvDist] using
      (tvDist_averagedResidualUniformView_uniformPublicView_le
        (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) sourceRingErrorSampler targetRingErrorSampler
        sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget coordinate
        (transformer.wrongKeySwitchResidual coordinate)
        (transformer.wrongError coordinate)
        (transformer.wrongCost_le coordinate))

end AveragedResidualCandidateViewTransformer

/-- Complete augmented residual-evaluator certificate, including shared-context amplification
parameters and a nonnegative effective decision gap. -/
structure AveragedResidualCandidateViewTransformerReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount
      ringEta keySwitchEta : ℕ)
    [NeZero q]
    (inputErrorSampler : ProbComp (ZMod q))
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toTransformer :
    PublicDistinguisher q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount →
    AveragedResidualCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      (RLWE.CenteredBinomial.sampler q degree ringEta) targetRingErrorSampler
      (CenteredBinomial.scalarSampler q keySwitchEta) targetKeySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget
  rounds : PublicDistinguisher q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount → Fin lweDimension → ℕ
  threshold : PublicDistinguisher q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount → Fin lweDimension → ENNReal
  threshold_pos : ∀ distinguisher coordinate, 0 < threshold distinguisher coordinate
  threshold_le_one : ∀ distinguisher coordinate, threshold distinguisher coordinate ≤ 1

namespace AveragedResidualCandidateViewTransformerReduction

/-- Forget residual witnesses only after using them to prove the generic augmented distances. -/
noncomputable def toAveragedReduction
    {ringEta keySwitchEta : ℕ}
    {inputErrorSampler : ProbComp (ZMod q)}
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedResidualCandidateViewTransformerReduction q degree ringRank
      tgswLevels lweDimension keySwitchLevels queryCount ringEta keySwitchEta
      inputErrorSampler targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget) :
    AveragedCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount ringEta keySwitchEta inputErrorSampler
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget where
  toTransformer := fun distinguisher ↦
    (reduction.toTransformer distinguisher).toAveraged
  rounds := reduction.rounds
  threshold := reduction.threshold
  threshold_pos := reduction.threshold_pos
  threshold_le_one := reduction.threshold_le_one

/-- Averaged residual evaluation yields the full scalar-secret reduction. -/
noncomputable def toScalarSecretReduction
    {ringEta keySwitchEta : ℕ}
    {inputErrorSampler : ProbComp (ZMod q)}
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedResidualCandidateViewTransformerReduction q degree ringRank
      tgswLevels lweDimension keySwitchLevels queryCount ringEta keySwitchEta
      inputErrorSampler targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget) :
    ScalarSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      queryCount ringEta keySwitchEta inputErrorSampler targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget :=
  reduction.toAveragedReduction.toScalarSecretReduction

/-- A centered-binomial KSK decoding margin upgrades the scalar reduction to paired recovery. -/
noncomputable def toPairedSecretReduction
    {ringEta keySwitchEta : ℕ}
    {inputErrorSampler : ProbComp (ZMod q)}
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedResidualCandidateViewTransformerReduction q degree ringRank
      tgswLevels lweDimension keySwitchLevels queryCount ringEta keySwitchEta
      inputErrorSampler targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    PairedSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      queryCount ringEta keySwitchEta inputErrorSampler targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget :=
  reduction.toScalarSecretReduction.toPairedSecretReduction level hmargin

/-- Narrow paired-search hardness transfers to the public augmented CircLWE game through the
residual evaluator, thresholded amplification, and exact KSK completion. -/
theorem publicHardAgainst_of_search
    {ringEta keySwitchEta : ℕ}
    (inputErrorSampler : ProbComp (ZMod q))
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reduction : AveragedResidualCandidateViewTransformerReduction q degree ringRank
      tgswLevels lweDimension keySwitchLevels queryCount ringEta keySwitchEta
      inputErrorSampler targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (decisionAllowed : PublicDistinguisher q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount → Prop)
    (solverAllowed : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount → Prop)
    (searchBound lossBound : ℝ)
    (hSearch : LWE.AuxiliaryInput.SearchToDecision.RealSearchHardAgainst
      (problem (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount)
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        inputErrorSampler tgswGadget keySwitchGadget)
      solverAllowed searchBound)
    (hClosed : ∀ distinguisher, decisionAllowed distinguisher →
      solverAllowed ((reduction.toPairedSecretReduction level hmargin).toSolver
        distinguisher))
    (hLoss : ∀ distinguisher, decisionAllowed distinguisher →
      (reduction.toPairedSecretReduction level hmargin).loss distinguisher ≤ lossBound) :
    LWE.AuxiliaryInput.SearchToDecision.PublicHardAgainst
      (KeySwitchFirstFiniteView.augmentedCircularProblem
        (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) targetRingErrorSampler
        targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
      decisionAllowed (searchBound + lossBound) :=
  ScalarSecretReduction.publicHardAgainst_of_search
    inputErrorSampler targetRingErrorSampler targetKeySwitchErrorSampler
    tgswGadget keySwitchGadget reduction.toScalarSecretReduction level hmargin
    decisionAllowed solverAllowed searchBound lossBound hSearch hClosed hLoss

end AveragedResidualCandidateViewTransformerReduction

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual
