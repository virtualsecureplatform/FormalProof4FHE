/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveKeySwitchFirstFiniteViewNativeCircular
import FormalProof4FHE.TFHE.AuxiliaryInputZeroSecurity
import FormalProof4FHE.TFHE.ScalarSecretRandomization

/-!
# Public Auxiliary-Input CircLWE for Adaptive Native TFHE

A bounded adaptive encryption transcript is public side information once it has been sampled.
This module puts that observation on the exact native distributions used by TFHE.

First, scalar XOR masking transports the complete public view consisting of the BRK, KSK, and
zero-message input tape.  The BRK and KSK use the existing native evaluation-key transport; the
input tape uses the exact batch-TLWE transport.  Both the real centered-binomial endpoint and the
uniform-BRK endpoint are preserved with zero statistical loss.

Second, the adaptive real-to-zero BRK replacement is identified with a public augmented KDM
game.  The distinguisher receives `(BRK, KSK, tape)` and no hidden secret.  Consequently the
generic KDM triangle bounds the adaptive circular hop by a public augmented CircLWE term plus
its explicit zero-message auxiliary-input LWE term.  This avoids the secret-aware continuation
introduced by a same-secret batch hybrid.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular

open Native

namespace ScalarTransport

variable
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ}

/-- The public adaptive view in evaluation-key-pair-plus-tape layout. -/
abbrev View
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) :=
  (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension ×
      Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) ×
    KeySwitchFirstSecurity.InputTape q lweDimension queryCount

/-- Publicly XOR-transport the evaluation keys and the bounded TLWE input tape together. -/
noncomputable def transformView
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (mask : BinarySecret lweDimension)
    (view : View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) :
    View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  (Native.ScalarSecretRandomization.transformEvaluationKeyPair
      tgswGadget mask view.1,
    Native.ScalarSecretRandomization.transformBatch mask view.2)

/-- The complete adaptive-view transport is a public permutation. -/
theorem transformView_bijective
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (mask : BinarySecret lweDimension) :
    Function.Bijective
      (transformView (ringRank := ringRank) (keySwitchLevels := keySwitchLevels)
        (queryCount := queryCount)
        tgswGadget mask) := by
  change Function.Bijective (Prod.map
    (Native.ScalarSecretRandomization.transformEvaluationKeyPair
      (sourceDimension := ringRank * degree) (keySwitchLevels := keySwitchLevels)
      tgswGadget mask)
    (Native.ScalarSecretRandomization.transformBatch
      (R := ZMod q) (samples := queryCount) mask))
  exact
    (Native.ScalarSecretRandomization.transformEvaluationKeyPair_bijective
      (sourceDimension := ringRank * degree) (keySwitchLevels := keySwitchLevels)
      tgswGadget mask).prodMap
      (Native.ScalarSecretRandomization.transformBatch_bijective mask)

/-- A fixed-secret real centered-binomial evaluation-key view together with an independent
zero-message adaptive input tape under the same scalar secret. -/
noncomputable def sampleRealView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount ringEta : ℕ)
    [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    ProbComp
      (View q (degree + 1) ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let evaluationKeys ← Native.ScalarSecretRandomization.sampleRealEvaluationKeyPair
    q (degree + 1) ringRank tgswLevels lweDimension keySwitchLevels
    (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
    keySwitchErrorSampler tgswGadget keySwitchGadget lweSecret ringSecret
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret lweSecret) 0
  return (evaluationKeys, tape)

/-- A uniform BRK, real KSK, and zero-message input tape under one fixed scalar secret. -/
noncomputable def sampleUniformBootstrapView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ)
    [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp
      (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let evaluationKeys ←
    Native.ScalarSecretRandomization.sampleUniformBootstrapEvaluationKeyPair
      q degree ringRank tgswLevels lweDimension keySwitchLevels
      keySwitchErrorSampler keySwitchGadget lweSecret ringSecret
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret lweSecret) 0
  return (evaluationKeys, tape)

/-- Exact fixed-mask transport of the complete real adaptive public view.  In particular, adding
the bounded input tape introduces no extra smudging or statistical loss. -/
theorem transform_sampleRealView_centeredBinomial_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount ringEta : ℕ}
    [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist
        (transformView (queryCount := queryCount) tgswGadget mask <$>
          sampleRealView q degree ringRank tgswLevels lweDimension keySwitchLevels
            queryCount ringEta keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget lweSecret ringSecret) =
      evalDist
        (sampleRealView q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringEta keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget
          (Native.ScalarSecretRandomization.maskedSecret lweSecret mask) ringSecret) := by
  unfold sampleRealView transformView
  exact Native.ScalarSecretRandomization.independentPair_map_evalDist_congr _ _ _ _ _ _
    (Native.ScalarSecretRandomization.transform_realEvaluationKeyPair_centeredBinomial_evalDist
      keySwitchErrorSampler tgswGadget keySwitchGadget lweSecret mask ringSecret)
    (Native.ScalarSecretRandomization.transformBatch_batchEncrypt_evalDist
      inputErrorSampler lweSecret mask 0)

/-- Exact fixed-mask transport at the uniform-BRK endpoint, including the same bounded input
tape. -/
theorem transform_sampleUniformBootstrapView_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist
        (transformView (queryCount := queryCount) tgswGadget mask <$>
          sampleUniformBootstrapView q degree ringRank tgswLevels lweDimension
            keySwitchLevels queryCount keySwitchErrorSampler inputErrorSampler
            keySwitchGadget lweSecret ringSecret) =
      evalDist
        (sampleUniformBootstrapView q degree ringRank tgswLevels lweDimension
          keySwitchLevels queryCount keySwitchErrorSampler inputErrorSampler
          keySwitchGadget
          (Native.ScalarSecretRandomization.maskedSecret lweSecret mask) ringSecret) := by
  unfold sampleUniformBootstrapView transformView
  exact Native.ScalarSecretRandomization.independentPair_map_evalDist_congr _ _ _ _ _ _
    (Native.ScalarSecretRandomization.transform_uniformBootstrapEvaluationKeyPair_evalDist
      keySwitchErrorSampler tgswGadget keySwitchGadget lweSecret mask ringSecret)
    (Native.ScalarSecretRandomization.transformBatch_batchEncrypt_evalDist
      inputErrorSampler lweSecret mask 0)

/-- Mask a fixed scalar key and transport its complete real adaptive public view. -/
noncomputable def sampleMaskedRealView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount ringEta : ℕ)
    [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    ProbComp (BinarySecret lweDimension ×
      View q (degree + 1) ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let mask ← $ᵗ BinarySecret lweDimension
  let view ← sampleRealView q degree ringRank tgswLevels lweDimension
    keySwitchLevels queryCount ringEta keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget lweSecret ringSecret
  return (Native.ScalarSecretRandomization.maskedSecret lweSecret mask,
      transformView (ringRank := ringRank) tgswGadget mask view)

/-- Sample a fresh uniform scalar key and its complete real adaptive public view. -/
noncomputable def sampleFreshRealView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount ringEta : ℕ)
    [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    ProbComp (BinarySecret lweDimension ×
      View q (degree + 1) ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let freshSecret ← $ᵗ BinarySecret lweDimension
  let view ← sampleRealView q degree ringRank tgswLevels lweDimension
    keySwitchLevels queryCount ringEta keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget freshSecret ringSecret
  return (freshSecret, view)

/-- Uniform scalar masking of a fixed real adaptive view gives a fresh uniform scalar secret and
its complete correlated BRK+KSK+tape view. -/
theorem sampleMaskedRealView_centeredBinomial_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount ringEta : ℕ}
    [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist
        (sampleMaskedRealView q degree ringRank tgswLevels lweDimension
          keySwitchLevels queryCount ringEta keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget lweSecret ringSecret) =
      evalDist
        (sampleFreshRealView q degree ringRank tgswLevels lweDimension
          keySwitchLevels queryCount ringEta keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget ringSecret) := by
  unfold sampleMaskedRealView sampleFreshRealView
  exact Native.ScalarSecretRandomization.sampleMaskedView_evalDist lweSecret
    (fun freshSecret ↦ sampleRealView q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount ringEta keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget freshSecret ringSecret)
    (transformView (ringRank := ringRank) tgswGadget)
    (fun mask ↦ transform_sampleRealView_centeredBinomial_evalDist
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
      lweSecret mask ringSecret)

/-- Mask a fixed scalar key at the uniform-BRK endpoint, retaining the real KSK and tape. -/
noncomputable def sampleMaskedUniformBootstrapView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ)
    [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (BinarySecret lweDimension ×
      View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let mask ← $ᵗ BinarySecret lweDimension
  let view ← sampleUniformBootstrapView q degree ringRank tgswLevels lweDimension
    keySwitchLevels queryCount keySwitchErrorSampler inputErrorSampler
    keySwitchGadget lweSecret ringSecret
  return (Native.ScalarSecretRandomization.maskedSecret lweSecret mask,
      transformView (ringRank := ringRank) tgswGadget mask view)

/-- Sample a fresh uniform scalar key at the uniform-BRK endpoint. -/
noncomputable def sampleFreshUniformBootstrapView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ)
    [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (BinarySecret lweDimension ×
      View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let freshSecret ← $ᵗ BinarySecret lweDimension
  let view ← sampleUniformBootstrapView q degree ringRank tgswLevels lweDimension
    keySwitchLevels queryCount keySwitchErrorSampler inputErrorSampler
    keySwitchGadget freshSecret ringSecret
  return (freshSecret, view)

/-- Uniform scalar masking is equally exact at the uniform-BRK endpoint with the adaptive tape. -/
theorem sampleMaskedUniformBootstrapView_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree) :
    evalDist
        (sampleMaskedUniformBootstrapView q degree ringRank tgswLevels lweDimension
          keySwitchLevels queryCount keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget lweSecret ringSecret) =
      evalDist
        (sampleFreshUniformBootstrapView q degree ringRank tgswLevels lweDimension
          keySwitchLevels queryCount keySwitchErrorSampler inputErrorSampler
          keySwitchGadget ringSecret) := by
  unfold sampleMaskedUniformBootstrapView sampleFreshUniformBootstrapView
  exact Native.ScalarSecretRandomization.sampleMaskedView_evalDist lweSecret
    (fun freshSecret ↦ sampleUniformBootstrapView q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount keySwitchErrorSampler inputErrorSampler
      keySwitchGadget freshSecret ringSecret)
    (transformView (ringRank := ringRank) tgswGadget)
    (fun mask ↦ transform_sampleUniformBootstrapView_evalDist
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
      lweSecret mask ringSecret)

end ScalarTransport

variable {Message : Type}
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]

/-- Public distinguishers for one augmented `(BRK, KSK, tape)` CircLWE view. -/
abbrev PublicDistinguisher
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) :=
  LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
    (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
    (KeySwitchFirstFiniteView.CircularBatchAuxiliary
      q ringRank degree lweDimension keySwitchLevels queryCount)

/-- Reassociate the existing curried adaptive public distinguisher as a generic augmented
auxiliary-input distinguisher. -/
def bundleDistinguisher
    (distinguisher : KeySwitchFirstSecurity.PublicDistinguisher
      q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) :
    PublicDistinguisher q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount :=
  fun bootstrapKey auxiliary ↦
    distinguisher bootstrapKey auxiliary.1 auxiliary.2

/-- The public continuation embedding; neither component of the hidden native key is exposed. -/
def publicContinuation
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    LWE.AuxiliaryInput.Continuation
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
        lweDimension ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchFirstFiniteView.CircularBatchAuxiliary
        q ringRank degree lweDimension keySwitchLevels queryCount) :=
  LWE.AuxiliaryInput.SearchToDecision.publicContinuation distinguisher

/-- The zero-message BRK endpoint with the real KSK and bounded zero-message input tape. -/
noncomputable def zeroDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : KeySwitchFirstSecurity.PublicDistinguisher
      q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) : ProbComp Bool := do
  let lweSecret ← sampleLweSecret lweDimension
  let ringSecret ← sampleRingSecret ringRank degree
  let bootstrapKey ← generateZeroBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget ringSecret
  let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
    keySwitchLevels keySwitchErrorSampler keySwitchGadget
    (keyExtract ringSecret) lweSecret
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret lweSecret) 0
  distinguisher bootstrapKey keySwitchKey tape

/-- The real branch of the public augmented problem is exactly the existing adaptive public
decision experiment. -/
theorem augmentedRealGame_evalDist_eq_realDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : KeySwitchFirstSecurity.PublicDistinguisher
      q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) :
    evalDist
        (LWE.AuxiliaryInput.realGame
          (KeySwitchFirstFiniteView.augmentedCircularProblem
            ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget)
          (publicContinuation (bundleDistinguisher distinguisher))) =
      evalDist
        (KeySwitchFirstSecurity.realDecisionGame (queryCount := queryCount)
          ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher) := by
  simp only [LWE.AuxiliaryInput.realGame,
    KeySwitchFirstFiniteView.augmentedCircularProblem,
    KeySwitchFirstFiniteView.secretSampler, publicContinuation,
    LWE.AuxiliaryInput.SearchToDecision.publicContinuation,
    bundleDistinguisher, KeySwitchFirstSecurity.realDecisionGame,
    bind_assoc, pure_bind]
  refine evalDist_bind_congr' (sampleLweSecret lweDimension) fun lweSecret ↦ ?_
  refine evalDist_bind_congr' (sampleRingSecret ringRank degree) fun ringSecret ↦ ?_
  have hbootstrap :
      evalDist
          (Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
            q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
            lweSecret ringSecret) =
        evalDist
          (Native.generateBootstrappingKey
            q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
            lweSecret ringSecret) := by
    rw [Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey_eq_direct]
    exact
      (Native.BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct
        q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
        lweSecret ringSecret).symm
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hbootstrap (fun bootstrapKey ↦ do
      let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract ringSecret) lweSecret
      let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
        (embedBinarySecret lweSecret) 0
      distinguisher bootstrapKey keySwitchKey tape)

/-- The zero branch of the public augmented problem is definitionally the zero-BRK adaptive
decision endpoint. -/
theorem augmentedZeroGame_evalDist_eq_zeroDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : KeySwitchFirstSecurity.PublicDistinguisher
      q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) :
    evalDist
        (LWE.AuxiliaryInput.zeroGame
          (KeySwitchFirstFiniteView.augmentedCircularProblem
            ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget)
          (publicContinuation (bundleDistinguisher distinguisher))) =
      evalDist
        (zeroDecisionGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher) := by
  simp [LWE.AuxiliaryInput.zeroGame,
    KeySwitchFirstFiniteView.augmentedCircularProblem,
    KeySwitchFirstFiniteView.secretSampler, publicContinuation,
    LWE.AuxiliaryInput.SearchToDecision.publicContinuation,
    bundleDistinguisher, zeroDecisionGame, bind_assoc, monad_norm]

/-- Public augmented real-versus-uniform CircLWE advantage. -/
noncomputable def publicCircularLweAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ℝ :=
  LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
    (KeySwitchFirstFiniteView.augmentedCircularProblem
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget)
    distinguisher

/-- Public zero-message-versus-uniform advantage with the same KSK and input-tape auxiliary. -/
noncomputable def publicZeroLweAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ℝ :=
  LWE.AuxiliaryInput.zeroLweAdvantage
    (KeySwitchFirstFiniteView.augmentedCircularProblem
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget)
    (publicContinuation distinguisher)

/-- Public real-versus-zero augmented KDM advantage. -/
noncomputable def publicKdmAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ℝ :=
  LWE.AuxiliaryInput.kdmAdvantage
    (KeySwitchFirstFiniteView.augmentedCircularProblem
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget)
    (publicContinuation distinguisher)

/-- The generic public KDM triangle specialized to the complete adaptive auxiliary input. -/
theorem publicKdmAdvantage_le_circular_add_zero
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    publicKdmAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher ≤
      publicCircularLweAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher +
        publicZeroLweAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher := by
  exact LWE.AuxiliaryInput.kdmAdvantage_le_circularLwe_add_zeroLwe _ _

/-! ## Exact bridge to the bounded adaptive encryption experiment -/

/-- The honest adaptive game is the real branch of the public augmented problem. -/
theorem adaptiveRealGame_evalDist_eq_augmentedRealGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist
        (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary) =
      evalDist
        (LWE.AuxiliaryInput.realGame
          (KeySwitchFirstFiniteView.augmentedCircularProblem
            ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget)
          (publicContinuation
            (bundleDistinguisher
              (KeySwitchFirstSecurity.toPublicDistinguisher
                (queryCount := queryCount) encode adversary)))) := by
  calc
    _ = evalDist
        (KeySwitchFirstSecurity.realDecisionGame (queryCount := queryCount)
          ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget
          (KeySwitchFirstSecurity.toPublicDistinguisher
            (queryCount := queryCount) encode adversary)) :=
      KeySwitchFirstSecurity.realGame_evalDist_eq_realDecisionGame
        queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary
    _ = _ := (augmentedRealGame_evalDist_eq_realDecisionGame
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget
      (KeySwitchFirstSecurity.toPublicDistinguisher
        (queryCount := queryCount) encode adversary)).symm

/-- The adaptive zero-BRK hybrid is the zero branch of the same public augmented problem. -/
theorem adaptiveBootstrapZeroGame_evalDist_eq_augmentedZeroGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist
        (Adaptive.bootstrapZeroGame queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary) =
      evalDist
        (LWE.AuxiliaryInput.zeroGame
          (KeySwitchFirstFiniteView.augmentedCircularProblem
            ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget)
          (publicContinuation
            (bundleDistinguisher
              (KeySwitchFirstSecurity.toPublicDistinguisher
                (queryCount := queryCount) encode adversary)))) := by
  calc
    _ = evalDist
        (zeroDecisionGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget
          (KeySwitchFirstSecurity.toPublicDistinguisher
            (queryCount := queryCount) encode adversary)) := by
      rfl
    _ = _ := (augmentedZeroGame_evalDist_eq_zeroDecisionGame
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget
      (KeySwitchFirstSecurity.toPublicDistinguisher
        (queryCount := queryCount) encode adversary)).symm

/-- The public augmented uniform-BRK branch is exactly the adaptive zero-BRK game obtained by
using uniform ring errors. -/
theorem augmentedUniformGame_evalDist_eq_uniformErrorBootstrapZeroGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist
        (LWE.AuxiliaryInput.uniformGame
          (KeySwitchFirstFiniteView.augmentedCircularProblem
            ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget)
          (publicContinuation
            (bundleDistinguisher
              (KeySwitchFirstSecurity.toPublicDistinguisher
                (queryCount := queryCount) encode adversary)))) =
      evalDist
        (Adaptive.bootstrapZeroGame queryCount ($ᵗ (RLWE.Rq q degree))
          keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
          encode adversary) := by
  simp only [LWE.AuxiliaryInput.uniformGame,
    KeySwitchFirstFiniteView.augmentedCircularProblem,
    KeySwitchFirstFiniteView.secretSampler, publicContinuation,
    LWE.AuxiliaryInput.SearchToDecision.publicContinuation,
    bundleDistinguisher, Adaptive.bootstrapZeroGame,
    Circular.bootstrapZeroContinuationGame, Native.nativeCycleSpec,
    Adaptive.continuation, KeySwitchFirstSecurity.toPublicDistinguisher,
    bind_assoc, pure_bind]
  refine evalDist_bind_congr' (sampleLweSecret lweDimension) fun lweSecret ↦ ?_
  refine evalDist_bind_congr' (sampleRingSecret ringRank degree) fun ringSecret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (Native.BootstrapCutSecurity.generateZeroBootstrappingKey_uniformError_evalDist
      q degree ringRank tgswLevels lweDimension tgswGadget ringSecret).symm
    (fun bootstrapKey ↦ do
      let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract ringSecret) lweSecret
      let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
        (embedBinarySecret lweSecret) 0
      let bit ← $ᵗ Bool
      let guess ← Adaptive.runFromTranscript bit encode adversary
        ⟨bootstrapKey, keySwitchKey⟩ tape
      return (bit == guess))

/-- The public zero-side term induced by a bounded adaptive adversary costs two conventional
joint-LWE advantages: one with the actual zero-BRK context and one with the exactly uniform BRK
context. -/
theorem publicZeroLweAdvantage_toPublic_le_two_jointLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    publicZeroLweAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget
        (bundleDistinguisher
          (KeySwitchFirstSecurity.toPublicDistinguisher
            (queryCount := queryCount) encode adversary)) ≤
      LearningWithErrors.advantage
        (Adaptive.jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (Adaptive.keySwitchMessageReduction ringErrorSampler
          keySwitchErrorSampler inputErrorSampler tgswGadget
          (Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary) +
      LearningWithErrors.advantage
        (Adaptive.jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (Adaptive.keySwitchMessageReduction ($ᵗ (RLWE.Rq q degree))
          keySwitchErrorSampler inputErrorSampler tgswGadget
          (Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary) := by
  rw [← Adaptive.abs_signedAdvantage_bootstrapZero_eq_jointLwe queryCount
      ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
      encode adversary hbound,
    ← Adaptive.abs_signedAdvantage_bootstrapZero_eq_jointLwe queryCount
      ($ᵗ (RLWE.Rq q degree)) keySwitchErrorSampler inputErrorSampler tgswGadget
      keySwitchGadget encode adversary hbound]
  unfold publicZeroLweAdvantage LWE.AuxiliaryInput.zeroLweAdvantage
    ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (adaptiveBootstrapZeroGame_evalDist_eq_augmentedZeroGame queryCount
        ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        keySwitchGadget encode adversary).symm,
    probOutput_congr rfl
      (augmentedUniformGame_evalDist_eq_uniformErrorBootstrapZeroGame queryCount
        ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        keySwitchGadget encode adversary)]
  have h := abs_sub_le
    (Pr[= true | Adaptive.bootstrapZeroGame queryCount ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
      encode adversary]).toReal
    (1 / 2 : ℝ)
    (Pr[= true | Adaptive.bootstrapZeroGame queryCount ($ᵗ (RLWE.Rq q degree))
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
      encode adversary]).toReal
  rw [abs_sub_comm (1 / 2 : ℝ)] at h
  exact h

/-- The complete adaptive real-to-zero BRK replacement is exactly a public augmented KDM
advantage.  The continuation no longer receives either hidden secret. -/
theorem bootstrapReplacementAdvantage_eq_publicKdmAdvantage
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Adaptive.bootstrapReplacementAdvantage queryCount ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
        encode adversary =
      publicKdmAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget
        (bundleDistinguisher
          (KeySwitchFirstSecurity.toPublicDistinguisher
            (queryCount := queryCount) encode adversary)) := by
  unfold Adaptive.bootstrapReplacementAdvantage publicKdmAdvantage
    LWE.AuxiliaryInput.kdmAdvantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (adaptiveRealGame_evalDist_eq_augmentedRealGame queryCount ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
        encode adversary),
    probOutput_congr rfl
      (adaptiveBootstrapZeroGame_evalDist_eq_augmentedZeroGame queryCount
        ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        keySwitchGadget encode adversary)]

/-- The adaptive circular hop is bounded by public augmented CircLWE plus its explicit
zero-message auxiliary-input LWE branch. -/
theorem bootstrapReplacementAdvantage_le_publicCircular_add_zero
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Adaptive.bootstrapReplacementAdvantage queryCount ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
        encode adversary ≤
      publicCircularLweAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget
          (bundleDistinguisher
            (KeySwitchFirstSecurity.toPublicDistinguisher
              (queryCount := queryCount) encode adversary)) +
        publicZeroLweAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget
          (bundleDistinguisher
            (KeySwitchFirstSecurity.toPublicDistinguisher
              (queryCount := queryCount) encode adversary)) := by
  rw [bootstrapReplacementAdvantage_eq_publicKdmAdvantage queryCount
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
    keySwitchGadget encode adversary]
  exact publicKdmAdvantage_le_circular_add_zero
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget _

/-- **Finite adaptive TFHE security through a genuinely public circular premise.**

The honest bounded-query advantage is at most one public augmented CircLWE term, the matching
zero-message auxiliary-input LWE term, and the existing ordinary joint-LWE endpoint for the KSK
rows plus adaptive input rows. -/
theorem abs_signedAdvantage_real_le_publicCircular_add_zero_add_jointLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      publicCircularLweAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget
          (bundleDistinguisher
            (KeySwitchFirstSecurity.toPublicDistinguisher
              (queryCount := queryCount) encode adversary)) +
        publicZeroLweAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget
          (bundleDistinguisher
            (KeySwitchFirstSecurity.toPublicDistinguisher
              (queryCount := queryCount) encode adversary)) +
        LearningWithErrors.advantage
          (Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchErrorSampler inputErrorSampler)
          (Adaptive.keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget
            (Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary) := by
  have hAdaptive := Adaptive.abs_signedAdvantage_real_le_bootstrap_add_jointLwe
    queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary hbound
  have hCircular := bootstrapReplacementAdvantage_le_publicCircular_add_zero
    queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary
  linarith

/-- **Finite adaptive TFHE security with public augmented CircLWE as the only circular term.**

The public zero-side term is discharged by ordinary joint LWE.  The actual-context joint-LWE
reduction occurs once for the final adaptive endpoint and once in the zero-side triangle; the
uniform-BRK-context reduction occurs once. -/
theorem abs_signedAdvantage_real_le_publicCircular_add_two_jointLwe_add_uniformJointLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      publicCircularLweAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget
          (bundleDistinguisher
            (KeySwitchFirstSecurity.toPublicDistinguisher
              (queryCount := queryCount) encode adversary)) +
        2 * LearningWithErrors.advantage
          (Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchErrorSampler inputErrorSampler)
          (Adaptive.keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget
            (Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary) +
        LearningWithErrors.advantage
          (Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchErrorSampler inputErrorSampler)
          (Adaptive.keySwitchMessageReduction ($ᵗ (RLWE.Rq q degree))
            keySwitchErrorSampler inputErrorSampler tgswGadget
            (Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary) := by
  have hPublic := abs_signedAdvantage_real_le_publicCircular_add_zero_add_jointLwe
    queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary hbound
  have hZero := publicZeroLweAdvantage_toPublic_le_two_jointLwe
    queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary hbound
  linarith

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular
