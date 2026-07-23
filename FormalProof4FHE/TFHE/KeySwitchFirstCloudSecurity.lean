/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CutCycleSecurity
import FormalProof4FHE.TFHE.KeySwitchFirstFiniteView
import FormalProof4FHE.TFHE.KeySwitchSecurity

/-!
# Cloud-Key Security from the Finite KSK-First TFHE Reduction

This module composes the finite-view KSK-first search reduction with the two ordinary-LWE
replacement hops that remain after the KSK has been made uniform.  The cloud-key path is

* real BRK + real KSK;
* real BRK + uniform KSK;
* zero-message BRK + uniform KSK;
* zero-message BRK + zero-message KSK.

The first hop is the finite-batch paired-search obligation.  Once the KSK is uniform, the BRK
hop is an ordinary binary-secret batch module-LWE reduction.  After the BRK messages are zero,
the last KSK hop is one ordinary binary-secret batch-LWE reduction.

This is a cloud-key-only theorem.  A secret-dependent adaptive encryption continuation requires
the finite KSK-first challenge to include its bounded downstream transcript; that extension is
not claimed here.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.KeySwitchFirstCloudSecurity

open FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery
open FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstCandidateView
open FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstFiniteView

/-! ## Uniform zero-message key-switch keys -/

/-- A zero-message TLWE batch with uniform scalar errors is exactly uniform on the complete
batch carrier, for every fixed target secret. -/
theorem generateZeroKeySwitchKey_uniformError_evalDist
    (q targetDimension sourceDimension keySwitchLevels : ℕ) [NeZero q]
    (targetSecret : BinarySecret targetDimension) :
    evalDist (generateZeroKeySwitchKey q targetDimension sourceDimension keySwitchLevels
      ($ᵗ (ZMod q)) targetSecret) =
      evalDist ($ᵗ (KeySwitchKey q targetDimension sourceDimension keySwitchLevels)) := by
  let Samples := sourceDimension * keySwitchLevels
  let Challenge := Matrix (Fin targetDimension) (Fin Samples) (ZMod q)
  let Output := Fin Samples → ZMod q
  let challenges : ProbComp Challenge := $ᵗ Challenge
  let errors : ProbComp Output := ProbComp.sampleIID Samples ($ᵗ (ZMod q))
  have hErrors : evalDist errors = evalDist ($ᵗ Output) := by
    simpa [errors, Output, Samples] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := ZMod q) Samples)
  let shift : Challenge → Output := fun challenge ↦
    vecMul (embedBinarySecret targetSecret) challenge
  have hShift (challenge : Challenge) :
      evalDist (($ᵗ Output) >>= fun error ↦
        pure (challenge, shift challenge + error)) =
      evalDist (($ᵗ Output) >>= fun output ↦ pure (challenge, output)) := by
    have h := evalDist_bind_bijective_add_right_uniform
      (α := Output) (β := Output) id Function.bijective_id (shift challenge)
      (fun output ↦ (pure (challenge, output) : ProbComp (Challenge × Output)))
    change evalDist (($ᵗ Output) >>= fun error ↦
        pure (challenge, error + shift challenge)) =
      evalDist (($ᵗ Output) >>= fun output ↦ pure (challenge, output)) at h
    rw [show (fun error : Output ↦
        (pure (challenge, shift challenge + error) : ProbComp (Challenge × Output))) =
      fun error ↦ pure (challenge, error + shift challenge) by
        funext error
        rw [add_comm]]
    exact h
  have uniformProduct :
      ($ᵗ (Challenge × Output) : ProbComp (Challenge × Output)) =
        Prod.mk <$> ($ᵗ Challenge) <*> ($ᵗ Output) := rfl
  calc
    evalDist (generateZeroKeySwitchKey q targetDimension sourceDimension keySwitchLevels
        ($ᵗ (ZMod q)) targetSecret) =
      evalDist (challenges >>= fun challenge ↦
        errors >>= fun error ↦ pure (challenge, shift challenge + error)) := by
          simp [generateZeroKeySwitchKey, TLWE.batchEncrypt, TLWE.batchAssemble,
            challenges, errors, shift, Challenge, Output, Samples, monad_norm]
    _ = evalDist (challenges >>= fun challenge ↦
        ($ᵗ Output) >>= fun error ↦ pure (challenge, shift challenge + error)) := by
          refine evalDist_bind_congr' challenges fun challenge ↦ ?_
          exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
            hErrors (fun error ↦ pure (challenge, shift challenge + error))
    _ = evalDist (challenges >>= fun challenge ↦
        ($ᵗ Output) >>= fun output ↦ pure (challenge, output)) := by
          exact evalDist_bind_congr' challenges hShift
    _ = evalDist ($ᵗ (Challenge × Output)) := by
          rw [uniformProduct]
          simp [challenges, monad_norm]
    _ = evalDist ($ᵗ (KeySwitchKey q targetDimension sourceDimension keySwitchLevels)) := by
          rfl

/-! ## Cloud-key hybrid games -/

/-- The cloud-key-only adversary type used throughout this composition. -/
abbrev Adversary
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  Circular.Adversary Unit
    (BootstrappingKey q degree ringRank tgswLevels lweDimension)
    (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)

/-- Forget the unit payload and expose a cloud-key adversary as a native public distinguisher. -/
def toPublicDistinguisher
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    PublicDistinguisher q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun bootstrapKey keySwitchKey ↦ adversary ⟨(), bootstrapKey, keySwitchKey⟩

/-- Regard a cloud-key adversary as a cut-cycle continuation.  The scalar secret remains hidden
because this continuation ignores its secret argument. -/
def toCutContinuation
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    BootstrapCutSecurity.Continuation q degree ringRank tgswLevels lweDimension
      keySwitchLevels :=
  fun _ bootstrapKey keySwitchKey ↦ adversary ⟨(), bootstrapKey, keySwitchKey⟩

/-- The post-BRK-cut intermediate: a native zero-message BRK and an independent uniform KSK. -/
noncomputable def zeroBootstrapUniformKeySwitchGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    ProbComp Bool := do
  let _ ← sampleLweSecret lweDimension
  let ringSecret ← sampleRingSecret ringRank degree
  let bootstrapKey ← generateZeroBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget ringSecret
  let keySwitchKey ← $ᵗ (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
  adversary ⟨(), bootstrapKey, keySwitchKey⟩

/-- The structured native real cloud-key game and the direct-row real decision game have the
same output distribution. -/
theorem realGame_evalDist_eq_realDecisionGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    evalDist (Circular.realGame
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload adversary) =
      evalDist (realDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget (toPublicDistinguisher adversary)) := by
  simp only [Circular.realGame, Circular.realView, Circular.evaluationKeyOnlyPayload,
    nativeCycleSpec, realDecisionGame,
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.problem,
    LWE.AuxiliaryInput.Search.exactRecoveryProblem,
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.problem,
    toPublicDistinguisher, bind_assoc, pure_bind]
  refine evalDist_bind_congr' (sampleLweSecret lweDimension) fun lweSecret ↦ ?_
  refine evalDist_bind_congr' (sampleRingSecret ringRank degree) fun ringSecret ↦ ?_
  rw [BootstrapSecurity.MonomialKDM.generateBootstrappingKey_eq_direct]
  rw [evalDist_bind, evalDist_bind,
    BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct]

/-- The real-BRK/uniform-KSK public decision endpoint is the real cut-cycle game when its
zero-message KSK is generated with uniform scalar errors. -/
theorem realCutGame_uniformError_evalDist_eq_uniformKeySwitchDecisionGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    evalDist (BootstrapCutSecurity.realCutGame
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler ($ᵗ (ZMod q)) tgswGadget (toCutContinuation adversary)) =
      evalDist (uniformKeySwitchDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget (toPublicDistinguisher adversary)) := by
  simp only [BootstrapCutSecurity.realCutGame, BootstrapCutSecurity.zeroKeySwitchContext,
    uniformKeySwitchDecisionGame, uniformKeySwitchPublicView,
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.problem,
    LWE.AuxiliaryInput.Search.exactRecoveryProblem,
    BootstrapSecurity.MonomialKDM.AuxiliaryInput.problem,
    toCutContinuation, toPublicDistinguisher, bind_assoc, pure_bind]
  refine evalDist_bind_congr' (sampleLweSecret lweDimension) fun lweSecret ↦ ?_
  let UniformKeySwitch : ProbComp
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) :=
    $ᵗ (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
  let RingSecrets := sampleRingSecret ringRank degree
  let NativeBootstrap := fun ringSecret ↦
    generateBootstrappingKey q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget lweSecret ringSecret
  let DirectBootstrap := fun ringSecret ↦
    BootstrapSecurity.MonomialKDM.generateBootstrappingKey
      q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget lweSecret ringSecret
  let finish := fun
      (keySwitchKey : KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
      (bootstrapKey : BootstrappingKey q degree ringRank tgswLevels lweDimension) ↦
    adversary ⟨(), bootstrapKey, keySwitchKey⟩
  calc
    evalDist (generateZeroKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels ($ᵗ (ZMod q)) lweSecret >>= fun keySwitchKey ↦
      RingSecrets >>= fun ringSecret ↦
      NativeBootstrap ringSecret >>= fun bootstrapKey ↦
      finish keySwitchKey bootstrapKey) =
      evalDist (UniformKeySwitch >>= fun keySwitchKey ↦
        RingSecrets >>= fun ringSecret ↦
        NativeBootstrap ringSecret >>= fun bootstrapKey ↦
        finish keySwitchKey bootstrapKey) := by
          exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
            (generateZeroKeySwitchKey_uniformError_evalDist
              q lweDimension (ringRank * degree) keySwitchLevels lweSecret)
            (fun keySwitchKey ↦ RingSecrets >>= fun ringSecret ↦
              NativeBootstrap ringSecret >>= fun bootstrapKey ↦
              finish keySwitchKey bootstrapKey)
    _ = evalDist (RingSecrets >>= fun ringSecret ↦
        UniformKeySwitch >>= fun keySwitchKey ↦
        NativeBootstrap ringSecret >>= fun bootstrapKey ↦
        finish keySwitchKey bootstrapKey) :=
      evalDist_bind_bind_swap UniformKeySwitch RingSecrets _
    _ = evalDist (RingSecrets >>= fun ringSecret ↦
        NativeBootstrap ringSecret >>= fun bootstrapKey ↦
        UniformKeySwitch >>= fun keySwitchKey ↦
        finish keySwitchKey bootstrapKey) := by
          refine evalDist_bind_congr' RingSecrets fun ringSecret ↦ ?_
          exact evalDist_bind_bind_swap UniformKeySwitch (NativeBootstrap ringSecret)
            (fun keySwitchKey bootstrapKey ↦ finish keySwitchKey bootstrapKey)
    _ = evalDist (RingSecrets >>= fun ringSecret ↦
        DirectBootstrap ringSecret >>= fun bootstrapKey ↦
        UniformKeySwitch >>= fun keySwitchKey ↦
        finish keySwitchKey bootstrapKey) := by
          refine evalDist_bind_congr' RingSecrets fun ringSecret ↦ ?_
          dsimp only [NativeBootstrap, DirectBootstrap]
          rw [BootstrapSecurity.MonomialKDM.generateBootstrappingKey_eq_direct]
          rw [evalDist_bind, evalDist_bind,
            BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct]

/-- The zero-BRK/uniform-KSK intermediate is likewise the zero cut-cycle endpoint with uniform
scalar errors in its generated zero-message KSK. -/
theorem zeroCutGame_uniformError_evalDist_eq_zeroBootstrapUniformKeySwitchGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    evalDist (BootstrapCutSecurity.zeroCutGame
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler ($ᵗ (ZMod q)) tgswGadget (toCutContinuation adversary)) =
      evalDist (zeroBootstrapUniformKeySwitchGame ringErrorSampler tgswGadget adversary) := by
  simp only [BootstrapCutSecurity.zeroCutGame, BootstrapCutSecurity.zeroKeySwitchContext,
    zeroBootstrapUniformKeySwitchGame, toCutContinuation, bind_assoc, pure_bind]
  refine evalDist_bind_congr' (sampleLweSecret lweDimension) fun lweSecret ↦ ?_
  let UniformKeySwitch : ProbComp
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) :=
    $ᵗ (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
  let RingSecrets := sampleRingSecret ringRank degree
  let ZeroBootstrap := fun ringSecret ↦
    generateZeroBootstrappingKey q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget ringSecret
  let finish := fun
      (keySwitchKey : KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
      (bootstrapKey : BootstrappingKey q degree ringRank tgswLevels lweDimension) ↦
    adversary ⟨(), bootstrapKey, keySwitchKey⟩
  calc
    evalDist (generateZeroKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels ($ᵗ (ZMod q)) lweSecret >>= fun keySwitchKey ↦
      RingSecrets >>= fun ringSecret ↦
      ZeroBootstrap ringSecret >>= fun bootstrapKey ↦
      finish keySwitchKey bootstrapKey) =
      evalDist (UniformKeySwitch >>= fun keySwitchKey ↦
        RingSecrets >>= fun ringSecret ↦
        ZeroBootstrap ringSecret >>= fun bootstrapKey ↦
        finish keySwitchKey bootstrapKey) := by
          exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
            (generateZeroKeySwitchKey_uniformError_evalDist
              q lweDimension (ringRank * degree) keySwitchLevels lweSecret)
            (fun keySwitchKey ↦ RingSecrets >>= fun ringSecret ↦
              ZeroBootstrap ringSecret >>= fun bootstrapKey ↦
              finish keySwitchKey bootstrapKey)
    _ = evalDist (RingSecrets >>= fun ringSecret ↦
        UniformKeySwitch >>= fun keySwitchKey ↦
        ZeroBootstrap ringSecret >>= fun bootstrapKey ↦
        finish keySwitchKey bootstrapKey) :=
      evalDist_bind_bind_swap UniformKeySwitch RingSecrets _
    _ = evalDist (RingSecrets >>= fun ringSecret ↦
        ZeroBootstrap ringSecret >>= fun bootstrapKey ↦
        UniformKeySwitch >>= fun keySwitchKey ↦
        finish keySwitchKey bootstrapKey) := by
          refine evalDist_bind_congr' RingSecrets fun ringSecret ↦ ?_
          exact evalDist_bind_bind_swap UniformKeySwitch (ZeroBootstrap ringSecret)
            (fun keySwitchKey bootstrapKey ↦ finish keySwitchKey bootstrapKey)

/-- The zero-BRK/uniform-KSK intermediate is exactly the uniform branch of the ordinary scalar
LWE pass-through reduction used for the final zero-message KSK hop. -/
theorem zeroBootstrapUniformKeySwitchGame_evalDist_eq_lwe_game1
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    evalDist (zeroBootstrapUniformKeySwitchGame ringErrorSampler tgswGadget adversary) =
      evalDist (LearningWithErrors.game1
        (KeySwitchSecurity.binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (KeySwitchSecurity.zeroMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget adversary)) := by
  let ScalarSecrets := sampleLweSecret lweDimension
  let Context := KeySwitchSecurity.zeroBootstrapContext
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
  let Challenge := Matrix (Fin lweDimension)
    (Fin ((ringRank * degree) * keySwitchLevels)) (ZMod q)
  let Output := Fin ((ringRank * degree) * keySwitchLevels) → ZMod q
  let UniformKeySwitch : ProbComp
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) :=
    $ᵗ (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
  let SplitUniform : ProbComp
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) := do
    let challenge ← $ᵗ Challenge
    let output ← $ᵗ Output
    return (challenge, output)
  let finish := fun
      (context : RingBinarySecret ringRank degree ×
        BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (keySwitchKey : KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) ↦
    adversary ⟨(), context.2, keySwitchKey⟩
  have hUniform : evalDist UniformKeySwitch = evalDist SplitUniform := by
    exact (FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
      (first := Challenge) (second := Output)).symm
  calc
    evalDist (zeroBootstrapUniformKeySwitchGame ringErrorSampler tgswGadget adversary) =
      evalDist (ScalarSecrets >>= fun _ ↦
        Context >>= fun context ↦
        UniformKeySwitch >>= fun keySwitchKey ↦
        finish context keySwitchKey) := by
          simp [zeroBootstrapUniformKeySwitchGame, ScalarSecrets, Context,
            KeySwitchSecurity.zeroBootstrapContext, UniformKeySwitch, finish,
            bind_assoc, monad_norm]
    _ = evalDist (Context >>= fun context ↦
        UniformKeySwitch >>= fun keySwitchKey ↦
        finish context keySwitchKey) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ScalarSecrets (by simp [ScalarSecrets, sampleLweSecret]) _
    _ = evalDist (Context >>= fun context ↦
        SplitUniform >>= fun keySwitchKey ↦
        finish context keySwitchKey) := by
          refine evalDist_bind_congr' Context fun context ↦ ?_
          exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
            hUniform (fun keySwitchKey ↦ finish context keySwitchKey)
    _ = evalDist (SplitUniform >>= fun keySwitchKey ↦
        Context >>= fun context ↦ finish context keySwitchKey) :=
      evalDist_bind_bind_swap Context SplitUniform _
    _ = evalDist (LearningWithErrors.game1
        (KeySwitchSecurity.binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (KeySwitchSecurity.zeroMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget adversary)) := by
      simp [LearningWithErrors.game1, LearningWithErrors.uniformDistr,
        KeySwitchSecurity.binaryLweProblem, FormalProof4FHE.LWE.embeddedBatchProblem,
        KeySwitchSecurity.zeroMessageReduction, Context,
        KeySwitchSecurity.zeroBootstrapContext, SplitUniform, Challenge, Output,
        finish, bind_assoc, monad_norm]

/-! ## Exact advantage bridges -/

/-- The first cloud-key hop, from the structured native real game to the direct-row
real-BRK/uniform-KSK endpoint. -/
noncomputable def realToUniformKeySwitchAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) : ℝ :=
  (Circular.realGame
    (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    Circular.evaluationKeyOnlyPayload adversary).boolDistAdvantage
  (uniformKeySwitchDecisionGame ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget (toPublicDistinguisher adversary))

/-- The middle cloud-key hop, replacing the BRK while the KSK is uniform. -/
noncomputable def uniformKeySwitchBootstrapAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) : ℝ :=
  (uniformKeySwitchDecisionGame ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget (toPublicDistinguisher adversary)).boolDistAdvantage
  (zeroBootstrapUniformKeySwitchGame ringErrorSampler tgswGadget adversary)

/-- The final cloud-key hop, from a uniform KSK to a zero-message KSK after the BRK cut. -/
noncomputable def uniformToZeroKeySwitchAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) : ℝ :=
  (zeroBootstrapUniformKeySwitchGame ringErrorSampler tgswGadget adversary).boolDistAdvantage
  (Circular.zeroGame
    (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    Circular.evaluationKeyOnlyPayload adversary)

/-- The first hybrid advantage is exactly the KSK-first public decision advantage consumed by
the finite-search reduction. -/
theorem realToUniformKeySwitchAdvantage_eq_keySwitchDecisionAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    realToUniformKeySwitchAdvantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget adversary =
      keySwitchDecisionAdvantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget (toPublicDistinguisher adversary) := by
  unfold realToUniformKeySwitchAdvantage keySwitchDecisionAdvantage
    ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
    (realGame_evalDist_eq_realDecisionGame ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget adversary)]

/-- The middle hybrid advantage is exactly the existing cut-cycle BRK replacement advantage
instantiated with uniform scalar errors in its zero-message KSK context. -/
theorem uniformKeySwitchBootstrapAdvantage_eq_cutBootstrapReplacementAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    uniformKeySwitchBootstrapAdvantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget adversary =
      BootstrapCutSecurity.cutBootstrapReplacementAdvantage
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler ($ᵗ (ZMod q)) tgswGadget (toCutContinuation adversary) := by
  unfold uniformKeySwitchBootstrapAdvantage
    BootstrapCutSecurity.cutBootstrapReplacementAdvantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (realCutGame_uniformError_evalDist_eq_uniformKeySwitchDecisionGame
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary),
    probOutput_congr rfl
      (zeroCutGame_uniformError_evalDist_eq_zeroBootstrapUniformKeySwitchGame
        ringErrorSampler tgswGadget adversary)]

/-- The last hybrid advantage is exactly one ordinary scalar binary-secret batch-LWE
advantage: its two endpoints are the uniform and real branches in reverse order. -/
theorem uniformToZeroKeySwitchAdvantage_eq_lwe
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    uniformToZeroKeySwitchAdvantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget adversary =
      LearningWithErrors.advantage
        (KeySwitchSecurity.binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (KeySwitchSecurity.zeroMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold uniformToZeroKeySwitchAdvantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (zeroBootstrapUniformKeySwitchGame_evalDist_eq_lwe_game1
        ringErrorSampler keySwitchErrorSampler tgswGadget adversary),
    probOutput_congr rfl
      (KeySwitchSecurity.zeroGame_evalDist_eq_lwe_game0
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary)]
  rw [abs_sub_comm]

/-! ## Cloud-key composition -/

/-- The native cloud-key circular advantage splits along the KSK-first four-game path. -/
theorem circularAdvantage_le_kskFirst_hybrids
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    Circular.circularAdvantage
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload adversary ≤
      realToUniformKeySwitchAdvantage ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget adversary +
        uniformKeySwitchBootstrapAdvantage ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget adversary +
        uniformToZeroKeySwitchAdvantage ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget adversary := by
  let realGame := Circular.realGame
    (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    Circular.evaluationKeyOnlyPayload adversary
  let realUniformGame := uniformKeySwitchDecisionGame ringErrorSampler
    keySwitchErrorSampler tgswGadget keySwitchGadget (toPublicDistinguisher adversary)
  let zeroUniformGame := zeroBootstrapUniformKeySwitchGame
    ringErrorSampler tgswGadget adversary
  let zeroGame := Circular.zeroGame
    (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    Circular.evaluationKeyOnlyPayload adversary
  have hFirst := ProbComp.boolDistAdvantage_triangle realGame realUniformGame zeroGame
  have hRest := ProbComp.boolDistAdvantage_triangle realUniformGame zeroUniformGame zeroGame
  unfold Circular.circularAdvantage realToUniformKeySwitchAdvantage
    uniformKeySwitchBootstrapAdvantage uniformToZeroKeySwitchAdvantage
  dsimp only [realGame, realUniformGame, zeroUniformGame, zeroGame] at hFirst hRest ⊢
  linarith

/-- **KSK-first native cloud-key security bound.**  The complete circular advantage is at most
the KSK-first public decision term, two ordinary batch module-LWE advantages for replacing the
BRK with a uniform KSK, and one ordinary scalar batch-LWE advantage for the final KSK hop. -/
theorem circularAdvantage_le_decision_add_two_moduleLwe_add_lwe
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    Circular.circularAdvantage
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload adversary ≤
      keySwitchDecisionAdvantage ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget (toPublicDistinguisher adversary) +
        LearningWithErrors.advantage
          (BootstrapCutSecurity.batchModuleLweProblem
            q degree ringRank tgswLevels lweDimension ringErrorSampler)
          (BootstrapCutSecurity.realBatchReduction
            ringErrorSampler ($ᵗ (ZMod q)) tgswGadget (toCutContinuation adversary)) +
        LearningWithErrors.advantage
          (BootstrapCutSecurity.batchModuleLweProblem
            q degree ringRank tgswLevels lweDimension ringErrorSampler)
          (BootstrapCutSecurity.zeroBatchReduction
            ringErrorSampler ($ᵗ (ZMod q)) (toCutContinuation adversary)) +
        LearningWithErrors.advantage
          (KeySwitchSecurity.binaryLweProblem q lweDimension
            ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
          (KeySwitchSecurity.zeroMessageReduction ringErrorSampler keySwitchErrorSampler
            tgswGadget adversary) := by
  have hHybrid := circularAdvantage_le_kskFirst_hybrids
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary
  rw [realToUniformKeySwitchAdvantage_eq_keySwitchDecisionAdvantage,
    uniformKeySwitchBootstrapAdvantage_eq_cutBootstrapReplacementAdvantage,
    uniformToZeroKeySwitchAdvantage_eq_lwe] at hHybrid
  have hCut := BootstrapCutSecurity.cutBootstrapReplacementAdvantage_le_two_batchModuleLwe
    ringErrorSampler ($ᵗ (ZMod q)) tgswGadget (toCutContinuation adversary)
  linarith

/-! ## Hardness transfer -/

/-- KSK-first public-decision hardness plus ordinary post-cut module-LWE and scalar-LWE hardness
imply native cloud-key circular security. -/
theorem circularHardAgainst_of_decision_and_lwe
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tfheAllowed : Adversary q degree ringRank tgswLevels lweDimension
      keySwitchLevels → Prop)
    (decisionAllowed : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (moduleLweAllowed : LearningWithErrors.Adversary
      (BootstrapCutSecurity.batchModuleLweProblem
        q degree ringRank tgswLevels lweDimension ringErrorSampler) → Prop)
    (scalarLweAllowed : LearningWithErrors.Adversary
      (KeySwitchSecurity.binaryLweProblem q lweDimension
        ((ringRank * degree) * keySwitchLevels)
        (CenteredBinomial.scalarSampler q keySwitchEta)) → Prop)
    (decisionBound moduleLweBound scalarLweBound : ℝ)
    (hDecision :
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstSearchToDecision.NativePublicHardAgainst
          (keySwitchEta := keySwitchEta) ringErrorSampler
          tgswGadget keySwitchGadget decisionAllowed decisionBound)
    (hDecisionClosed : ∀ adversary, tfheAllowed adversary →
      decisionAllowed (toPublicDistinguisher adversary))
    (hRealModuleClosed : ∀ adversary, tfheAllowed adversary →
      moduleLweAllowed
        (BootstrapCutSecurity.realBatchReduction ringErrorSampler ($ᵗ (ZMod q))
          tgswGadget (toCutContinuation adversary)))
    (hZeroModuleClosed : ∀ adversary, tfheAllowed adversary →
      moduleLweAllowed
        (BootstrapCutSecurity.zeroBatchReduction ringErrorSampler ($ᵗ (ZMod q))
          (toCutContinuation adversary)))
    (hScalarClosed : ∀ adversary, tfheAllowed adversary →
      scalarLweAllowed
        (KeySwitchSecurity.zeroMessageReduction ringErrorSampler
          (CenteredBinomial.scalarSampler q keySwitchEta) tgswGadget adversary))
    (hModuleLwe : FormalProof4FHE.LWE.HardAgainst
      (BootstrapCutSecurity.batchModuleLweProblem
        q degree ringRank tgswLevels lweDimension ringErrorSampler)
      moduleLweAllowed moduleLweBound)
    (hScalarLwe : FormalProof4FHE.LWE.HardAgainst
      (KeySwitchSecurity.binaryLweProblem q lweDimension
        ((ringRank * degree) * keySwitchLevels)
        (CenteredBinomial.scalarSampler q keySwitchEta))
      scalarLweAllowed scalarLweBound) :
    Circular.CircularHardAgainst
      (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget)
      Circular.evaluationKeyOnlyPayload tfheAllowed
      (decisionBound + 2 * moduleLweBound + scalarLweBound) := by
  intro adversary hadversary
  have hExpanded := circularAdvantage_le_decision_add_two_moduleLwe_add_lwe
    ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
    tgswGadget keySwitchGadget adversary
  have hDecisionAdversary := hDecision
    (toPublicDistinguisher adversary) (hDecisionClosed adversary hadversary)
  have hRealModule := hModuleLwe _ (hRealModuleClosed adversary hadversary)
  have hZeroModule := hModuleLwe _ (hZeroModuleClosed adversary hadversary)
  have hScalar := hScalarLwe _ (hScalarClosed adversary hadversary)
  linarith

/-- **Finite-search-to-cloud-key security theorem.**  Finite-batch paired-search hardness for
exactly `lweDimension * 3 ^ rounds + 1` centered-binomial native views, together with the explicit
amplification-loss bound and ordinary post-cut LWE assumptions, implies native TFHE cloud-key
circular security. -/
theorem circularHardAgainst_of_finiteSearch_and_lwe
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (threshold : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels → ENNReal)
    (hthreshold_pos : ∀ distinguisher, 0 < threshold distinguisher)
    (hthreshold_one : ∀ distinguisher, threshold distinguisher ≤ 1)
    (tfheAllowed : Adversary q degree ringRank tgswLevels lweDimension
      keySwitchLevels → Prop)
    (decisionAllowed : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (solverAllowed : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels rounds → Prop)
    (moduleLweAllowed : LearningWithErrors.Adversary
      (BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
        lweDimension (RLWE.CenteredBinomial.sampler q degree ringEta)) → Prop)
    (scalarLweAllowed : LearningWithErrors.Adversary
      (KeySwitchSecurity.binaryLweProblem q lweDimension
        ((ringRank * degree) * keySwitchLevels)
        (CenteredBinomial.scalarSampler q keySwitchEta)) → Prop)
    (searchBound lossBound moduleLweBound scalarLweBound : ℝ)
    (hSearch : RealSearchHardAgainst (ringEta := ringEta)
      (keySwitchEta := keySwitchEta) tgswGadget keySwitchGadget
      rounds solverAllowed searchBound)
    (hFiniteClosed : ∀ distinguisher, decisionAllowed distinguisher →
      solverAllowed
        (amplifiedSolver
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget level rounds distinguisher))
    (hLoss : ∀ distinguisher, decisionAllowed distinguisher →
      BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstFreshView.amplifiedLoss
          (ringEta := ringEta) (keySwitchEta := keySwitchEta)
          tgswGadget keySwitchGadget (fun _ ↦ rounds)
          (threshold distinguisher) distinguisher ≤ lossBound)
    (hDecisionClosed : ∀ adversary, tfheAllowed adversary →
      decisionAllowed (toPublicDistinguisher adversary))
    (hRealModuleClosed : ∀ adversary, tfheAllowed adversary →
      moduleLweAllowed
        (BootstrapCutSecurity.realBatchReduction
          (RLWE.CenteredBinomial.sampler q degree ringEta) ($ᵗ (ZMod q))
          tgswGadget (toCutContinuation adversary)))
    (hZeroModuleClosed : ∀ adversary, tfheAllowed adversary →
      moduleLweAllowed
        (BootstrapCutSecurity.zeroBatchReduction
          (RLWE.CenteredBinomial.sampler q degree ringEta) ($ᵗ (ZMod q))
          (toCutContinuation adversary)))
    (hScalarClosed : ∀ adversary, tfheAllowed adversary →
      scalarLweAllowed
        (KeySwitchSecurity.zeroMessageReduction
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta) tgswGadget adversary))
    (hModuleLwe : FormalProof4FHE.LWE.HardAgainst
      (BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
        lweDimension (RLWE.CenteredBinomial.sampler q degree ringEta))
      moduleLweAllowed moduleLweBound)
    (hScalarLwe : FormalProof4FHE.LWE.HardAgainst
      (KeySwitchSecurity.binaryLweProblem q lweDimension
        ((ringRank * degree) * keySwitchLevels)
        (CenteredBinomial.scalarSampler q keySwitchEta))
      scalarLweAllowed scalarLweBound) :
    Circular.CircularHardAgainst
      (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget)
      Circular.evaluationKeyOnlyPayload tfheAllowed
      ((searchBound + lossBound) + 2 * moduleLweBound + scalarLweBound) := by
  have hDecision := nativePublicHardAgainst_of_finiteSearchHardness
    (ringEta := ringEta) (keySwitchEta := keySwitchEta)
    tgswGadget keySwitchGadget level hmargin reference rounds threshold
    hthreshold_pos hthreshold_one decisionAllowed solverAllowed
    searchBound lossBound hSearch hFiniteClosed hLoss
  exact circularHardAgainst_of_decision_and_lwe
    (RLWE.CenteredBinomial.sampler q degree ringEta)
    tgswGadget keySwitchGadget tfheAllowed decisionAllowed
    moduleLweAllowed scalarLweAllowed (searchBound + lossBound)
    moduleLweBound scalarLweBound hDecision hDecisionClosed
    hRealModuleClosed hZeroModuleClosed hScalarClosed hModuleLwe hScalarLwe

end FormalProof4FHE.TFHE.Native.KeySwitchFirstCloudSecurity
