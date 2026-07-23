/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.EncryptionSecurity
import FormalProof4FHE.TFHE.SharedRandomnessOneCycle

/-!
# One-Time Encryption Security for Shared-Randomness One-Cycle TFHE

This module instantiates the shared-randomness one-cycle BRK theorem inside TFHE's one-time
left-or-right encryption experiment.  The scalar TLWE key is the prefix of one rank-one master
ring key, and the suffix-only KSK encrypts only the independent suffix under that prefix.

The security proof has two steps:

1. replace the native self-circular BRK by an independent uniform BRK, paying the exact finite
   ring-error sampler distance;
2. place every suffix-KSK row and the adaptive input ciphertext row in one unequal two-block
   binary-secret LWE transcript.

For equal KSK/input noises the second step is exactly an ordinary batch-LWE problem.  Uniform or
near-uniform BRK row errors are a security-only regime and are not claimed to satisfy TFHE's
correctness margin.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption.SharedRandomnessOneCycle

noncomputable section

variable {Message : Type}
  {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]

/-- Public evaluation key of the shared-randomness one-cycle TFHE variant. -/
abbrev CloudKey
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) :=
  Native.SharedRandomnessOneCycle.CloudKey q prefixDimension suffixDimension
    tgswLevels keySwitchLevels

/-- One-time left-or-right adversary for the shared-randomness cloud-key layout. -/
abbrev Adversary (Message : Type)
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) :=
  Encryption.OneTimeAdversary Message
    (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels)
    (ScalarCiphertext q prefixDimension)

/-- Run the adaptive one-time challenge from an already supplied scalar key and cloud key. -/
def oneTimeExperiment
    (inputErrorSampler : ProbComp (ZMod q)) (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (prefixKey : BinarySecret prefixDimension)
    (bootstrappingKey :
      Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
        suffixDimension tgswLevels)
    (keySwitchKey :
      Native.SharedRandomnessOneCycle.SharedKeySwitchKey q prefixDimension
        suffixDimension keySwitchLevels) : ProbComp Bool := do
  let bit ← $ᵗ Bool
  let (message₀, message₁, state) ←
    adversary.chooseMessages ⟨bootstrappingKey, keySwitchKey⟩
  let ciphertext ← Encryption.encrypt q prefixDimension inputErrorSampler encode
    prefixKey (if bit then message₀ else message₁)
  let guess ← adversary.distinguish state ciphertext
  return (bit == guess)

/-- Secret-dependent continuation induced by the shared-key one-time encryption adversary. -/
def oneTimeContinuation
    (inputErrorSampler : ProbComp (ZMod q)) (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    Native.SharedRandomnessOneCycle.SecretContinuation q prefixDimension suffixDimension
      tgswLevels keySwitchLevels :=
  fun masterSecret bootstrappingKey keySwitchKey ↦
    oneTimeExperiment inputErrorSampler encode adversary
      (Native.SharedRandomnessOneCycle.prefixSecret masterSecret)
      bootstrappingKey keySwitchKey

/-- Honest one-time TFHE encryption game for the shared-randomness one-cycle construction. -/
noncomputable def realGame
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) : ProbComp Bool :=
  Native.SharedRandomnessOneCycle.realSecretContinuationGame q prefixDimension
    suffixDimension tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget (oneTimeContinuation inputErrorSampler encode adversary)

/-- Uniform-BRK endpoint retaining one sampled master key and its real suffix-only KSK. -/
noncomputable def masterUniformBootstrapGame
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) : ProbComp Bool := do
  let masterSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  let bootstrappingKey ← $ᵗ
    (Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
      suffixDimension tgswLevels)
  let keySwitchKey ← Native.SharedRandomnessOneCycle.generateKeySwitchKey q
    prefixDimension suffixDimension keySwitchLevels keySwitchErrorSampler
    keySwitchGadget masterSecret
  oneTimeExperiment inputErrorSampler encode adversary
    (Native.SharedRandomnessOneCycle.prefixSecret masterSecret)
    bootstrappingKey keySwitchKey

/-- Equivalent uniform-BRK endpoint with independently sampled prefix and suffix keys. -/
noncomputable def independentUniformBootstrapGame
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) : ProbComp Bool := do
  let prefixKey ← Native.sampleLweSecret prefixDimension
  let suffixKey ← Native.sampleLweSecret suffixDimension
  let bootstrappingKey ← $ᵗ
    (Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
      suffixDimension tgswLevels)
  let keySwitchKey ← Native.generateKeySwitchKey q prefixDimension suffixDimension
    keySwitchLevels keySwitchErrorSampler keySwitchGadget suffixKey prefixKey
  oneTimeExperiment inputErrorSampler encode adversary prefixKey
    bootstrappingKey keySwitchKey

/-- With uniform ring-row errors, the real self-circular BRK can be resampled as an independent
uniform public key while the exact master-secret-correlated suffix KSK is retained. -/
theorem realGame_uniformRingError_evalDist_eq_masterUniformBootstrap
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    evalDist (realGame
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary) =
    evalDist (masterUniformBootstrapGame keySwitchErrorSampler inputErrorSampler
      keySwitchGadget encode adversary) := by
  unfold realGame Native.SharedRandomnessOneCycle.realSecretContinuationGame
    oneTimeContinuation masterUniformBootstrapGame
  refine evalDist_bind_congr'
    (Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) fun masterSecret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (Native.SharedRandomnessOneCycle.generateBootstrappingKey_uniformError_evalDist
      q prefixDimension suffixDimension tgswLevels tgswGadget masterSecret)
    (fun bootstrappingKey ↦
      Native.SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension
          suffixDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget
          masterSecret >>= fun keySwitchKey ↦
        oneTimeExperiment inputErrorSampler encode adversary
          (Native.SharedRandomnessOneCycle.prefixSecret masterSecret)
          bootstrappingKey keySwitchKey)

/-- The master-key endpoint is exactly the independent prefix/suffix presentation. -/
theorem masterUniformBootstrapGame_evalDist_eq_independent
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    evalDist (masterUniformBootstrapGame keySwitchErrorSampler inputErrorSampler
      keySwitchGadget encode adversary) =
    evalDist (independentUniformBootstrapGame keySwitchErrorSampler inputErrorSampler
      keySwitchGadget encode adversary) := by
  let splitSampler : ProbComp
      (BinarySecret prefixDimension × BinarySecret suffixDimension) := do
    let masterSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
    return Native.SharedRandomnessOneCycle.splitNestedSecret masterSecret
  let independentSampler : ProbComp
      (BinarySecret prefixDimension × BinarySecret suffixDimension) := do
    let prefixKey ← Native.sampleLweSecret prefixDimension
    let suffixKey ← Native.sampleLweSecret suffixDimension
    return (prefixKey, suffixKey)
  let finish := fun
      keys : BinarySecret prefixDimension × BinarySecret suffixDimension ↦ do
    let bootstrappingKey ← $ᵗ
      (Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
        suffixDimension tgswLevels)
    let keySwitchKey ← Native.generateKeySwitchKey q prefixDimension suffixDimension
      keySwitchLevels keySwitchErrorSampler keySwitchGadget keys.2 keys.1
    oneTimeExperiment inputErrorSampler encode adversary keys.1
      bootstrappingKey keySwitchKey
  have hSampler : evalDist splitSampler = evalDist independentSampler := by
    exact Native.SharedRandomnessOneCycle.sampleRingSecret_prefix_suffix_evalDist
      prefixDimension suffixDimension
  have hBind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hSampler finish
  simpa [masterUniformBootstrapGame, independentUniformBootstrapGame,
    Native.SharedRandomnessOneCycle.generateKeySwitchKey, splitSampler,
    independentSampler, finish, Native.SharedRandomnessOneCycle.splitNestedSecret,
    bind_assoc, monad_norm] using hBind

/-- Complete uniform-BRK normalization from the honest uniform-error game to independent keys. -/
theorem realGame_uniformRingError_evalDist_eq_independent
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    evalDist (realGame
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary) =
    evalDist (independentUniformBootstrapGame keySwitchErrorSampler inputErrorSampler
      keySwitchGadget encode adversary) :=
  (realGame_uniformRingError_evalDist_eq_masterUniformBootstrap
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary).trans
      (masterUniformBootstrapGame_evalDist_eq_independent
        keySwitchErrorSampler inputErrorSampler keySwitchGadget encode adversary)

/-! ## The suffix KSK and input row as one ordinary-LWE transcript -/

/-- Number of direct scalar-LWE rows in the suffix-only KSK. -/
abbrev keySwitchSamples (suffixDimension keySwitchLevels : ℕ) : ℕ :=
  suffixDimension * keySwitchLevels

/-- Unequal two-block LWE problem containing every suffix-KSK row and one input row under the
same hidden prefix key. -/
def jointLweProblem
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)) :=
  Encryption.Security.jointLweProblem q prefixDimension
    (keySwitchSamples suffixDimension keySwitchLevels)
    keySwitchErrorSampler inputErrorSampler

/-- Independent public context in the uniform-BRK endpoint: a suffix key and a uniform BRK. -/
noncomputable def uniformBootstrapContext
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q] :
    ProbComp
      (BinarySecret suffixDimension ×
        Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
          suffixDimension tgswLevels) := do
  let suffixKey ← Native.sampleLweSecret suffixDimension
  let bootstrappingKey ← $ᵗ
    (Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
      suffixDimension tgswLevels)
  return (suffixKey, bootstrappingKey)

/-- Gadget messages carried by the complete suffix-only KSK block. -/
def keySwitchMessage
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (suffixKey : BinarySecret suffixDimension) :
    Fin (keySwitchSamples suffixDimension keySwitchLevels) → ZMod q :=
  Native.keySwitchMessages suffixDimension keySwitchLevels keySwitchGadget suffixKey

/-- Run the one-time challenge from an already supplied two-block public transcript. -/
def transcriptGame
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (bootstrappingKey :
      Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
        suffixDimension tgswLevels)
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript (ZMod q) prefixDimension
      (keySwitchSamples suffixDimension keySwitchLevels) 1) : ProbComp Bool := do
  let bit ← $ᵗ Bool
  let (message₀, message₁, state) ← adversary.chooseMessages
    ⟨bootstrappingKey, Encryption.Security.keySwitchTranscript transcript⟩
  let ciphertext := Encryption.Security.challengeCiphertext encode
    (if bit then message₀ else message₁)
    (Encryption.Security.inputTranscript transcript)
  let guess ← adversary.distinguish state ciphertext
  return (bit == guess)

/-- LWE distinguisher which translates the first block by the independently sampled suffix-key
messages and runs the shared-key TFHE adversary with an independent uniform BRK. -/
noncomputable def jointLweReduction
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    LearningWithErrors.Adversary
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
        keySwitchErrorSampler inputErrorSampler) :=
  fun transcript ↦ do
    let context ← uniformBootstrapContext q prefixDimension suffixDimension tgswLevels
    transcriptGame encode adversary context.2
      (Encryption.Security.shiftFirstBlock
        (keySwitchMessage keySwitchGadget context.1) transcript)

/-- Unshifted comparison reduction used to analyze the uniform LWE branch. -/
noncomputable def zeroJointLweReduction
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    LearningWithErrors.Adversary
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
        keySwitchErrorSampler inputErrorSampler) :=
  fun transcript ↦ do
    let context ← uniformBootstrapContext q prefixDimension suffixDimension tgswLevels
    transcriptGame encode adversary context.2 transcript

/-- The independent uniform-BRK endpoint is exactly the real branch of the translated unequal
two-block binary-secret LWE reduction. -/
theorem independentUniformBootstrapGame_evalDist_eq_jointLwe_game0
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    evalDist (independentUniformBootstrapGame keySwitchErrorSampler inputErrorSampler
      keySwitchGadget encode adversary) =
    evalDist (LearningWithErrors.game0
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
        keySwitchErrorSampler inputErrorSampler)
      (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
        encode adversary)) := by
  let samples := keySwitchSamples suffixDimension keySwitchLevels
  let FirstChallenge := Matrix (Fin prefixDimension) (Fin samples) (ZMod q)
  let SecondChallenge := Matrix (Fin prefixDimension) (Fin 1) (ZMod q)
  let FirstError := Fin samples → ZMod q
  let SecondError := Fin 1 → ZMod q
  let prefixSecrets := Native.sampleLweSecret prefixDimension
  let contexts := uniformBootstrapContext q prefixDimension suffixDimension tgswLevels
  let firstChallenges : ProbComp FirstChallenge := $ᵗ FirstChallenge
  let secondChallenges : ProbComp SecondChallenge := $ᵗ SecondChallenge
  let firstErrors : ProbComp FirstError :=
    ProbComp.sampleIID samples keySwitchErrorSampler
  let secondErrors : ProbComp SecondError :=
    ProbComp.sampleIID 1 inputErrorSampler
  let nativeInputs : ProbComp ((Fin prefixDimension → ZMod q) × ZMod q) := do
    let mask ← $ᵗ (Fin prefixDimension → ZMod q)
    let error ← inputErrorSampler
    return (mask, error)
  let batchInputs : ProbComp ((Fin prefixDimension → ZMod q) × ZMod q) := do
    let challenge ← secondChallenges
    let error ← secondErrors
    return (Encryption.Security.singleMask challenge,
      Encryption.Security.headOutput error)
  let preGame := fun (prefixKey : BinarySecret prefixDimension)
      (context : BinarySecret suffixDimension ×
        Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
          suffixDimension tgswLevels)
      (challenge : FirstChallenge) (error : FirstError) ↦ do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages
      ⟨context.2, TLWE.batchAssemble (embedBinarySecret prefixKey) challenge
        (keySwitchMessage keySwitchGadget context.1) error⟩
    return (bit, messages)
  let final := fun (prefixKey : BinarySecret prefixDimension)
      (pre : Bool × (Message × Message × adversary.State))
      (input : (Fin prefixDimension → ZMod q) × ZMod q) ↦ do
    let selected := if pre.1 then pre.2.1 else pre.2.2.1
    let ciphertext := TLWE.assemble (embedBinarySecret prefixKey) input.1
      (encode selected) input.2
    let guess ← adversary.distinguish pre.2.2.2 ciphertext
    return (pre.1 == guess)
  let finish := fun (prefixKey : BinarySecret prefixDimension)
      (context : BinarySecret suffixDimension ×
        Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
          suffixDimension tgswLevels)
      (challenge : FirstChallenge) (error : FirstError)
      (input : (Fin prefixDimension → ZMod q) × ZMod q) ↦
    preGame prefixKey context challenge error >>= fun pre ↦
      final prefixKey pre input
  have native_eq :
      independentUniformBootstrapGame keySwitchErrorSampler inputErrorSampler
          keySwitchGadget encode adversary =
        (prefixSecrets >>= fun prefixKey ↦
          contexts >>= fun context ↦
          firstChallenges >>= fun challenge ↦
          firstErrors >>= fun error ↦
          preGame prefixKey context challenge error >>= fun pre ↦
          nativeInputs >>= fun input ↦
          final prefixKey pre input) := by
    simp [independentUniformBootstrapGame, oneTimeExperiment,
      Native.generateKeySwitchKey, TLWE.batchEncrypt, Encryption.encrypt, TLWE.encrypt,
      prefixSecrets, contexts, uniformBootstrapContext, samples, keySwitchSamples,
      FirstChallenge, FirstError, firstChallenges, firstErrors, nativeInputs,
      preGame, final, keySwitchMessage, bind_assoc, monad_norm]
  have lwe_eq :
      LearningWithErrors.game0
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
            keySwitchErrorSampler inputErrorSampler)
          (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
            encode adversary) =
        (firstChallenges >>= fun challenge ↦
          secondChallenges >>= fun inputChallenge ↦
          prefixSecrets >>= fun prefixKey ↦
          firstErrors >>= fun error ↦
          secondErrors >>= fun inputError ↦
          contexts >>= fun context ↦
          finish prefixKey context challenge error
            (Encryption.Security.singleMask inputChallenge,
              Encryption.Security.headOutput inputError)) := by
    have uniformChallengeProduct :
        ($ᵗ (FormalProof4FHE.LWE.TwoBlock.Challenge
          (ZMod q) prefixDimension samples 1) :
          ProbComp (FormalProof4FHE.LWE.TwoBlock.Challenge
            (ZMod q) prefixDimension samples 1)) =
        Prod.mk <$> firstChallenges <*> secondChallenges := rfl
    rw [LearningWithErrors.game0]
    simp only [jointLweProblem, Encryption.Security.jointLweProblem]
    unfold LearningWithErrors.distr
    simp only [FormalProof4FHE.LWE.TwoBlock.heterogeneousProblem]
    rw [uniformChallengeProduct]
    simp [jointLweReduction, transcriptGame,
      Encryption.Security.keySwitchTranscript_shiftFirstBlock_real,
      Encryption.Security.inputTranscript_shiftFirstBlock,
      Encryption.Security.challengeCiphertext_inputTranscript_real,
      samples, keySwitchSamples, FirstChallenge, SecondChallenge, FirstError, SecondError,
      prefixSecrets, contexts, firstChallenges, secondChallenges, firstErrors, secondErrors,
      finish, preGame, final, Encryption.Security.headOutput, bind_assoc, monad_norm]
  rw [native_eq, lwe_eq]
  calc
    _ = evalDist (prefixSecrets >>= fun prefixKey ↦
        contexts >>= fun context ↦
        firstChallenges >>= fun challenge ↦
        firstErrors >>= fun error ↦
        nativeInputs >>= fun input ↦
        finish prefixKey context challenge error input) := by
      refine evalDist_bind_congr' prefixSecrets fun prefixKey ↦ ?_
      refine evalDist_bind_congr' contexts fun context ↦ ?_
      refine evalDist_bind_congr' firstChallenges fun challenge ↦ ?_
      refine evalDist_bind_congr' firstErrors fun error ↦ ?_
      exact evalDist_bind_bind_swap
        (preGame prefixKey context challenge error) nativeInputs
        (fun pre input ↦ final prefixKey pre input)
    _ = evalDist (prefixSecrets >>= fun prefixKey ↦
        contexts >>= fun context ↦
        firstChallenges >>= fun challenge ↦
        firstErrors >>= fun error ↦
        batchInputs >>= fun input ↦
        finish prefixKey context challenge error input) := by
      have hInput : evalDist batchInputs = evalDist nativeInputs := by
        simpa only [batchInputs, nativeInputs, secondChallenges, secondErrors] using
          (Encryption.Security.inputMaterial_evalDist
            (R := ZMod q) prefixDimension inputErrorSampler)
      refine evalDist_bind_congr' prefixSecrets fun prefixKey ↦ ?_
      refine evalDist_bind_congr' contexts fun context ↦ ?_
      refine evalDist_bind_congr' firstChallenges fun challenge ↦ ?_
      refine evalDist_bind_congr' firstErrors fun error ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hInput.symm _
    _ = evalDist (prefixSecrets >>= fun prefixKey ↦
        contexts >>= fun context ↦
        firstChallenges >>= fun challenge ↦
        firstErrors >>= fun error ↦
        secondChallenges >>= fun inputChallenge ↦
        secondErrors >>= fun inputError ↦
        finish prefixKey context challenge error
          (Encryption.Security.singleMask inputChallenge,
            Encryption.Security.headOutput inputError)) := by
      simp [batchInputs, bind_assoc, monad_norm]
    _ = _ :=
      Encryption.Security.evalDist_bind_six_reorder prefixSecrets contexts
        firstChallenges firstErrors secondChallenges secondErrors
        (fun prefixKey context challenge error inputChallenge inputError ↦
          finish prefixKey context challenge error
            (Encryption.Security.singleMask inputChallenge,
              Encryption.Security.headOutput inputError))

/-- Translating the KSK block by the independently sampled suffix messages does not change the
uniform two-block LWE branch. -/
theorem jointLweReduction_game1_evalDist_eq_zero
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    evalDist (LearningWithErrors.game1
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
        keySwitchErrorSampler inputErrorSampler)
      (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
        encode adversary)) =
    evalDist (LearningWithErrors.game1
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
        keySwitchErrorSampler inputErrorSampler)
      (zeroJointLweReduction keySwitchErrorSampler inputErrorSampler
        encode adversary)) := by
  let samples := keySwitchSamples suffixDimension keySwitchLevels
  let contexts := uniformBootstrapContext q prefixDimension suffixDimension tgswLevels
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [jointLweProblem, Encryption.Security.jointLweProblem]
  rw [FormalProof4FHE.LWE.TwoBlock.heterogeneousUniformDistr_eq_uniformSample]
  have hShift := Encryption.Security.uniformTranscript_context_shiftFirst_evalDist
    prefixDimension samples 1 contexts
    (fun context ↦ keySwitchMessage keySwitchGadget context.1)
    (fun context transcript ↦ transcriptGame encode adversary context.2 transcript)
  simpa [samples, contexts, jointLweReduction, zeroJointLweReduction,
    bind_assoc, monad_norm] using hShift

/-- For every fixed shared cloud key, a uniform one-row transcript erases the adaptively selected
encoded message, so a fair challenge bit is guessed with probability exactly one half. -/
theorem uniformChallenge_probOutput_true
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (cloudKey : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    Pr[= true | do
      let bit ← $ᵗ Bool
      let (message₀, message₁, state) ← adversary.chooseMessages cloudKey
      let transcript ←
        $ᵗ (FormalProof4FHE.LWE.BatchTranscript (ZMod q) prefixDimension 1)
      let ciphertext := Encryption.Security.challengeCiphertext encode
        (if bit then message₀ else message₁) transcript
      let guess ← adversary.distinguish state ciphertext
      return (bit == guess)] = 1 / 2 := by
  let preGame : ProbComp
      (Bool × (Message × Message × adversary.State)) := do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages cloudKey
    return (bit, messages)
  let shiftedCont := fun
      (pre : Bool × (Message × Message × adversary.State))
      (transcript :
        FormalProof4FHE.LWE.BatchTranscript (ZMod q) prefixDimension 1) ↦ do
    let message := if pre.1 then pre.2.1 else pre.2.2.1
    let ciphertext := Encryption.Security.challengeCiphertext encode message transcript
    let guess ← adversary.distinguish pre.2.2.2 ciphertext
    return (pre.1 == guess)
  let unshiftedCont := fun
      (pre : Bool × (Message × Message × adversary.State))
      (transcript :
        FormalProof4FHE.LWE.BatchTranscript (ZMod q) prefixDimension 1) ↦ do
    let guess ← adversary.distinguish pre.2.2.2
      (Encryption.Security.unshiftedCiphertext transcript)
    return (pre.1 == guess)
  calc
    _ = Pr[= true | preGame >>= fun pre ↦
          ($ᵗ (FormalProof4FHE.LWE.BatchTranscript (ZMod q) prefixDimension 1)) >>=
            fun transcript ↦ shiftedCont pre transcript] := by
      simp [preGame, shiftedCont, monad_norm]
    _ = Pr[= true | preGame >>= fun pre ↦
          ($ᵗ (FormalProof4FHE.LWE.BatchTranscript (ZMod q) prefixDimension 1)) >>=
            fun transcript ↦ unshiftedCont pre transcript] := by
      refine probOutput_bind_congr' preGame true fun pre ↦ ?_
      let message := if pre.1 then pre.2.1 else pre.2.2.1
      simpa [shiftedCont, unshiftedCont, message,
          Encryption.Security.challengeCiphertext_eq_unshifted_shift] using
        (probOutput_bind_bijective_uniform_cross
          (FormalProof4FHE.LWE.BatchTranscript (ZMod q) prefixDimension 1)
          (Encryption.Security.shiftInputTranscript
            (lweDimension := prefixDimension) (encode message))
          (Encryption.Security.shiftInputTranscript_bijective
            (lweDimension := prefixDimension) (encode message))
          (fun transcript ↦ do
            let guess ← adversary.distinguish pre.2.2.2
              (Encryption.Security.unshiftedCiphertext transcript)
            return (pre.1 == guess)) true)
    _ = Pr[= true | adversary.chooseMessages cloudKey >>= fun messages ↦
          ($ᵗ Bool) >>= fun bit ↦
          ($ᵗ (FormalProof4FHE.LWE.BatchTranscript (ZMod q) prefixDimension 1)) >>=
            fun transcript ↦ unshiftedCont (bit, messages) transcript] := by
      simpa [preGame, unshiftedCont, monad_norm] using
        (probOutput_bind_bind_swap ($ᵗ Bool) (adversary.chooseMessages cloudKey)
          (fun bit messages ↦ do
            let transcript ←
              $ᵗ (FormalProof4FHE.LWE.BatchTranscript (ZMod q) prefixDimension 1)
            unshiftedCont (bit, messages) transcript) true)
    _ = 1 / 2 := by
      rw [probOutput_bind_eq_tsum]
      calc
        _ = ∑' messages, Pr[= messages | adversary.chooseMessages cloudKey] * (1 / 2) := by
          refine tsum_congr fun messages : Message × Message × adversary.State ↦ ?_
          congr 1
          simpa [unshiftedCont, monad_norm] using
            (Encryption.Security.fairBit_eq_independentGuess
              (do
                let transcript ←
                  $ᵗ (FormalProof4FHE.LWE.BatchTranscript
                    (ZMod q) prefixDimension 1)
                adversary.distinguish messages.2.2
                  (Encryption.Security.unshiftedCiphertext transcript)))
        _ = 1 / 2 := by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

/-- The uniform branch of the unshifted two-block reduction is an information-theoretic one-time
pad and succeeds with probability exactly one half. -/
theorem zeroJointLweReduction_game1_probOutput_true
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    Pr[= true | LearningWithErrors.game1
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
        keySwitchErrorSampler inputErrorSampler)
      (zeroJointLweReduction keySwitchErrorSampler inputErrorSampler
        encode adversary)] = 1 / 2 := by
  let samples := keySwitchSamples suffixDimension keySwitchLevels
  let FirstTranscript :=
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) prefixDimension samples
  let SecondTranscript :=
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) prefixDimension 1
  let firstTranscripts : ProbComp FirstTranscript := $ᵗ FirstTranscript
  let secondTranscripts : ProbComp SecondTranscript := $ᵗ SecondTranscript
  let contexts := uniformBootstrapContext q prefixDimension suffixDimension tgswLevels
  let finish := fun
      (context : BinarySecret suffixDimension ×
        Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
          suffixDimension tgswLevels)
      (first : FirstTranscript) (bit : Bool)
      (messages : Message × Message × adversary.State)
      (second : SecondTranscript) ↦ do
    let ciphertext := Encryption.Security.challengeCiphertext encode
      (if bit then messages.1 else messages.2.1) second
    let guess ← adversary.distinguish messages.2.2 ciphertext
    return (bit == guess)
  rw [LearningWithErrors.game1]
  simp only [jointLweProblem, Encryption.Security.jointLweProblem]
  rw [FormalProof4FHE.LWE.TwoBlock.heterogeneousUniformDistr_eq_uniformSample]
  calc
    _ = Pr[= true | ($ᵗ (FirstTranscript × SecondTranscript)) >>= fun transcripts ↦
        zeroJointLweReduction keySwitchErrorSampler inputErrorSampler encode adversary
          (FormalProof4FHE.LWE.TwoBlock.ofTranscriptPair transcripts)] := by
      simpa [samples, FirstTranscript, SecondTranscript] using
        (probOutput_bind_bijective_uniform_cross
          (α := FormalProof4FHE.LWE.TwoBlock.Transcript
            (ZMod q) prefixDimension samples 1)
          (β := FirstTranscript × SecondTranscript)
          FormalProof4FHE.LWE.TwoBlock.toTranscriptPair
          (FormalProof4FHE.LWE.TwoBlock.toTranscriptPair_bijective
            (R := ZMod q) (dimension := prefixDimension)
            (firstSamples := samples) (secondSamples := 1))
          (fun transcripts ↦
            zeroJointLweReduction keySwitchErrorSampler inputErrorSampler encode adversary
              (FormalProof4FHE.LWE.TwoBlock.ofTranscriptPair transcripts)) true)
    _ = Pr[= true | firstTranscripts >>= fun first ↦
        secondTranscripts >>= fun second ↦
        contexts >>= fun context ↦
        ($ᵗ Bool) >>= fun bit ↦
        adversary.chooseMessages ⟨context.2, first⟩ >>= fun messages ↦
        finish context first bit messages second] := by
      have uniformProduct :
          ($ᵗ (FirstTranscript × SecondTranscript) :
            ProbComp (FirstTranscript × SecondTranscript)) =
          Prod.mk <$> firstTranscripts <*> secondTranscripts := rfl
      rw [uniformProduct]
      simp [firstTranscripts, secondTranscripts, contexts, finish,
        zeroJointLweReduction, transcriptGame,
        Encryption.Security.keySwitchTranscript,
        Encryption.Security.inputTranscript,
        FormalProof4FHE.LWE.TwoBlock.ofTranscriptPair,
        FormalProof4FHE.LWE.TwoBlock.toTranscriptPair, monad_norm]
    _ = Pr[= true | firstTranscripts >>= fun first ↦
        contexts >>= fun context ↦
        secondTranscripts >>= fun second ↦
        ($ᵗ Bool) >>= fun bit ↦
        adversary.chooseMessages ⟨context.2, first⟩ >>= fun messages ↦
        finish context first bit messages second] := by
      refine probOutput_bind_congr' firstTranscripts true fun first ↦ ?_
      exact probOutput_bind_bind_swap secondTranscripts contexts
        (fun second context ↦
          ($ᵗ Bool) >>= fun bit ↦
          adversary.chooseMessages ⟨context.2, first⟩ >>= fun messages ↦
          finish context first bit messages second) true
    _ = Pr[= true | firstTranscripts >>= fun first ↦
        contexts >>= fun context ↦
        ($ᵗ Bool) >>= fun bit ↦
        secondTranscripts >>= fun second ↦
        adversary.chooseMessages ⟨context.2, first⟩ >>= fun messages ↦
        finish context first bit messages second] := by
      refine probOutput_bind_congr' firstTranscripts true fun first ↦ ?_
      refine probOutput_bind_congr' contexts true fun context ↦ ?_
      exact probOutput_bind_bind_swap secondTranscripts ($ᵗ Bool)
        (fun second bit ↦
          adversary.chooseMessages ⟨context.2, first⟩ >>= fun messages ↦
          finish context first bit messages second) true
    _ = Pr[= true | firstTranscripts >>= fun first ↦
        contexts >>= fun context ↦
        ($ᵗ Bool) >>= fun bit ↦
        adversary.chooseMessages ⟨context.2, first⟩ >>= fun messages ↦
        secondTranscripts >>= fun second ↦
        finish context first bit messages second] := by
      refine probOutput_bind_congr' firstTranscripts true fun first ↦ ?_
      refine probOutput_bind_congr' contexts true fun context ↦ ?_
      refine probOutput_bind_congr' ($ᵗ Bool) true fun bit ↦ ?_
      exact probOutput_bind_bind_swap secondTranscripts
        (adversary.chooseMessages ⟨context.2, first⟩)
        (fun second messages ↦ finish context first bit messages second) true
    _ = 1 / 2 := by
      rw [probOutput_bind_eq_tsum]
      calc
        _ = ∑' first, Pr[= first | firstTranscripts] * (1 / 2) := by
          refine tsum_congr fun first : FirstTranscript ↦ ?_
          congr 1
          rw [probOutput_bind_eq_tsum]
          calc
            _ = ∑' context, Pr[= context | contexts] * (1 / 2) := by
              refine tsum_congr fun context : BinarySecret suffixDimension ×
                  Native.SharedRandomnessOneCycle.SharedBootstrappingKey q
                    prefixDimension suffixDimension tgswLevels ↦ ?_
              congr 1
              simpa [finish, firstTranscripts, secondTranscripts] using
                (uniformChallenge_probOutput_true encode adversary
                  (⟨context.2, first⟩ : CloudKey q prefixDimension suffixDimension
                    tgswLevels keySwitchLevels))
            _ = 1 / 2 := by
              rw [ENNReal.tsum_mul_right,
                tsum_probOutput_eq_one' (by simp [contexts]), one_mul]
        _ = 1 / 2 := by
          rw [ENNReal.tsum_mul_right,
            tsum_probOutput_eq_one' (by simp [firstTranscripts]), one_mul]

/-- The translated reduction has the same exactly fair uniform branch. -/
theorem jointLweReduction_game1_probOutput_true
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    Pr[= true | LearningWithErrors.game1
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
        keySwitchErrorSampler inputErrorSampler)
      (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
        encode adversary)] = 1 / 2 := by
  rw [evalDist_ext_iff.mp
    (jointLweReduction_game1_evalDist_eq_zero keySwitchErrorSampler inputErrorSampler
      keySwitchGadget encode adversary) true]
  exact zeroJointLweReduction_game1_probOutput_true
    keySwitchErrorSampler inputErrorSampler encode adversary

/-- The absolute IND advantage of the independent uniform-BRK endpoint is exactly the advantage
of the constructed heterogeneous two-block binary-secret LWE distinguisher. -/
theorem abs_signedAdvantage_independentUniformBootstrap_eq_jointLwe
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    |Encryption.signedAdvantage
      (independentUniformBootstrapGame keySwitchErrorSampler inputErrorSampler
        keySwitchGadget encode adversary)| =
      LearningWithErrors.advantage
        (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
          keySwitchErrorSampler inputErrorSampler)
        (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
          encode adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold Encryption.signedAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (independentUniformBootstrapGame_evalDist_eq_jointLwe_game0
        keySwitchErrorSampler inputErrorSampler keySwitchGadget encode adversary) true,
    jointLweReduction_game1_probOutput_true keySwitchErrorSampler inputErrorSampler
      keySwitchGadget encode adversary]
  norm_num

/-- With uniform ring-row errors, honest shared-key TFHE one-time confidentiality is exactly the
ordinary suffix-KSK-plus-input LWE advantage. -/
theorem abs_signedAdvantage_real_uniformRingError_eq_jointLwe
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    |Encryption.signedAdvantage
      (realGame ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
        encode adversary)| =
      LearningWithErrors.advantage
        (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
          keySwitchErrorSampler inputErrorSampler)
        (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
          encode adversary) := by
  have hGame := realGame_uniformRingError_evalDist_eq_independent
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary
  have hSigned :
      Encryption.signedAdvantage
          (realGame ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
            keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
            encode adversary) =
        Encryption.signedAdvantage
          (independentUniformBootstrapGame keySwitchErrorSampler inputErrorSampler
            keySwitchGadget encode adversary) := by
    unfold Encryption.signedAdvantage
    rw [evalDist_ext_iff.mp hGame true]
  rw [hSigned]
  exact abs_signedAdvantage_independentUniformBootstrap_eq_jointLwe
    keySwitchErrorSampler inputErrorSampler keySwitchGadget encode adversary

/-- **End-to-end shared-randomness TFHE security.** For every finite executable ring-error
sampler, honest one-time IND advantage is at most one complete BRK sampler-replacement cost plus
one heterogeneous binary-secret LWE advantage containing the suffix KSK and input row. -/
theorem abs_signedAdvantage_real_le_ringErrorDistance_add_jointLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    |Encryption.signedAdvantage
      (realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      (TFHE.SamplerReplacement.bootstrappingErrorCount
          1 tgswLevels prefixDimension : ℝ) *
          tvDist ringErrorSampler
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) +
        LearningWithErrors.advantage
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
            keySwitchErrorSampler inputErrorSampler)
          (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
            encode adversary) := by
  let uniformRingError : ProbComp
      (RLWE.Rq q (prefixDimension + suffixDimension)) :=
    $ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))
  let actualGame := realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary
  let uniformGame := realGame uniformRingError keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary
  let replacementBound :=
    (TFHE.SamplerReplacement.bootstrappingErrorCount
        1 tgswLevels prefixDimension : ℝ) *
      tvDist ringErrorSampler uniformRingError
  have hTV : tvDist actualGame uniformGame ≤ replacementBound := by
    simpa [actualGame, uniformGame, realGame, replacementBound] using
      (Native.SharedRandomnessOneCycle.tvDist_realSecretContinuationGame_ringError_le
        q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler uniformRingError keySwitchErrorSampler tgswGadget
        keySwitchGadget (oneTimeContinuation inputErrorSampler encode adversary))
  have hProbability :
      |(Pr[= true | actualGame]).toReal - (Pr[= true | uniformGame]).toReal| ≤
        tvDist actualGame uniformGame :=
    abs_probOutput_toReal_sub_le_tvDist actualGame uniformGame
  have hUniform :
      |Encryption.signedAdvantage uniformGame| =
        LearningWithErrors.advantage
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
            keySwitchErrorSampler inputErrorSampler)
          (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
            encode adversary) := by
    simpa [uniformGame, uniformRingError] using
      (abs_signedAdvantage_real_uniformRingError_eq_jointLwe
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
        encode adversary)
  calc
    |Encryption.signedAdvantage
        (realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary)| =
        |(Pr[= true | actualGame]).toReal - 1 / 2| := by
      rfl
    _ ≤ |(Pr[= true | actualGame]).toReal -
          (Pr[= true | uniformGame]).toReal| +
        |(Pr[= true | uniformGame]).toReal - 1 / 2| :=
      abs_sub_le _ _ _
    _ ≤ tvDist actualGame uniformGame +
        |Encryption.signedAdvantage uniformGame| := by
      exact add_le_add hProbability le_rfl
    _ ≤ replacementBound + |Encryption.signedAdvantage uniformGame| := by
      exact add_le_add hTV le_rfl
    _ = (TFHE.SamplerReplacement.bootstrappingErrorCount
          1 tgswLevels prefixDimension : ℝ) *
          tvDist ringErrorSampler
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) +
        LearningWithErrors.advantage
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
            keySwitchErrorSampler inputErrorSampler)
          (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
            encode adversary) := by
      rw [hUniform]

/-- Equal KSK and input noises flatten the unequal endpoint exactly to one conventional
binary-secret batch-LWE problem with `suffixDimension * keySwitchLevels + 1` rows. -/
theorem abs_signedAdvantage_real_le_ringErrorDistance_add_batchLwe_of_same_noise
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    |Encryption.signedAdvantage
      (realGame ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      (TFHE.SamplerReplacement.bootstrappingErrorCount
          1 tgswLevels prefixDimension : ℝ) *
          tvDist ringErrorSampler
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels + 1) errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (jointLweReduction errorSampler errorSampler keySwitchGadget
              encode adversary)) := by
  calc
    |Encryption.signedAdvantage
        (realGame ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
      (TFHE.SamplerReplacement.bootstrappingErrorCount
          1 tgswLevels prefixDimension : ℝ) *
          tvDist ringErrorSampler
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) +
        LearningWithErrors.advantage
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels
            errorSampler errorSampler)
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary) :=
      abs_signedAdvantage_real_le_ringErrorDistance_add_jointLwe
        ringErrorSampler errorSampler errorSampler tgswGadget keySwitchGadget
        encode adversary
    _ = (TFHE.SamplerReplacement.bootstrappingErrorCount
          1 tgswLevels prefixDimension : ℝ) *
          tvDist ringErrorSampler
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels + 1) errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (jointLweReduction errorSampler errorSampler keySwitchGadget
              encode adversary)) := by
      congr 1
      change LearningWithErrors.advantage
          (FormalProof4FHE.LWE.TwoBlock.problem prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels) 1
            (Native.sampleLweSecret prefixDimension) embedBinarySecret errorSampler)
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary) = _
      simpa [Native.KeySwitchSecurity.binaryLweProblem] using
        (FormalProof4FHE.LWE.TwoBlock.advantage_eq_batch
          prefixDimension (keySwitchSamples suffixDimension keySwitchLevels) 1
          (Native.sampleLweSecret prefixDimension) embedBinarySecret errorSampler
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary))

end

end FormalProof4FHE.TFHE.Encryption.SharedRandomnessOneCycle
