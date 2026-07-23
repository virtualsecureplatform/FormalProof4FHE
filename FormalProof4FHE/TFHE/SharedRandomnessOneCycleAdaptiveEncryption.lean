/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveEncryptionSecurity
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleEncryption

/-!
# Reusable-Key Adaptive Security for Shared-Randomness One-Cycle TFHE

This module lifts the one-time shared-randomness theorem to a sequential query-bounded encryption
oracle. One hidden bit and one cloud key are reused for all queries, and later message pairs may
depend on earlier ciphertexts. An eager tape contains exactly `queryCount` scalar-LWE input rows.

After the self-circular BRK is replaced by an independent uniform BRK, the complete suffix KSK and
input tape form one unequal two-block binary-secret LWE transcript under the prefix key.
-/

open Matrix OracleComp OracleSpec

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle

noncomputable section

variable {Message : Type}
  {q prefixDimension suffixDimension tgswLevels keySwitchLevels queryCount : ℕ} [NeZero q]

/-- Shared-randomness cloud key used by the adaptive encryption oracle. -/
abbrev CloudKey
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) :=
  Encryption.SharedRandomnessOneCycle.CloudKey q prefixDimension suffixDimension
    tgswLevels keySwitchLevels

/-- Query-bounded adaptive adversary for the shared-randomness cloud-key layout. -/
abbrev SharedAdversary (Message : Type)
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) :=
  Adaptive.Adversary Message
    (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels)
    (TLWE.Ciphertext (ZMod q) prefixDimension)

/-- Execute an adaptive adversary from an ordered matrix-form tape of scalar LWE rows. -/
noncomputable def runFromTranscript
    (bit : Bool) (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (cloudKey : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels)
    {samples : ℕ}
    (transcript : FormalProof4FHE.LWE.BatchTranscript
      (ZMod q) prefixDimension samples) : ProbComp Bool :=
  (simulateQ
      (GeneralizedSubspaceLWE.Adaptive.sourceImpl
        ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) prefixDimension)).withPregen
      (simulateQ
        (Adaptive.sourceReduction (lweDimension := prefixDimension) bit encode)
        (adversary cloudKey))).run'
    (GeneralizedSubspaceLWE.Adaptive.sourceSampleSeed
      (GeneralizedSubspaceLWE.Adaptive.batchSamples transcript))

/-- Query-bounded downstream experiment for an already generated master key and cloud key. -/
noncomputable def continuation
    (queryCount : ℕ) (inputErrorSampler : ProbComp (ZMod q))
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    Native.SharedRandomnessOneCycle.SecretContinuation q prefixDimension suffixDimension
      tgswLevels keySwitchLevels :=
  fun masterSecret bootstrapKey keySwitchKey ↦ do
    let tape ← TLWE.batchEncrypt prefixDimension queryCount inputErrorSampler
      (embedBinarySecret (Native.SharedRandomnessOneCycle.prefixSecret masterSecret)) 0
    let bit ← $ᵗ Bool
    let guess ← runFromTranscript bit encode adversary
      ⟨bootstrapKey, keySwitchKey⟩ tape
    return (bit == guess)

/-- Honest reusable-key adaptive TFHE encryption game. -/
noncomputable def realGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) : ProbComp Bool :=
  Native.SharedRandomnessOneCycle.realSecretContinuationGame q prefixDimension
    suffixDimension tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget
    (continuation queryCount inputErrorSampler encode adversary)

/-- Uniform-BRK endpoint retaining one sampled master key and the real suffix-only KSK. -/
noncomputable def masterUniformBootstrapGame
    (queryCount : ℕ)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) : ProbComp Bool := do
  let masterSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  let bootstrappingKey ← $ᵗ
    (Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
      suffixDimension tgswLevels)
  let keySwitchKey ← Native.SharedRandomnessOneCycle.generateKeySwitchKey q
    prefixDimension suffixDimension keySwitchLevels keySwitchErrorSampler
    keySwitchGadget masterSecret
  continuation queryCount inputErrorSampler encode adversary
    masterSecret bootstrappingKey keySwitchKey

/-- Equivalent uniform-BRK endpoint with independent prefix and suffix keys. -/
noncomputable def independentUniformBootstrapGame
    (queryCount : ℕ)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) : ProbComp Bool := do
  let prefixKey ← Native.sampleLweSecret prefixDimension
  let suffixKey ← Native.sampleLweSecret suffixDimension
  let bootstrappingKey ← $ᵗ
    (Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
      suffixDimension tgswLevels)
  let keySwitchKey ← Native.generateKeySwitchKey q prefixDimension suffixDimension
    keySwitchLevels keySwitchErrorSampler keySwitchGadget suffixKey prefixKey
  let tape ← TLWE.batchEncrypt prefixDimension queryCount inputErrorSampler
    (embedBinarySecret prefixKey) 0
  let bit ← $ᵗ Bool
  let guess ← runFromTranscript bit encode adversary
    ⟨bootstrappingKey, keySwitchKey⟩ tape
  return (bit == guess)

/-- Uniform ring-row errors resample the complete real BRK independently inside the adaptive
oracle continuation. -/
theorem realGame_uniformRingError_evalDist_eq_masterUniformBootstrap
    (queryCount : ℕ)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    evalDist (realGame queryCount
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary) =
    evalDist (masterUniformBootstrapGame queryCount keySwitchErrorSampler
      inputErrorSampler keySwitchGadget encode adversary) := by
  unfold realGame Native.SharedRandomnessOneCycle.realSecretContinuationGame
    masterUniformBootstrapGame
  refine evalDist_bind_congr'
    (Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) fun masterSecret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (Native.SharedRandomnessOneCycle.generateBootstrappingKey_uniformError_evalDist
      q prefixDimension suffixDimension tgswLevels tgswGadget masterSecret)
    (fun bootstrappingKey ↦
      Native.SharedRandomnessOneCycle.generateKeySwitchKey q prefixDimension
          suffixDimension keySwitchLevels keySwitchErrorSampler keySwitchGadget
          masterSecret >>= fun keySwitchKey ↦
        continuation queryCount inputErrorSampler encode adversary
          masterSecret bootstrappingKey keySwitchKey)

/-- Splitting the master key gives the independent prefix/suffix adaptive endpoint exactly. -/
theorem masterUniformBootstrapGame_evalDist_eq_independent
    (queryCount : ℕ)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    evalDist (masterUniformBootstrapGame queryCount keySwitchErrorSampler
      inputErrorSampler keySwitchGadget encode adversary) =
    evalDist (independentUniformBootstrapGame queryCount keySwitchErrorSampler
      inputErrorSampler keySwitchGadget encode adversary) := by
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
    let tape ← TLWE.batchEncrypt prefixDimension queryCount inputErrorSampler
      (embedBinarySecret keys.1) 0
    let bit ← $ᵗ Bool
    let guess ← runFromTranscript bit encode adversary
      ⟨bootstrappingKey, keySwitchKey⟩ tape
    return (bit == guess)
  have hSampler : evalDist splitSampler = evalDist independentSampler := by
    exact Native.SharedRandomnessOneCycle.sampleRingSecret_prefix_suffix_evalDist
      prefixDimension suffixDimension
  have hBind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hSampler finish
  simpa [masterUniformBootstrapGame, independentUniformBootstrapGame, continuation,
    Native.SharedRandomnessOneCycle.generateKeySwitchKey, splitSampler,
    independentSampler, finish, Native.SharedRandomnessOneCycle.splitNestedSecret,
    bind_assoc, monad_norm] using hBind

/-- Complete adaptive uniform-BRK normalization to independent prefix/suffix keys. -/
theorem realGame_uniformRingError_evalDist_eq_independent
    (queryCount : ℕ)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    evalDist (realGame queryCount
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary) =
    evalDist (independentUniformBootstrapGame queryCount keySwitchErrorSampler
      inputErrorSampler keySwitchGadget encode adversary) :=
  (realGame_uniformRingError_evalDist_eq_masterUniformBootstrap queryCount
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary).trans
      (masterUniformBootstrapGame_evalDist_eq_independent queryCount
        keySwitchErrorSampler inputErrorSampler keySwitchGadget encode adversary)

/-! ## Complete suffix-KSK plus adaptive-input LWE transcript -/

/-- Number of rows in the suffix-only KSK. -/
abbrev keySwitchSamples (suffixDimension keySwitchLevels : ℕ) : ℕ :=
  Encryption.SharedRandomnessOneCycle.keySwitchSamples suffixDimension keySwitchLevels

/-- Heterogeneous two-block LWE problem for every suffix-KSK row and every charged adaptive
input query. -/
abbrev jointLweProblem
    (q prefixDimension suffixDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)) :=
  Adaptive.jointLweProblem q prefixDimension
    (keySwitchSamples suffixDimension keySwitchLevels) queryCount
    keySwitchErrorSampler inputErrorSampler

/-- Independent suffix-key and uniform-BRK context at the normalized endpoint. -/
abbrev uniformBootstrapContext
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q] :=
  Encryption.SharedRandomnessOneCycle.uniformBootstrapContext q prefixDimension
    suffixDimension tgswLevels

/-- Complete suffix-KSK message vector. -/
abbrev keySwitchMessage
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (suffixKey : BinarySecret suffixDimension) :
    Fin (keySwitchSamples suffixDimension keySwitchLevels) → ZMod q :=
  Encryption.SharedRandomnessOneCycle.keySwitchMessage keySwitchGadget suffixKey

/-- Run the adaptive game from a supplied two-block public transcript. -/
noncomputable def transcriptGame
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (bootstrapKey :
      Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
        suffixDimension tgswLevels)
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript (ZMod q) prefixDimension
      (keySwitchSamples suffixDimension keySwitchLevels) queryCount) : ProbComp Bool := do
  let bit ← $ᵗ Bool
  let guess ← runFromTranscript bit encode adversary
    ⟨bootstrapKey, MultiQuery.keySwitchTranscript transcript⟩
    (MultiQuery.inputTranscript transcript)
  return (bit == guess)

/-- Joint-LWE reduction translating the first block by suffix-key gadget messages. -/
noncomputable def jointLweReduction
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    LearningWithErrors.Adversary
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
        keySwitchErrorSampler inputErrorSampler) :=
  fun transcript ↦ do
    let context ← uniformBootstrapContext q prefixDimension suffixDimension tgswLevels
    transcriptGame encode adversary context.2
      (Encryption.Security.shiftFirstBlock
        (keySwitchMessage keySwitchGadget context.1) transcript)

/-- Unshifted comparison reduction for the uniform branch. -/
noncomputable def zeroJointLweReduction
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    LearningWithErrors.Adversary
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
        keySwitchErrorSampler inputErrorSampler) :=
  fun transcript ↦ do
    let context ← uniformBootstrapContext q prefixDimension suffixDimension tgswLevels
    transcriptGame encode adversary context.2 transcript

/-- The independent uniform-BRK adaptive endpoint is exactly game 0 of the translated
query-counted two-block binary-secret LWE problem. -/
theorem independentUniformBootstrapGame_evalDist_eq_jointLwe_game0
    (queryCount : ℕ)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    evalDist (independentUniformBootstrapGame queryCount keySwitchErrorSampler
      inputErrorSampler keySwitchGadget encode adversary) =
    evalDist (LearningWithErrors.game0
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
        keySwitchErrorSampler inputErrorSampler)
      (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
        encode adversary)) := by
  let samples := keySwitchSamples suffixDimension keySwitchLevels
  let FirstChallenge := Matrix (Fin prefixDimension) (Fin samples) (ZMod q)
  let SecondChallenge := Matrix (Fin prefixDimension) (Fin queryCount) (ZMod q)
  let FirstError := Fin samples → ZMod q
  let SecondError := Fin queryCount → ZMod q
  let prefixSecrets := Native.sampleLweSecret prefixDimension
  let contexts := uniformBootstrapContext q prefixDimension suffixDimension tgswLevels
  let firstChallenges : ProbComp FirstChallenge := $ᵗ FirstChallenge
  let secondChallenges : ProbComp SecondChallenge := $ᵗ SecondChallenge
  let firstErrors : ProbComp FirstError :=
    ProbComp.sampleIID samples keySwitchErrorSampler
  let secondErrors : ProbComp SecondError :=
    ProbComp.sampleIID queryCount inputErrorSampler
  let finish := fun (prefixKey : BinarySecret prefixDimension)
      (context : BinarySecret suffixDimension ×
        Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
          suffixDimension tgswLevels)
      (challenge : FirstChallenge) (error : FirstError)
      (inputChallenge : SecondChallenge) (inputError : SecondError) ↦ do
    let bit ← $ᵗ Bool
    let guess ← runFromTranscript bit encode adversary
      ⟨context.2, TLWE.batchAssemble (embedBinarySecret prefixKey) challenge
        (keySwitchMessage keySwitchGadget context.1) error⟩
      (TLWE.batchAssemble (embedBinarySecret prefixKey) inputChallenge 0 inputError)
    return (bit == guess)
  have native_eq :
      independentUniformBootstrapGame queryCount keySwitchErrorSampler
          inputErrorSampler keySwitchGadget encode adversary =
        (prefixSecrets >>= fun prefixKey ↦
          contexts >>= fun context ↦
          firstChallenges >>= fun challenge ↦
          firstErrors >>= fun error ↦
          secondChallenges >>= fun inputChallenge ↦
          secondErrors >>= fun inputError ↦
          finish prefixKey context challenge error inputChallenge inputError) := by
    simp [independentUniformBootstrapGame, TLWE.batchEncrypt,
      Native.generateKeySwitchKey, prefixSecrets, contexts,
      Encryption.SharedRandomnessOneCycle.uniformBootstrapContext,
      samples, keySwitchSamples, FirstChallenge, SecondChallenge, FirstError, SecondError,
      firstChallenges, secondChallenges, firstErrors, secondErrors, finish,
      keySwitchMessage, Encryption.SharedRandomnessOneCycle.keySwitchMessage,
      bind_assoc, monad_norm]
  have lwe_eq :
      LearningWithErrors.game0
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
            keySwitchErrorSampler inputErrorSampler)
          (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
            encode adversary) =
        (firstChallenges >>= fun challenge ↦
          secondChallenges >>= fun inputChallenge ↦
          prefixSecrets >>= fun prefixKey ↦
          firstErrors >>= fun error ↦
          secondErrors >>= fun inputError ↦
          contexts >>= fun context ↦
          finish prefixKey context challenge error inputChallenge inputError) := by
    have uniformChallengeProduct :
        ($ᵗ (FormalProof4FHE.LWE.TwoBlock.Challenge
          (ZMod q) prefixDimension samples queryCount) :
          ProbComp (FormalProof4FHE.LWE.TwoBlock.Challenge
            (ZMod q) prefixDimension samples queryCount)) =
        Prod.mk <$> firstChallenges <*> secondChallenges := rfl
    rw [LearningWithErrors.game0]
    simp only [jointLweProblem, Adaptive.jointLweProblem, MultiQuery.jointLweProblem]
    unfold LearningWithErrors.distr
    simp only [FormalProof4FHE.LWE.TwoBlock.heterogeneousProblem]
    rw [uniformChallengeProduct]
    simp [jointLweReduction, transcriptGame,
      MultiQuery.keySwitchTranscript_shiftFirstBlock_real,
      Adaptive.inputTranscript_real,
      samples, keySwitchSamples, FirstChallenge, SecondChallenge, FirstError, SecondError,
      prefixSecrets, contexts, firstChallenges, secondChallenges,
      firstErrors, secondErrors, finish, bind_assoc, monad_norm]
  rw [native_eq, lwe_eq]
  exact Encryption.Security.evalDist_bind_six_reorder prefixSecrets contexts
    firstChallenges firstErrors secondChallenges secondErrors finish

/-! ## Bounded eager tapes and the adaptive uniform branch -/

/-- The source translation consumes at most one LWE sample per charged encryption query for the
shared cloud-key adversary type. -/
theorem sourceReduction_isQueryBoundP
    (bit : Bool) (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (cloudKey : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels)
    (hbound : IsQueryBoundP (adversary cloudKey)
      (Adaptive.isEncryptionQuery (Message := Message)
        (Ciphertext := TLWE.Ciphertext (ZMod q) prefixDimension)) queryCount) :
    IsQueryBoundP
      (simulateQ (Adaptive.sourceReduction (lweDimension := prefixDimension) bit encode)
        (adversary cloudKey))
      (GeneralizedSubspaceLWE.Adaptive.isSourceSample
        (F := ZMod q) (dimension := prefixDimension)) queryCount := by
  letI : Inhabited (ZMod q) := ⟨0⟩
  letI : IsUniformSpec
      (Unit →ₒ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) prefixDimension) :=
    IsUniformSpec.ofFintypeInhabited _
  apply IsQueryBoundP.simulateQ_of_step hbound
  · intro index hcharged
    rcases index with uniformIndex | messages
    · simp [Adaptive.isEncryptionQuery] at hcharged
    · simp only [Adaptive.sourceReduction]
      let sourceQuery : OracleComp
          (GeneralizedSubspaceLWE.Adaptive.SourceInterface (ZMod q) prefixDimension)
          (GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) prefixDimension) :=
        liftM ((GeneralizedSubspaceLWE.Adaptive.SourceInterface
          (ZMod q) prefixDimension).query (Sum.inr ()))
      let sourceContinuation := fun
          (sample : GeneralizedSubspaceLWE.Adaptive.LWESample
            (ZMod q) prefixDimension) ↦
        (pure ⟨sample.1,
          sample.2 + encode (if bit then messages.1 else messages.2)⟩ :
            OracleComp
              (GeneralizedSubspaceLWE.Adaptive.SourceInterface
                (ZMod q) prefixDimension)
              (TLWE.Ciphertext (ZMod q) prefixDimension))
      change IsQueryBoundP (sourceQuery >>= sourceContinuation)
        (GeneralizedSubspaceLWE.Adaptive.isSourceSample
          (F := ZMod q) (dimension := prefixDimension)) 1
      have hsource : IsQueryBoundP sourceQuery
          (GeneralizedSubspaceLWE.Adaptive.isSourceSample
            (F := ZMod q) (dimension := prefixDimension)) 1 := by
        dsimp [sourceQuery]
        change (¬ GeneralizedSubspaceLWE.Adaptive.isSourceSample
            (F := ZMod q) (dimension := prefixDimension) (Sum.inr ()) ∨ 0 < 1) ∧
          ∀ _ : GeneralizedSubspaceLWE.Adaptive.LWESample
            (ZMod q) prefixDimension, True
        simp [GeneralizedSubspaceLWE.Adaptive.isSourceSample]
      have hcontinuation : ∀ sample ∈ support sourceQuery,
          IsQueryBoundP (sourceContinuation sample)
            (GeneralizedSubspaceLWE.Adaptive.isSourceSample
              (F := ZMod q) (dimension := prefixDimension)) 0 := by
        simp [sourceContinuation]
      simpa [sourceQuery, sourceContinuation] using
        isQueryBoundP_bind (n := 1) (m := 0) hsource hcontinuation
  · intro index hfree
    rcases index with uniformIndex | messages
    · exact GeneralizedSubspaceLWE.Adaptive.isQueryBoundP_liftProbComp_left
        (F := ZMod q) (dimension := prefixDimension)
        (liftM (unifSpec.query uniformIndex) : ProbComp (unifSpec.Range uniformIndex))
    · simp [Adaptive.isEncryptionQuery] at hfree

/-- Installing a uniform matrix transcript as an eager tape is distributionally equal to the
online uniform source for every bounded shared-key adversary. -/
theorem evalDist_uniformTranscript_runFromTranscript_eq_online
    (queryCount : ℕ) (bit : Bool) (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (cloudKey : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels)
    (hbound : IsQueryBoundP (adversary cloudKey)
      (Adaptive.isEncryptionQuery (Message := Message)
        (Ciphertext := TLWE.Ciphertext (ZMod q) prefixDimension)) queryCount) :
    evalDist (do
        let transcript ←
          $ᵗ (FormalProof4FHE.LWE.BatchTranscript
            (ZMod q) prefixDimension queryCount)
        runFromTranscript bit encode adversary cloudKey transcript) =
      evalDist
        (simulateQ
          (GeneralizedSubspaceLWE.Adaptive.sourceImpl
            ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) prefixDimension))
          (simulateQ
            (Adaptive.sourceReduction (lweDimension := prefixDimension) bit encode)
            (adversary cloudKey))) := by
  let Sample := GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) prefixDimension
  let sampleSampler : ProbComp Sample := $ᵗ Sample
  let computation :=
    simulateQ (Adaptive.sourceReduction (lweDimension := prefixDimension) bit encode)
      (adversary cloudKey)
  let finish := fun (sourceSamples : List Sample) ↦
    (simulateQ
      (GeneralizedSubspaceLWE.Adaptive.sourceImpl sampleSampler).withPregen
      computation).run'
      (GeneralizedSubspaceLWE.Adaptive.sourceSampleSeed sourceSamples)
  have hsource : IsQueryBoundP computation
      (GeneralizedSubspaceLWE.Adaptive.isSourceSample
        (F := ZMod q) (dimension := prefixDimension)) queryCount :=
    sourceReduction_isQueryBoundP bit encode adversary cloudKey hbound
  have hbatch := Adaptive.evalDist_uniformBatch_batchSamples_eq_replicate
    (q := q) (lweDimension := prefixDimension) queryCount
  have hbatched := GeneralizedSubspaceLWE.Adaptive.evalDist_sourceImpl_eq_batched
    sampleSampler sampleSampler computation queryCount hsource
  calc
    evalDist (do
        let transcript ←
          $ᵗ (FormalProof4FHE.LWE.BatchTranscript
            (ZMod q) prefixDimension queryCount)
        runFromTranscript bit encode adversary cloudKey transcript) =
      evalDist
        ((GeneralizedSubspaceLWE.Adaptive.batchSamples <$>
            ($ᵗ (FormalProof4FHE.LWE.BatchTranscript
              (ZMod q) prefixDimension queryCount))) >>= finish) := by
          simp [runFromTranscript, Sample, sampleSampler, computation, finish,
            map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (OracleComp.replicate queryCount sampleSampler >>= finish) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hbatch finish
    _ = evalDist (simulateQ
          (GeneralizedSubspaceLWE.Adaptive.sourceImpl sampleSampler)
          computation) := hbatched.symm

/-- Online uniform source execution is bit-independent for the shared cloud-key adversary. -/
theorem evalDist_onlineUniform_eq_plain
    (bit : Bool) (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (cloudKey : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    evalDist
        (simulateQ
          (GeneralizedSubspaceLWE.Adaptive.sourceImpl
            ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) prefixDimension))
          (simulateQ
            (Adaptive.sourceReduction (lweDimension := prefixDimension) bit encode)
            (adversary cloudKey))) =
      evalDist (simulateQ
        (Adaptive.plainUniformImpl
          (Message := Message) (q := q) (lweDimension := prefixDimension))
        (adversary cloudKey)) := by
  rw [← QueryImpl.simulateQ_compose]
  exact GeneralizedSubspaceLWE.Adaptive.evalDist_simulateQ_congr
    (GeneralizedSubspaceLWE.Adaptive.sourceImpl
        ($ᵗ GeneralizedSubspaceLWE.Adaptive.LWESample (ZMod q) prefixDimension) ∘ₛ
      Adaptive.sourceReduction (lweDimension := prefixDimension) bit encode)
    (Adaptive.plainUniformImpl
      (Message := Message) (q := q) (lweDimension := prefixDimension))
    (Adaptive.evalDist_uniformSource_compose_sourceReduction bit encode)
    (adversary cloudKey)

/-- For a fixed cloud key, every query-bounded adaptive adversary wins against the uniform eager
tape with probability exactly one half. -/
theorem uniformAdaptive_probOutput_true
    (queryCount : ℕ) (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (cloudKey : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels)
    (hbound : IsQueryBoundP (adversary cloudKey)
      (Adaptive.isEncryptionQuery (Message := Message)
        (Ciphertext := TLWE.Ciphertext (ZMod q) prefixDimension)) queryCount) :
    Pr[= true | do
      let bit ← $ᵗ Bool
      let transcript ←
        $ᵗ (FormalProof4FHE.LWE.BatchTranscript
          (ZMod q) prefixDimension queryCount)
      let guess ← runFromTranscript bit encode adversary cloudKey transcript
      return (bit == guess)] = 1 / 2 := by
  let plainGuess := simulateQ
    (Adaptive.plainUniformImpl
      (Message := Message) (q := q) (lweDimension := prefixDimension))
    (adversary cloudKey)
  have hgame :
      evalDist (do
        let bit ← $ᵗ Bool
        let transcript ←
          $ᵗ (FormalProof4FHE.LWE.BatchTranscript
            (ZMod q) prefixDimension queryCount)
        let guess ← runFromTranscript bit encode adversary cloudKey transcript
        return (bit == guess)) =
      evalDist (do
        let bit ← $ᵗ Bool
        let guess ← plainGuess
        return (bit == guess)) := by
    refine evalDist_bind_congr' ($ᵗ Bool) fun bit ↦ ?_
    have htape := evalDist_uniformTranscript_runFromTranscript_eq_online
      queryCount bit encode adversary cloudKey hbound
    have honline := evalDist_onlineUniform_eq_plain bit encode adversary cloudKey
    simpa [plainGuess, bind_assoc] using
      (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (htape.trans honline) (fun guess ↦ pure (bit == guess)))
  rw [evalDist_ext_iff.mp hgame true]
  exact Encryption.Security.fairBit_eq_independentGuess plainGuess

/-- Suffix-message translation vanishes in the uniform two-block LWE branch. -/
theorem jointLweReduction_game1_evalDist_eq_zero
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    evalDist (LearningWithErrors.game1
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
        keySwitchErrorSampler inputErrorSampler)
      (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
        encode adversary)) =
    evalDist (LearningWithErrors.game1
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
        keySwitchErrorSampler inputErrorSampler)
      (zeroJointLweReduction keySwitchErrorSampler inputErrorSampler
        encode adversary)) := by
  let samples := keySwitchSamples suffixDimension keySwitchLevels
  let contexts := uniformBootstrapContext q prefixDimension suffixDimension tgswLevels
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [jointLweProblem, Adaptive.jointLweProblem, MultiQuery.jointLweProblem]
  rw [FormalProof4FHE.LWE.TwoBlock.heterogeneousUniformDistr_eq_uniformSample]
  have hShift := Encryption.Security.uniformTranscript_context_shiftFirst_evalDist
    prefixDimension samples queryCount contexts
    (fun context ↦ keySwitchMessage keySwitchGadget context.1)
    (fun context transcript ↦ transcriptGame encode adversary context.2 transcript)
  simpa [samples, contexts, jointLweReduction, zeroJointLweReduction,
    transcriptGame, bind_assoc, monad_norm] using hShift

/-- The unshifted uniform adaptive LWE branch is exactly fair for every publicly query-bounded
adversary. -/
theorem zeroJointLweReduction_game1_probOutput_true
    (queryCount : ℕ)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    Pr[= true | LearningWithErrors.game1
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
        keySwitchErrorSampler inputErrorSampler)
      (zeroJointLweReduction keySwitchErrorSampler inputErrorSampler
        encode adversary)] = 1 / 2 := by
  let samples := keySwitchSamples suffixDimension keySwitchLevels
  let FirstTranscript :=
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) prefixDimension samples
  let SecondTranscript :=
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) prefixDimension queryCount
  let firstTranscripts : ProbComp FirstTranscript := $ᵗ FirstTranscript
  let secondTranscripts : ProbComp SecondTranscript := $ᵗ SecondTranscript
  let contexts := uniformBootstrapContext q prefixDimension suffixDimension tgswLevels
  let finish := fun
      (context : BinarySecret suffixDimension ×
        Native.SharedRandomnessOneCycle.SharedBootstrappingKey q prefixDimension
          suffixDimension tgswLevels)
      (first : FirstTranscript) (bit : Bool) (second : SecondTranscript) ↦ do
    let guess ← runFromTranscript bit encode adversary
      ⟨context.2, first⟩ second
    return (bit == guess)
  rw [LearningWithErrors.game1]
  simp only [jointLweProblem, Adaptive.jointLweProblem, MultiQuery.jointLweProblem]
  rw [FormalProof4FHE.LWE.TwoBlock.heterogeneousUniformDistr_eq_uniformSample]
  calc
    _ = Pr[= true | ($ᵗ (FirstTranscript × SecondTranscript)) >>= fun transcripts ↦
        zeroJointLweReduction keySwitchErrorSampler inputErrorSampler encode adversary
          (FormalProof4FHE.LWE.TwoBlock.ofTranscriptPair transcripts)] := by
      simpa [samples, FirstTranscript, SecondTranscript] using
        (probOutput_bind_bijective_uniform_cross
          (α := FormalProof4FHE.LWE.TwoBlock.Transcript
            (ZMod q) prefixDimension samples queryCount)
          (β := FirstTranscript × SecondTranscript)
          FormalProof4FHE.LWE.TwoBlock.toTranscriptPair
          (FormalProof4FHE.LWE.TwoBlock.toTranscriptPair_bijective
            (R := ZMod q) (dimension := prefixDimension)
            (firstSamples := samples) (secondSamples := queryCount))
          (fun transcripts ↦
            zeroJointLweReduction keySwitchErrorSampler inputErrorSampler encode adversary
              (FormalProof4FHE.LWE.TwoBlock.ofTranscriptPair transcripts)) true)
    _ = Pr[= true | firstTranscripts >>= fun first ↦
        secondTranscripts >>= fun second ↦
        contexts >>= fun context ↦
        ($ᵗ Bool) >>= fun bit ↦
        finish context first bit second] := by
      have uniformProduct :
          ($ᵗ (FirstTranscript × SecondTranscript) :
            ProbComp (FirstTranscript × SecondTranscript)) =
          Prod.mk <$> firstTranscripts <*> secondTranscripts := rfl
      rw [uniformProduct]
      simp [firstTranscripts, secondTranscripts, contexts, finish,
        zeroJointLweReduction, transcriptGame, MultiQuery.keySwitchTranscript,
        MultiQuery.inputTranscript,
        FormalProof4FHE.LWE.TwoBlock.ofTranscriptPair,
        FormalProof4FHE.LWE.TwoBlock.toTranscriptPair, monad_norm]
    _ = Pr[= true | firstTranscripts >>= fun first ↦
        contexts >>= fun context ↦
        secondTranscripts >>= fun second ↦
        ($ᵗ Bool) >>= fun bit ↦
        finish context first bit second] := by
      refine probOutput_bind_congr' firstTranscripts true fun first ↦ ?_
      exact probOutput_bind_bind_swap secondTranscripts contexts
        (fun second context ↦
          ($ᵗ Bool) >>= fun bit ↦ finish context first bit second) true
    _ = Pr[= true | firstTranscripts >>= fun first ↦
        contexts >>= fun context ↦
        ($ᵗ Bool) >>= fun bit ↦
        secondTranscripts >>= fun second ↦
        finish context first bit second] := by
      refine probOutput_bind_congr' firstTranscripts true fun first ↦ ?_
      refine probOutput_bind_congr' contexts true fun context ↦ ?_
      exact probOutput_bind_bind_swap secondTranscripts ($ᵗ Bool)
        (fun second bit ↦ finish context first bit second) true
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
                (uniformAdaptive_probOutput_true queryCount encode adversary
                  (⟨context.2, first⟩ : CloudKey q prefixDimension suffixDimension
                    tgswLevels keySwitchLevels)
                  (hbound ⟨context.2, first⟩))
            _ = 1 / 2 := by
              rw [ENNReal.tsum_mul_right,
                tsum_probOutput_eq_one' (by simp [contexts]), one_mul]
        _ = 1 / 2 := by
          rw [ENNReal.tsum_mul_right,
            tsum_probOutput_eq_one' (by simp [firstTranscripts]), one_mul]

/-- The translated adaptive reduction has the same exactly fair uniform branch. -/
theorem jointLweReduction_game1_probOutput_true
    (queryCount : ℕ)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    Pr[= true | LearningWithErrors.game1
      (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
        keySwitchErrorSampler inputErrorSampler)
      (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
        encode adversary)] = 1 / 2 := by
  rw [evalDist_ext_iff.mp
    (jointLweReduction_game1_evalDist_eq_zero
      (queryCount := queryCount) keySwitchErrorSampler inputErrorSampler
      keySwitchGadget encode adversary) true]
  exact zeroJointLweReduction_game1_probOutput_true queryCount
    keySwitchErrorSampler inputErrorSampler encode adversary hbound

/-! ## Final reusable-key adaptive confidentiality bounds -/

/-- The absolute advantage of the independent uniform-BRK adaptive endpoint is exactly its
query-counted heterogeneous binary-secret LWE advantage. -/
theorem abs_signedAdvantage_independentUniformBootstrap_eq_jointLwe
    (queryCount : ℕ)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (independentUniformBootstrapGame queryCount keySwitchErrorSampler
        inputErrorSampler keySwitchGadget encode adversary)| =
      LearningWithErrors.advantage
        (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
          keySwitchErrorSampler inputErrorSampler)
        (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
          encode adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold Encryption.signedAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (independentUniformBootstrapGame_evalDist_eq_jointLwe_game0 queryCount
        keySwitchErrorSampler inputErrorSampler keySwitchGadget encode adversary) true,
    jointLweReduction_game1_probOutput_true queryCount keySwitchErrorSampler
      inputErrorSampler keySwitchGadget encode adversary hbound]
  norm_num

/-- Uniform BRK errors reduce the complete reusable-key adaptive TFHE game exactly to the
suffix-KSK-plus-query-tape LWE advantage. -/
theorem abs_signedAdvantage_real_uniformRingError_eq_jointLwe
    (queryCount : ℕ)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount
        ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
        encode adversary)| =
      LearningWithErrors.advantage
        (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
          keySwitchErrorSampler inputErrorSampler)
        (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
          encode adversary) := by
  have hGame := realGame_uniformRingError_evalDist_eq_independent queryCount
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary
  have hSigned :
      Encryption.signedAdvantage
          (realGame queryCount
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
            keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
            encode adversary) =
        Encryption.signedAdvantage
          (independentUniformBootstrapGame queryCount keySwitchErrorSampler
            inputErrorSampler keySwitchGadget encode adversary) := by
    unfold Encryption.signedAdvantage
    rw [evalDist_ext_iff.mp hGame true]
  rw [hSigned]
  exact abs_signedAdvantage_independentUniformBootstrap_eq_jointLwe queryCount
    keySwitchErrorSampler inputErrorSampler keySwitchGadget encode adversary hbound

/-- **Reusable-key adaptive shared-randomness TFHE security.** Every query-bounded adversary's
honest advantage is bounded by one complete BRK sampler-replacement cost plus one heterogeneous
binary-secret LWE advantage containing the suffix KSK and exactly `queryCount` input rows. -/
theorem abs_signedAdvantage_real_le_ringErrorDistance_add_jointLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      (TFHE.SamplerReplacement.bootstrappingErrorCount
          1 tgswLevels prefixDimension : ℝ) *
          tvDist ringErrorSampler
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) +
        LearningWithErrors.advantage
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
            keySwitchErrorSampler inputErrorSampler)
          (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
            encode adversary) := by
  let uniformRingError : ProbComp
      (RLWE.Rq q (prefixDimension + suffixDimension)) :=
    $ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))
  let actualGame := realGame queryCount ringErrorSampler keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget encode adversary
  let uniformGame := realGame queryCount uniformRingError keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget encode adversary
  let replacementBound :=
    (TFHE.SamplerReplacement.bootstrappingErrorCount
        1 tgswLevels prefixDimension : ℝ) *
      tvDist ringErrorSampler uniformRingError
  have hTV : tvDist actualGame uniformGame ≤ replacementBound := by
    simpa [actualGame, uniformGame, realGame, replacementBound] using
      (Native.SharedRandomnessOneCycle.tvDist_realSecretContinuationGame_ringError_le
        q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler uniformRingError keySwitchErrorSampler tgswGadget
        keySwitchGadget (continuation queryCount inputErrorSampler encode adversary))
  have hProbability :
      |(Pr[= true | actualGame]).toReal - (Pr[= true | uniformGame]).toReal| ≤
        tvDist actualGame uniformGame :=
    abs_probOutput_toReal_sub_le_tvDist actualGame uniformGame
  have hUniform :
      |Encryption.signedAdvantage uniformGame| =
        LearningWithErrors.advantage
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
            keySwitchErrorSampler inputErrorSampler)
          (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
            encode adversary) := by
    simpa [uniformGame, uniformRingError] using
      (abs_signedAdvantage_real_uniformRingError_eq_jointLwe queryCount
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
        encode adversary hbound)
  calc
    |Encryption.signedAdvantage
        (realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
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
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
            keySwitchErrorSampler inputErrorSampler)
          (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
            encode adversary) := by
      rw [hUniform]

/-- Equal KSK/input noises flatten the reusable-key endpoint exactly to ordinary batch LWE on
`suffixDimension * keySwitchLevels + queryCount` rows. -/
theorem abs_signedAdvantage_real_le_ringErrorDistance_add_batchLwe_of_same_noise
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      (TFHE.SamplerReplacement.bootstrappingErrorCount
          1 tgswLevels prefixDimension : ℝ) *
          tvDist ringErrorSampler
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (jointLweReduction errorSampler errorSampler keySwitchGadget
              encode adversary)) := by
  calc
    |Encryption.signedAdvantage
        (realGame queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
      (TFHE.SamplerReplacement.bootstrappingErrorCount
          1 tgswLevels prefixDimension : ℝ) *
          tvDist ringErrorSampler
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) +
        LearningWithErrors.advantage
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
            errorSampler errorSampler)
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary) :=
      abs_signedAdvantage_real_le_ringErrorDistance_add_jointLwe queryCount
        ringErrorSampler errorSampler errorSampler tgswGadget keySwitchGadget
        encode adversary hbound
    _ = (TFHE.SamplerReplacement.bootstrappingErrorCount
          1 tgswLevels prefixDimension : ℝ) *
          tvDist ringErrorSampler
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (jointLweReduction errorSampler errorSampler keySwitchGadget
              encode adversary)) := by
      congr 1
      change LearningWithErrors.advantage
          (FormalProof4FHE.LWE.TwoBlock.problem prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels) queryCount
            (Native.sampleLweSecret prefixDimension) embedBinarySecret errorSampler)
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary) = _
      simpa [Native.KeySwitchSecurity.binaryLweProblem] using
        (FormalProof4FHE.LWE.TwoBlock.advantage_eq_batch
          prefixDimension (keySwitchSamples suffixDimension keySwitchLevels) queryCount
          (Native.sampleLweSecret prefixDimension) embedBinarySecret errorSampler
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary))

/-- Public deterministic ciphertext evaluation preserves the reusable-key theorem and the same
query count.  This is the explicit FHE-evaluation closure corollary of the equal-noise bound. -/
theorem abs_signedAdvantage_publicEvaluation_le_ringErrorDistance_add_batchLwe
    {Output : Type}
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (evaluate : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      TLWE.Ciphertext (ZMod q) prefixDimension → Output)
    (adversary : Adaptive.Adversary Message
      (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) Output)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode
        (Adaptive.compilePublicEvaluation evaluate adversary))| ≤
      (TFHE.SamplerReplacement.bootstrappingErrorCount
          1 tgswLevels prefixDimension : ℝ) *
          tvDist ringErrorSampler
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (jointLweReduction errorSampler errorSampler keySwitchGadget encode
              (Adaptive.compilePublicEvaluation evaluate adversary))) := by
  letI : IsUniformSpec
      ((Message × Message) →ₒ TLWE.Ciphertext (ZMod q) prefixDimension) :=
    IsUniformSpec.ofFintypeInhabited _
  apply abs_signedAdvantage_real_le_ringErrorDistance_add_batchLwe_of_same_noise
  exact Adaptive.compilePublicEvaluation_isQueryBound evaluate adversary queryCount hbound

/-- Under exactly uniform BRK errors and equal scalar noises, reusable-key adaptive TFHE
advantage equals one conventional binary-secret batch-LWE advantage. -/
theorem abs_signedAdvantage_real_uniformRingError_eq_batchLwe_of_same_noise
    (queryCount : ℕ)
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount
        ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
        errorSampler errorSampler tgswGadget keySwitchGadget encode adversary)| =
      LearningWithErrors.advantage
        (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
          (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (jointLweReduction errorSampler errorSampler keySwitchGadget
            encode adversary)) := by
  rw [abs_signedAdvantage_real_uniformRingError_eq_jointLwe queryCount
    errorSampler errorSampler tgswGadget keySwitchGadget encode adversary hbound]
  change LearningWithErrors.advantage
      (FormalProof4FHE.LWE.TwoBlock.problem prefixDimension
        (keySwitchSamples suffixDimension keySwitchLevels) queryCount
        (Native.sampleLweSecret prefixDimension) embedBinarySecret errorSampler)
      (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary) = _
  simpa [Native.KeySwitchSecurity.binaryLweProblem] using
    (FormalProof4FHE.LWE.TwoBlock.advantage_eq_batch
      prefixDimension (keySwitchSamples suffixDimension keySwitchLevels) queryCount
      (Native.sampleLweSecret prefixDimension) embedBinarySecret errorSampler
      (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary))

/-- Adversary-class reusable-key security predicate for the shared-randomness variant. -/
def HardAgainst
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary → Adaptive.IsQueryBound adversary queryCount →
    |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤ bound

/-- Exact-uniform security theorem: ordinary batch-LWE hardness alone proves reusable-key
adaptive confidentiality of the shared-randomness TFHE variant. No circular/KDM premise remains. -/
theorem hardAgainst_uniformRingError_of_batchLwe_same_noise
    (queryCount : ℕ)
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels → Prop)
    (batchLweAllowed : LearningWithErrors.Adversary
      (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
        (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler) → Prop)
    (batchLweBound : ℝ)
    (hBatchLweClosed : ∀ adversary, allowed adversary →
      batchLweAllowed
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary)))
    (hBatchLwe : FormalProof4FHE.LWE.HardAgainst
      (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
        (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
      batchLweAllowed batchLweBound) :
    HardAgainst queryCount
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
      errorSampler errorSampler tgswGadget keySwitchGadget encode allowed batchLweBound := by
  intro adversary hadversary hbound
  rw [abs_signedAdvantage_real_uniformRingError_eq_batchLwe_of_same_noise
    queryCount errorSampler tgswGadget keySwitchGadget encode adversary hbound]
  exact hBatchLwe _ (hBatchLweClosed adversary hadversary)

/-- Near-uniform security theorem with the exact one-draw statistical loss and otherwise only
ordinary batch-LWE hardness. -/
theorem hardAgainst_of_ringError_close_uniform_and_batchLwe_same_noise
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels → Prop)
    (batchLweAllowed : LearningWithErrors.Adversary
      (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
        (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler) → Prop)
    (ringErrorDistanceBound batchLweBound : ℝ)
    (hRingError : tvDist ringErrorSampler
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) ≤ ringErrorDistanceBound)
    (hBatchLweClosed : ∀ adversary, allowed adversary →
      batchLweAllowed
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary)))
    (hBatchLwe : FormalProof4FHE.LWE.HardAgainst
      (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
        (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
      batchLweAllowed batchLweBound) :
    HardAgainst queryCount ringErrorSampler errorSampler errorSampler
      tgswGadget keySwitchGadget encode allowed
      ((TFHE.SamplerReplacement.bootstrappingErrorCount
          1 tgswLevels prefixDimension : ℝ) * ringErrorDistanceBound + batchLweBound) := by
  intro adversary hadversary hbound
  calc
    |Encryption.signedAdvantage
        (realGame queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
      (TFHE.SamplerReplacement.bootstrappingErrorCount
          1 tgswLevels prefixDimension : ℝ) *
          tvDist ringErrorSampler
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (jointLweReduction errorSampler errorSampler keySwitchGadget
              encode adversary)) :=
      abs_signedAdvantage_real_le_ringErrorDistance_add_batchLwe_of_same_noise
        queryCount ringErrorSampler errorSampler tgswGadget keySwitchGadget
        encode adversary hbound
    _ ≤ (TFHE.SamplerReplacement.bootstrappingErrorCount
          1 tgswLevels prefixDimension : ℝ) * ringErrorDistanceBound +
        batchLweBound := by
      exact add_le_add (mul_le_mul_of_nonneg_left hRingError (by positivity))
        (hBatchLwe _ (hBatchLweClosed adversary hadversary))

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle
