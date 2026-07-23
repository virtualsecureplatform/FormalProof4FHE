/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.BootstrappingSecurity

/-!
# Query-Counted Native TFHE Encryption Security

This file lifts the one-challenge native TFHE game to a fixed batch of `queryCount` left-or-right
challenges under one hidden scalar key and one circular cloud key.  The adversary sees the cloud
key, chooses two message vectors and arbitrary state, receives one TLWE batch encrypted with one
shared challenge bit, and returns a guess.

The batch formulation is deliberately native: its ciphertext carrier is `TLWE.BatchCiphertext`,
so the all-zero-cloud hybrid is exactly one two-block LWE instance containing

* every direct-TLWE key-switch row; and
* exactly `queryCount` fresh challenge rows.

Thus equal protocol noises give ordinary batch LWE with
`keySwitchSamples + queryCount` samples.  The cloud key is replaced once, so the circular/KDM
premise is a single direct-bilinear continuation advantage rather than a per-query union bound.

This is a non-adaptive multi-challenge game: both message vectors are selected before their batch
is returned.  A fully adaptive left-or-right encryption oracle remains a separate strengthening.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption.MultiQuery

/-- A query-counted native TFHE adversary. -/
structure Adversary
    (Message CloudKey BatchCiphertext : Type) (queryCount : ℕ) where
  State : Type
  chooseMessages : CloudKey →
    ProbComp ((Fin queryCount → Message) × (Fin queryCount → Message) × State)
  distinguish : State → BatchCiphertext → ProbComp Bool

section Native

variable {Message : Type}
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]

abbrev NativeAdversary (Message : Type)
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) :=
  Adversary Message
    (Encryption.NativeCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (TLWE.BatchCiphertext (ZMod q) lweDimension queryCount) queryCount

/-- Query-counted downstream experiment for already-generated secrets and cloud-key components. -/
def continuation
    (inputErrorSampler : ProbComp (ZMod q)) (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) :=
  fun lweSecret _ bootstrapKey keySwitchKey ↦ do
    let bit ← $ᵗ Bool
    let (messages₀, messages₁, state) ←
      adversary.chooseMessages ⟨bootstrapKey, keySwitchKey⟩
    let messages := fun index ↦ encode (if bit then messages₀ index else messages₁ index)
    let ciphertexts ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
      (embedBinarySecret lweSecret) messages
    let guess ← adversary.distinguish state ciphertexts
    return (bit == guess)

/-- Honest query-counted game with the native circular cloud key. -/
noncomputable def realGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ProbComp Bool :=
  Circular.realContinuationGame
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (continuation inputErrorSampler encode adversary)

/-- Query-counted hybrid with zero bootstrapping-key messages and real key-switch messages. -/
noncomputable def bootstrapZeroGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ProbComp Bool :=
  Circular.bootstrapZeroContinuationGame
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (continuation inputErrorSampler encode adversary)

/-- Contextual cost of replacing the native bootstrapping key once inside the whole batch game. -/
noncomputable def bootstrapReplacementAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ℝ :=
  (realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary).boolDistAdvantage
  (bootstrapZeroGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary)

/-- The honest batch advantage is bounded by one cloud-key replacement and the bootstrap-zero
batch advantage. -/
theorem abs_signedAdvantage_real_le_bootstrap_add_zero
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    |Encryption.signedAdvantage
      (realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary +
        |Encryption.signedAdvantage
          (bootstrapZeroGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget encode adversary)| := by
  unfold Encryption.signedAdvantage bootstrapReplacementAdvantage
    ProbComp.boolDistAdvantage
  exact abs_sub_le
    (Pr[= true | realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode adversary]).toReal
    (Pr[= true | bootstrapZeroGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode adversary]).toReal
    (1 / 2 : ℝ)

/-- Shared-secret heterogeneous LWE problem containing the KSK rows and `queryCount` challenge
rows. -/
def jointLweProblem
    (q lweDimension keySwitchSamples queryCount : ℕ) [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)) :=
  FormalProof4FHE.LWE.TwoBlock.heterogeneousProblem
    lweDimension keySwitchSamples queryCount
    (Native.sampleLweSecret lweDimension) embedBinarySecret
    keySwitchErrorSampler inputErrorSampler

/-! ### Batch transcript translations -/

/-- Read the KSK block from a query-counted two-block transcript. -/
def keySwitchTranscript {firstSamples secondSamples : ℕ}
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript
      (ZMod q) lweDimension firstSamples secondSamples) :
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension firstSamples :=
  (FormalProof4FHE.LWE.TwoBlock.toTranscriptPair transcript).1

/-- Read the challenge block from a query-counted two-block transcript. -/
def inputTranscript {firstSamples secondSamples : ℕ}
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript
      (ZMod q) lweDimension firstSamples secondSamples) :
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension secondSamples :=
  (FormalProof4FHE.LWE.TwoBlock.toTranscriptPair transcript).2

/-- Add a vector of encoded messages to a zero-message batch transcript. -/
def challengeCiphertext
    (encode : Message → ZMod q) (messages : Fin queryCount → Message)
    (transcript : FormalProof4FHE.LWE.BatchTranscript
      (ZMod q) lweDimension queryCount) :
    TLWE.BatchCiphertext (ZMod q) lweDimension queryCount :=
  (transcript.1, transcript.2 + fun index ↦ encode (messages index))

/-- Translate every body coordinate of a public batch transcript. -/
def shiftInputTranscript
    (offset : Fin queryCount → ZMod q)
    (transcript : FormalProof4FHE.LWE.BatchTranscript
      (ZMod q) lweDimension queryCount) :
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension queryCount :=
  (transcript.1, transcript.2 + offset)

/-- Inverse batch-body translation. -/
def unshiftInputTranscript
    (offset : Fin queryCount → ZMod q)
    (transcript : FormalProof4FHE.LWE.BatchTranscript
      (ZMod q) lweDimension queryCount) :
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension queryCount :=
  (transcript.1, transcript.2 - offset)

omit [NeZero q] in
@[simp]
theorem shiftInputTranscript_unshiftInputTranscript
    (offset : Fin queryCount → ZMod q)
    (transcript : FormalProof4FHE.LWE.BatchTranscript
      (ZMod q) lweDimension queryCount) :
    shiftInputTranscript offset (unshiftInputTranscript offset transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  apply Prod.ext
  · rfl
  · funext sample
    simp [shiftInputTranscript, unshiftInputTranscript]

omit [NeZero q] in
@[simp]
theorem unshiftInputTranscript_shiftInputTranscript
    (offset : Fin queryCount → ZMod q)
    (transcript : FormalProof4FHE.LWE.BatchTranscript
      (ZMod q) lweDimension queryCount) :
    unshiftInputTranscript offset (shiftInputTranscript offset transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  apply Prod.ext
  · rfl
  · funext sample
    simp [shiftInputTranscript, unshiftInputTranscript]

omit [NeZero q] in
/-- Batch-body translation is a permutation of public transcripts. -/
theorem shiftInputTranscript_bijective (offset : Fin queryCount → ZMod q) :
    Function.Bijective
      (shiftInputTranscript (lweDimension := lweDimension) offset) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨unshiftInputTranscript offset, ?_, ?_⟩
  · exact unshiftInputTranscript_shiftInputTranscript offset
  · exact shiftInputTranscript_unshiftInputTranscript offset

omit [NeZero q] in
/-- Message addition is exactly a body translation of the unshifted transcript. -/
theorem challengeCiphertext_eq_shift
    (encode : Message → ZMod q) (messages : Fin queryCount → Message)
    (transcript : FormalProof4FHE.LWE.BatchTranscript
      (ZMod q) lweDimension queryCount) :
    challengeCiphertext encode messages transcript =
      shiftInputTranscript (fun index ↦ encode (messages index)) transcript := by
  rfl

omit [NeZero q] in
/-- On a real zero-message LWE batch, message translation is native TLWE batch assembly. -/
theorem challengeCiphertext_real
    (encode : Message → ZMod q) (messages : Fin queryCount → Message)
    (secret : Fin lweDimension → ZMod q)
    (challenge : Matrix (Fin lweDimension) (Fin queryCount) (ZMod q))
    (error : Fin queryCount → ZMod q) :
    challengeCiphertext encode messages
        (challenge, vecMul secret challenge + error) =
      TLWE.batchAssemble secret challenge (fun index ↦ encode (messages index)) error := by
  apply Prod.ext
  · rfl
  · funext sample
    simp only [challengeCiphertext, TLWE.batchAssemble, Pi.add_apply]
    abel

omit [NeZero q] in
@[simp]
theorem inputTranscript_shiftFirstBlock
    {firstSamples : ℕ}
    (message : Fin firstSamples → ZMod q)
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript
      (ZMod q) lweDimension firstSamples queryCount) :
    inputTranscript (Encryption.Security.shiftFirstBlock message transcript) =
      inputTranscript transcript := by
  rfl

omit [NeZero q] in
/-- First-block translation turns a real zero-message block into the native KSK batch. -/
theorem keySwitchTranscript_shiftFirstBlock_real
    {firstSamples : ℕ}
    (message : Fin firstSamples → ZMod q)
    (secret : Fin lweDimension → ZMod q)
    (firstChallenge : Matrix (Fin lweDimension) (Fin firstSamples) (ZMod q))
    (secondChallenge : Matrix (Fin lweDimension) (Fin queryCount) (ZMod q))
    (firstError : Fin firstSamples → ZMod q)
    (secondError : Fin queryCount → ZMod q) :
    keySwitchTranscript
        (Encryption.Security.shiftFirstBlock message
          ((firstChallenge, secondChallenge),
            (vecMul secret firstChallenge + firstError,
              vecMul secret secondChallenge + secondError))) =
      TLWE.batchAssemble secret firstChallenge message firstError := by
  apply Prod.ext
  · rfl
  · funext sample
    simp only [keySwitchTranscript, Encryption.Security.shiftFirstBlock,
      FormalProof4FHE.LWE.TwoBlock.toTranscriptPair,
      TLWE.batchAssemble, Pi.add_apply]
    abel

omit [NeZero q] in
/-- The second real block becomes the native encrypted message vector. -/
theorem challengeCiphertext_inputTranscript_real
    {firstSamples : ℕ}
    (encode : Message → ZMod q) (messages : Fin queryCount → Message)
    (secret : Fin lweDimension → ZMod q)
    (firstChallenge : Matrix (Fin lweDimension) (Fin firstSamples) (ZMod q))
    (secondChallenge : Matrix (Fin lweDimension) (Fin queryCount) (ZMod q))
    (firstError : Fin firstSamples → ZMod q)
    (secondError : Fin queryCount → ZMod q) :
    challengeCiphertext encode messages
        (inputTranscript
          ((firstChallenge, secondChallenge),
            (vecMul secret firstChallenge + firstError,
              vecMul secret secondChallenge + secondError))) =
      TLWE.batchAssemble secret secondChallenge
        (fun index ↦ encode (messages index)) secondError := by
  change challengeCiphertext encode messages
      (secondChallenge, vecMul secret secondChallenge + secondError) = _
  exact challengeCiphertext_real encode messages secret secondChallenge secondError

/-! ### Joint-LWE reduction -/

/-- Run the fixed-batch challenge from an already supplied two-block public transcript. -/
def transcriptGame
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (bootstrapKey : Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript (ZMod q) lweDimension
      (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
      queryCount) : ProbComp Bool := do
  let bit ← $ᵗ Bool
  let (messages₀, messages₁, state) ← adversary.chooseMessages
    ⟨bootstrapKey, keySwitchTranscript transcript⟩
  let messages := if bit then messages₀ else messages₁
  let ciphertext := challengeCiphertext encode messages (inputTranscript transcript)
  let guess ← adversary.distinguish state ciphertext
  return (bit == guess)

/-- Joint-LWE distinguisher for an arbitrary ring-secret-dependent KSK message vector. -/
noncomputable def keySwitchMessageReduction
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : RingBinarySecret ringRank degree →
      Fin (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    LearningWithErrors.Adversary
      (jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler) :=
  fun transcript ↦ do
    let context ← Native.KeySwitchSecurity.zeroBootstrapContext
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
    transcriptGame encode adversary context.2
      (Encryption.Security.shiftFirstBlock (message context.1) transcript)

/-- Native batch game with a zero-message bootstrapping key and arbitrary KSK messages. -/
noncomputable def keySwitchMessageGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : RingBinarySecret ringRank degree →
      Fin (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ProbComp Bool := do
  let lweSecret ← Native.sampleLweSecret lweDimension
  let ringSecret ← Native.sampleRingSecret ringRank degree
  let bootstrapKey ← Native.generateZeroBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget ringSecret
  let switchKey ← TLWE.batchEncrypt lweDimension
    (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
    keySwitchErrorSampler (embedBinarySecret lweSecret) (message ringSecret)
  continuation inputErrorSampler encode adversary
    lweSecret ringSecret bootstrapKey switchKey

/-- The actual gadget-scaled extracted-ring-secret messages in the native KSK. -/
abbrev nativeKeySwitchMessage
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret ringRank degree) :
    Fin (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) → ZMod q :=
  Encryption.Security.nativeKeySwitchMessage keySwitchGadget ringSecret

/-- The bootstrap-zero endpoint is the arbitrary-message batch game at the native KSK message. -/
theorem bootstrapZeroGame_eq_keySwitchMessageGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    bootstrapZeroGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary =
      keySwitchMessageGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary := by
  simp [bootstrapZeroGame, Circular.bootstrapZeroContinuationGame,
    Native.nativeCycleSpec, keySwitchMessageGame, nativeKeySwitchMessage,
    Encryption.Security.keySwitchSamples, Encryption.Security.nativeKeySwitchMessage,
    Native.generateKeySwitchKey]

/-- The arbitrary-message native endpoint is exactly the real branch of its query-counted
two-block LWE reduction. -/
theorem keySwitchMessageGame_evalDist_eq_game0
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : RingBinarySecret ringRank degree →
      Fin (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    evalDist (keySwitchMessageGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget message encode adversary) =
      evalDist (LearningWithErrors.game0
        (jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget message encode adversary)) := by
  let samples := Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels
  let FirstChallenge := Matrix (Fin lweDimension) (Fin samples) (ZMod q)
  let SecondChallenge := Matrix (Fin lweDimension) (Fin queryCount) (ZMod q)
  let FirstError := Fin samples → ZMod q
  let SecondError := Fin queryCount → ZMod q
  let scalarSecrets := Native.sampleLweSecret lweDimension
  let contexts := Native.KeySwitchSecurity.zeroBootstrapContext
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
  let firstChallenges : ProbComp FirstChallenge := $ᵗ FirstChallenge
  let secondChallenges : ProbComp SecondChallenge := $ᵗ SecondChallenge
  let firstErrors : ProbComp FirstError :=
    ProbComp.sampleIID samples keySwitchErrorSampler
  let secondErrors : ProbComp SecondError :=
    ProbComp.sampleIID queryCount inputErrorSampler
  let inputMaterials : ProbComp (SecondChallenge × SecondError) := do
    let challenge ← secondChallenges
    let error ← secondErrors
    return (challenge, error)
  let Pre := Bool ×
    ((Fin queryCount → Message) × (Fin queryCount → Message) × adversary.State)
  let preGame := fun (lweSecret : BinarySecret lweDimension)
      (context : RingBinarySecret ringRank degree ×
        Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (challenge : FirstChallenge) (error : FirstError) ↦ do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages
      ⟨context.2, TLWE.batchAssemble (embedBinarySecret lweSecret) challenge
        (message context.1) error⟩
    return (bit, messages)
  let final := fun (lweSecret : BinarySecret lweDimension) (pre : Pre)
      (challenge : SecondChallenge) (error : SecondError) ↦ do
    let ciphertext := TLWE.batchAssemble (embedBinarySecret lweSecret) challenge
      (fun index ↦ encode (if pre.1 then pre.2.1 index else pre.2.2.1 index)) error
    let guess ← adversary.distinguish pre.2.2.2 ciphertext
    return (pre.1 == guess)
  let finish := fun (lweSecret : BinarySecret lweDimension)
      (context : RingBinarySecret ringRank degree ×
        Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (challenge : FirstChallenge) (error : FirstError)
      (inputChallenge : SecondChallenge) (inputError : SecondError) ↦
    preGame lweSecret context challenge error >>= fun pre ↦
      final lweSecret pre inputChallenge inputError
  have native_eq :
      keySwitchMessageGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget message encode adversary =
        (scalarSecrets >>= fun lweSecret ↦
          contexts >>= fun context ↦
          firstChallenges >>= fun challenge ↦
          firstErrors >>= fun error ↦
          preGame lweSecret context challenge error >>= fun pre ↦
          inputMaterials >>= fun input ↦
          final lweSecret pre input.1 input.2) := by
    simp [keySwitchMessageGame, continuation, TLWE.batchEncrypt,
      scalarSecrets, contexts, Native.KeySwitchSecurity.zeroBootstrapContext,
      samples, Encryption.Security.keySwitchSamples,
      FirstChallenge, SecondChallenge, FirstError, SecondError,
      firstChallenges, secondChallenges, firstErrors, secondErrors,
      inputMaterials, Pre, preGame, final,
      bind_assoc, monad_norm]
  have lwe_eq :
      LearningWithErrors.game0
          (jointLweProblem q lweDimension samples queryCount
            keySwitchErrorSampler inputErrorSampler)
          (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget message encode adversary) =
        (firstChallenges >>= fun challenge ↦
          secondChallenges >>= fun inputChallenge ↦
          scalarSecrets >>= fun lweSecret ↦
          firstErrors >>= fun error ↦
          secondErrors >>= fun inputError ↦
          contexts >>= fun context ↦
          finish lweSecret context challenge error inputChallenge inputError) := by
    have uniformChallengeProduct :
        ($ᵗ (FormalProof4FHE.LWE.TwoBlock.Challenge
          (ZMod q) lweDimension samples queryCount) :
          ProbComp (FormalProof4FHE.LWE.TwoBlock.Challenge
            (ZMod q) lweDimension samples queryCount)) =
        Prod.mk <$> firstChallenges <*> secondChallenges := rfl
    rw [LearningWithErrors.game0]
    simp only [jointLweProblem]
    unfold LearningWithErrors.distr
    simp only [FormalProof4FHE.LWE.TwoBlock.heterogeneousProblem]
    rw [uniformChallengeProduct]
    simp [keySwitchMessageReduction, transcriptGame,
      keySwitchTranscript_shiftFirstBlock_real,
      challengeCiphertext_inputTranscript_real,
      samples, Encryption.Security.keySwitchSamples,
      FirstChallenge, SecondChallenge, FirstError, SecondError,
      scalarSecrets, contexts, firstChallenges, secondChallenges,
      firstErrors, secondErrors, finish, preGame, final, Pre,
      ite_apply, bind_assoc, monad_norm]
  rw [native_eq, lwe_eq]
  calc
    _ = evalDist (scalarSecrets >>= fun lweSecret ↦
        contexts >>= fun context ↦
        firstChallenges >>= fun challenge ↦
        firstErrors >>= fun error ↦
        inputMaterials >>= fun input ↦
        finish lweSecret context challenge error input.1 input.2) := by
      refine evalDist_bind_congr' scalarSecrets fun lweSecret ↦ ?_
      refine evalDist_bind_congr' contexts fun context ↦ ?_
      refine evalDist_bind_congr' firstChallenges fun challenge ↦ ?_
      refine evalDist_bind_congr' firstErrors fun error ↦ ?_
      exact evalDist_bind_bind_swap
        (preGame lweSecret context challenge error) inputMaterials
        (fun pre input ↦ final lweSecret pre input.1 input.2)
    _ = evalDist (scalarSecrets >>= fun lweSecret ↦
        contexts >>= fun context ↦
        firstChallenges >>= fun challenge ↦
        firstErrors >>= fun error ↦
        secondChallenges >>= fun inputChallenge ↦
        secondErrors >>= fun inputError ↦
        finish lweSecret context challenge error inputChallenge inputError) := by
      simp [inputMaterials, bind_assoc, monad_norm]
    _ = _ :=
      Encryption.Security.evalDist_bind_six_reorder scalarSecrets contexts
        firstChallenges firstErrors secondChallenges secondErrors finish

/-! ### Uniform branch -/

/-- For a fixed cloud key, translating a uniform batch transcript by either selected encoded
message vector leaves it uniform and independent of the hidden bit. -/
theorem uniformChallenge_probOutput_true
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (cloudKey : Encryption.NativeCloudKey q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Pr[= true | do
      let bit ← $ᵗ Bool
      let (messages₀, messages₁, state) ← adversary.chooseMessages cloudKey
      let transcript ←
        $ᵗ (FormalProof4FHE.LWE.BatchTranscript
          (ZMod q) lweDimension queryCount)
      let messages := if bit then messages₀ else messages₁
      let ciphertext := challengeCiphertext encode messages transcript
      let guess ← adversary.distinguish state ciphertext
      return (bit == guess)] = 1 / 2 := by
  let Pre := Bool ×
    ((Fin queryCount → Message) × (Fin queryCount → Message) × adversary.State)
  let preGame : ProbComp Pre := do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages cloudKey
    return (bit, messages)
  let shiftedCont := fun (pre : Pre)
      (transcript : FormalProof4FHE.LWE.BatchTranscript
        (ZMod q) lweDimension queryCount) ↦ do
    let messages := if pre.1 then pre.2.1 else pre.2.2.1
    let ciphertext := challengeCiphertext encode messages transcript
    let guess ← adversary.distinguish pre.2.2.2 ciphertext
    return (pre.1 == guess)
  let unshiftedCont := fun (pre : Pre)
      (transcript : FormalProof4FHE.LWE.BatchTranscript
        (ZMod q) lweDimension queryCount) ↦ do
    let guess ← adversary.distinguish pre.2.2.2 transcript
    return (pre.1 == guess)
  calc
    _ = Pr[= true | preGame >>= fun pre ↦
          ($ᵗ (FormalProof4FHE.LWE.BatchTranscript
            (ZMod q) lweDimension queryCount)) >>= fun transcript ↦
            shiftedCont pre transcript] := by
      simp [Pre, preGame, shiftedCont, monad_norm]
    _ = Pr[= true | preGame >>= fun pre ↦
          ($ᵗ (FormalProof4FHE.LWE.BatchTranscript
            (ZMod q) lweDimension queryCount)) >>= fun transcript ↦
            unshiftedCont pre transcript] := by
      refine probOutput_bind_congr' preGame true fun pre ↦ ?_
      let messages := if pre.1 then pre.2.1 else pre.2.2.1
      let offset := fun index ↦ encode (messages index)
      simpa [shiftedCont, unshiftedCont, messages, offset,
          challengeCiphertext_eq_shift] using
        (probOutput_bind_bijective_uniform_cross
          (FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension queryCount)
          (shiftInputTranscript (lweDimension := lweDimension) offset)
          (shiftInputTranscript_bijective
            (lweDimension := lweDimension) offset)
          (fun transcript ↦ do
            let guess ← adversary.distinguish pre.2.2.2 transcript
            return (pre.1 == guess)) true)
    _ = Pr[= true | adversary.chooseMessages cloudKey >>= fun messages ↦
          ($ᵗ Bool) >>= fun bit ↦
          ($ᵗ (FormalProof4FHE.LWE.BatchTranscript
            (ZMod q) lweDimension queryCount)) >>= fun transcript ↦
            unshiftedCont (bit, messages) transcript] := by
      simpa [Pre, preGame, unshiftedCont, monad_norm] using
        (probOutput_bind_bind_swap ($ᵗ Bool) (adversary.chooseMessages cloudKey)
          (fun bit messages ↦ do
            let transcript ←
              $ᵗ (FormalProof4FHE.LWE.BatchTranscript
                (ZMod q) lweDimension queryCount)
            unshiftedCont (bit, messages) transcript) true)
    _ = 1 / 2 := by
      rw [probOutput_bind_eq_tsum]
      calc
        _ = ∑' messages, Pr[= messages | adversary.chooseMessages cloudKey] * (1 / 2) := by
          refine tsum_congr fun messages :
              (Fin queryCount → Message) ×
                (Fin queryCount → Message) × adversary.State ↦ ?_
          congr 1
          simpa [unshiftedCont, monad_norm] using
            (Encryption.Security.fairBit_eq_independentGuess
              (do
                let transcript ←
                  $ᵗ (FormalProof4FHE.LWE.BatchTranscript
                    (ZMod q) lweDimension queryCount)
                adversary.distinguish messages.2.2 transcript))
        _ = 1 / 2 := by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

/-- Unshifted query-counted reduction used to analyze the uniform branch. -/
noncomputable def zeroCloudReduction
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    LearningWithErrors.Adversary
      (jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler) :=
  fun transcript ↦ do
    let context ← Native.KeySwitchSecurity.zeroBootstrapContext
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
    transcriptGame encode adversary context.2 transcript

/-- Context-dependent KSK message translation disappears exactly in the uniform LWE branch. -/
theorem keySwitchMessageReduction_game1_evalDist_eq_zeroCloud
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : RingBinarySecret ringRank degree →
      Fin (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    evalDist (LearningWithErrors.game1
        (jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget message encode adversary)) =
      evalDist (LearningWithErrors.game1
        (jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget encode adversary)) := by
  let samples := Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels
  let contexts := Native.KeySwitchSecurity.zeroBootstrapContext
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [jointLweProblem]
  rw [FormalProof4FHE.LWE.TwoBlock.heterogeneousUniformDistr_eq_uniformSample]
  have hShift := Encryption.Security.uniformTranscript_context_shiftFirst_evalDist
    lweDimension samples queryCount contexts (fun context ↦ message context.1)
    (fun context transcript ↦ transcriptGame encode adversary context.2 transcript)
  simpa [samples, contexts, keySwitchMessageReduction,
      zeroCloudReduction, transcriptGame, bind_assoc, monad_norm] using hShift

/-- The uniform branch of the unshifted joint reduction wins with probability exactly one half. -/
theorem jointLwe_game1_probOutput_true
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    Pr[= true | LearningWithErrors.game1
      (jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler)
      (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget encode adversary)] = 1 / 2 := by
  let samples := Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels
  let FirstTranscript :=
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension samples
  let SecondTranscript :=
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension queryCount
  let firstTranscripts : ProbComp FirstTranscript := $ᵗ FirstTranscript
  let secondTranscripts : ProbComp SecondTranscript := $ᵗ SecondTranscript
  let contexts := Native.KeySwitchSecurity.zeroBootstrapContext
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
  let finish := fun
      (_context : RingBinarySecret ringRank degree ×
        Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (_first : FirstTranscript) (bit : Bool)
      (messages : (Fin queryCount → Message) ×
        (Fin queryCount → Message) × adversary.State)
      (second : SecondTranscript) ↦ do
    let selected := if bit then messages.1 else messages.2.1
    let ciphertext := challengeCiphertext encode selected second
    let guess ← adversary.distinguish messages.2.2 ciphertext
    return (bit == guess)
  rw [LearningWithErrors.game1]
  simp only [jointLweProblem]
  rw [FormalProof4FHE.LWE.TwoBlock.heterogeneousUniformDistr_eq_uniformSample]
  calc
    _ = Pr[= true | ($ᵗ (FirstTranscript × SecondTranscript)) >>= fun transcripts ↦
        zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget encode adversary
          (FormalProof4FHE.LWE.TwoBlock.ofTranscriptPair transcripts)] := by
      simpa [samples, FirstTranscript, SecondTranscript] using
        (probOutput_bind_bijective_uniform_cross
          (α := FormalProof4FHE.LWE.TwoBlock.Transcript
            (ZMod q) lweDimension samples queryCount)
          (β := FirstTranscript × SecondTranscript)
          FormalProof4FHE.LWE.TwoBlock.toTranscriptPair
          (FormalProof4FHE.LWE.TwoBlock.toTranscriptPair_bijective
            (R := ZMod q) (dimension := lweDimension)
            (firstSamples := samples) (secondSamples := queryCount))
          (fun transcripts ↦
            zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
              tgswGadget encode adversary
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
        zeroCloudReduction, transcriptGame, keySwitchTranscript, inputTranscript,
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
              refine tsum_congr fun context : RingBinarySecret ringRank degree ×
                  Native.BootstrappingKey q degree ringRank tgswLevels lweDimension ↦ ?_
              congr 1
              simpa [finish, firstTranscripts, secondTranscripts] using
                (uniformChallenge_probOutput_true encode adversary
                  (⟨context.2, first⟩ : Encryption.NativeCloudKey q degree ringRank
                    tgswLevels lweDimension keySwitchLevels))
            _ = 1 / 2 := by
              rw [ENNReal.tsum_mul_right,
                tsum_probOutput_eq_one' (by simp [contexts]), one_mul]
        _ = 1 / 2 := by
          rw [ENNReal.tsum_mul_right,
            tsum_probOutput_eq_one' (by simp [firstTranscripts]), one_mul]

/-! ### Query-counted security theorem -/

/-- The bootstrap-zero batch game is exactly the real branch of the actual-message joint-LWE
reduction. -/
theorem bootstrapZeroGame_evalDist_eq_jointLwe_game0
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    evalDist (bootstrapZeroGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary) =
      evalDist (LearningWithErrors.game0
        (jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)) := by
  rw [bootstrapZeroGame_eq_keySwitchMessageGame]
  exact keySwitchMessageGame_evalDist_eq_game0
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
    (nativeKeySwitchMessage keySwitchGadget) encode adversary

/-- The actual-message reduction's uniform branch wins with probability exactly one half. -/
theorem nativeKeySwitchReduction_game1_probOutput_true
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    Pr[= true | LearningWithErrors.game1
      (jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler)
      (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)] = 1 / 2 := by
  rw [evalDist_ext_iff.mp
      (keySwitchMessageReduction_game1_evalDist_eq_zeroCloud
        ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        (nativeKeySwitchMessage keySwitchGadget) encode adversary) true,
    jointLwe_game1_probOutput_true ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget encode adversary]

/-- The absolute signed advantage of the bootstrap-zero batch game is exactly one joint-LWE
advantage with `queryCount` rows in its second block. -/
theorem abs_signedAdvantage_bootstrapZero_eq_jointLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    |Encryption.signedAdvantage
      (bootstrapZeroGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| =
      LearningWithErrors.advantage
        (jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold Encryption.signedAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (bootstrapZeroGame_evalDist_eq_jointLwe_game0 ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary)
      true,
    nativeKeySwitchReduction_game1_probOutput_true ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary]
  norm_num

/-- **Fixed-batch native TFHE security up to circular TRGSW.** The cloud key is replaced once;
the remaining computational term is one shared-secret heterogeneous LWE instance with every KSK
row and exactly `queryCount` input rows. -/
theorem abs_signedAdvantage_real_le_bootstrap_add_jointLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    |Encryption.signedAdvantage
      (realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchErrorSampler inputErrorSampler)
          (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary) := by
  rw [← abs_signedAdvantage_bootstrapZero_eq_jointLwe ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary]
  exact abs_signedAdvantage_real_le_bootstrap_add_zero ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary

/-- Equal-noise specialization: ordinary binary-secret batch LWE uses exactly all KSK rows plus
`queryCount` challenge rows. -/
theorem abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_same_noise
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    |Encryption.signedAdvantage
      (realGame ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      bootstrapReplacementAdvantage ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
            errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
              tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)) := by
  have h := abs_signedAdvantage_real_le_bootstrap_add_jointLwe
    ringErrorSampler errorSampler errorSampler tgswGadget keySwitchGadget encode adversary
  have hBatch := FormalProof4FHE.LWE.TwoBlock.advantage_eq_batch
    lweDimension (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
    queryCount (Native.sampleLweSecret lweDimension) embedBinarySecret errorSampler
    (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
      tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)
  change |Encryption.signedAdvantage
      (realGame ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
    bootstrapReplacementAdvantage ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary +
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.TwoBlock.problem lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          (Native.sampleLweSecret lweDimension) embedBinarySecret errorSampler)
        (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
          tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary) at h
  rw [hBatch] at h
  simpa [Native.KeySwitchSecurity.binaryLweProblem] using h

/-- The batch experiment's single structured bootstrap replacement is exactly the direct
bilinear cross-key KDM advantage for its whole continuation. -/
theorem bootstrapReplacementAdvantage_eq_directBilinear
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary =
      Native.BootstrapSecurity.directBilinearAdvantage
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (continuation inputErrorSampler encode adversary) := by
  exact Native.BootstrapSecurity.continuationBootstrapReplacementAdvantage_eq_directBilinear
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
    (continuation inputErrorSampler encode adversary)

/-- Concrete fixed-batch TFHE security against a selected adversary class. -/
def HardAgainst
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    |Encryption.signedAdvantage
      (realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤ bound

/-- **Conditional fixed-batch TFHE security theorem.** Direct bilinear circular/KDM security
for the single cloud-key replacement plus the exact two-noise shared-secret LWE premise implies
security for every allowed `queryCount`-challenge adversary. -/
theorem hardAgainst_of_directBilinear_and_jointLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount → Prop)
    (bootstrapAllowed : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) → Prop)
    (jointLweAllowed : LearningWithErrors.Adversary
      (jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler) → Prop)
    (bootstrapBound jointLweBound : ℝ)
    (hBootstrapClosed : ∀ adversary, allowed adversary →
      bootstrapAllowed (continuation inputErrorSampler encode adversary))
    (hJointLweClosed : ∀ adversary, allowed adversary →
      jointLweAllowed
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary))
    (hBootstrap : Native.BootstrapSecurity.DirectBilinearHardAgainst
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      bootstrapAllowed bootstrapBound)
    (hJointLwe : FormalProof4FHE.LWE.HardAgainst
      (jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler)
      jointLweAllowed jointLweBound) :
    HardAgainst ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode allowed (bootstrapBound + jointLweBound) := by
  intro adversary hadversary
  calc
    |Encryption.signedAdvantage
        (realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
        bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget encode adversary +
          LearningWithErrors.advantage
            (jointLweProblem q lweDimension
              (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
              keySwitchErrorSampler inputErrorSampler)
            (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
              tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary) :=
      abs_signedAdvantage_real_le_bootstrap_add_jointLwe ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary
    _ ≤ bootstrapBound + jointLweBound := add_le_add
      (by
        rw [bootstrapReplacementAdvantage_eq_directBilinear ringErrorSampler
          keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary]
        exact hBootstrap _ (hBootstrapClosed adversary hadversary))
      (hJointLwe _ (hJointLweClosed adversary hadversary))

/-- Equal-noise adversary-class specialization with an ordinary binary-secret batch-LWE premise
on exactly `keySwitchSamples + queryCount` rows. -/
theorem hardAgainst_of_directBilinear_and_batchLwe_same_noise
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount → Prop)
    (bootstrapAllowed : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) → Prop)
    (batchLweAllowed : LearningWithErrors.Adversary
      (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
        errorSampler) → Prop)
    (bootstrapBound batchLweBound : ℝ)
    (hBootstrapClosed : ∀ adversary, allowed adversary →
      bootstrapAllowed (continuation errorSampler encode adversary))
    (hBatchLweClosed : ∀ adversary, allowed adversary →
      batchLweAllowed
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
            tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)))
    (hBootstrap : Native.BootstrapSecurity.DirectBilinearHardAgainst
      ringErrorSampler errorSampler tgswGadget keySwitchGadget
      bootstrapAllowed bootstrapBound)
    (hBatchLwe : FormalProof4FHE.LWE.HardAgainst
      (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
        errorSampler)
      batchLweAllowed batchLweBound) :
    HardAgainst ringErrorSampler errorSampler errorSampler
      tgswGadget keySwitchGadget encode allowed (bootstrapBound + batchLweBound) := by
  intro adversary hadversary
  calc
    |Encryption.signedAdvantage
        (realGame ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
        bootstrapReplacementAdvantage ringErrorSampler errorSampler errorSampler
            tgswGadget keySwitchGadget encode adversary +
          LearningWithErrors.advantage
            (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
              (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
              errorSampler)
            (FormalProof4FHE.LWE.TwoBlock.reduction
              (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
                tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)) :=
      abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_same_noise
        ringErrorSampler errorSampler tgswGadget keySwitchGadget encode adversary
    _ ≤ bootstrapBound + batchLweBound := add_le_add
      (by
        rw [bootstrapReplacementAdvantage_eq_directBilinear ringErrorSampler
          errorSampler errorSampler tgswGadget keySwitchGadget encode adversary]
        exact hBootstrap _ (hBootstrapClosed adversary hadversary))
      (hBatchLwe _ (hBatchLweClosed adversary hadversary))

end Native

end FormalProof4FHE.TFHE.Encryption.MultiQuery
