/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.SampleRestriction
import FormalProof4FHE.LWE.BlockBinaryReduction

/-!
# Security of Shared-Randomness Key-Switching Keys

Let `short` be the output (encryption) key of a key switch.  A conventional full-size IKSK for
an independently sampled input key `unusedPrefix || suffix` encrypts gadget encodings of every
input-key coordinate under `short`.  When the input key instead shares its prefix with the output
key, `short || suffix`, the optimized shared-randomness IKSK publishes only the suffix entries.

This file proves two complementary exact reductions.

1. An IKSK which adds any message vector sampled independently of its encryption key has exactly
   the advantage of ordinary LWE under that encryption key.  All gadget levels and digits are
   shifted as one correlated vector, so there is no per-entry hybrid loss.
2. The suffix-only shared IKSK is exactly the public suffix projection of the conventional
   full-size IKSK for an independent input key.  Consequently shared randomness introduces no new
   security assumption: every shared-IKSK distinguisher has exactly the advantage of a projected
   full-independent-IKSK distinguisher.

The message encoders receive only the independently sampled input material.  Their types cannot
access the encryption key, enforcing the absence of a circular/KDM premise.  BRKs are deliberately
not part of these games.
-/

open Matrix OracleComp

namespace FormalProof4FHE.SharedRandomness.KeySwitching

/-- An affine-message batch-LWE problem.  `messageSampler` is independent of the encryption key,
and `message` cannot inspect that key. -/
def affineIKSKProblem {R EncryptionKey MessageSecret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (messageSampler : ProbComp MessageSecret)
    (message : MessageSecret → Fin samples → R)
    (errorSampler : ProbComp R) :
    LearningWithErrors.Problem
      (Matrix (Fin dimension) (Fin samples) R)
      (EncryptionKey × MessageSecret) (Fin samples → R) where
  sampleChallenge := $ᵗ Matrix (Fin dimension) (Fin samples) R
  sampleSecret := do
    let encryptionKey ← encryptionKeySampler
    let messageSecret ← messageSampler
    return (encryptionKey, messageSecret)
  sampleError := ProbComp.sampleIID samples errorSampler
  noiseless := fun secret challenge ↦
    vecMul (embedEncryptionKey secret.1) challenge + message secret.2
  sampleUniform := $ᵗ (Fin samples → R)

/-- Add the complete correlated IKSK message vector to an LWE transcript. -/
def addMessageToTranscript {R MessageSecret : Type} [Add R]
    {dimension samples : ℕ} (message : MessageSecret → Fin samples → R)
    (messageSecret : MessageSecret)
    (transcript : FormalProof4FHE.LWE.BatchTranscript R dimension samples) :
    FormalProof4FHE.LWE.BatchTranscript R dimension samples :=
  (transcript.1, transcript.2 + message messageSecret)

/-- Convert an IKSK distinguisher into a distinguisher for LWE under the IKSK encryption key. -/
def affineIKSKReduction {R EncryptionKey MessageSecret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    {dimension samples : ℕ}
    {encryptionKeySampler : ProbComp EncryptionKey}
    {embedEncryptionKey : EncryptionKey → Fin dimension → R}
    (messageSampler : ProbComp MessageSecret)
    (message : MessageSecret → Fin samples → R)
    {errorSampler : ProbComp R}
    (adversary : LearningWithErrors.Adversary
      (affineIKSKProblem dimension samples encryptionKeySampler embedEncryptionKey
        messageSampler message errorSampler)) :
    LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.embeddedBatchProblem dimension samples
        encryptionKeySampler embedEncryptionKey errorSampler) :=
  fun transcript ↦ do
    let messageSecret ← messageSampler
    adversary (addMessageToTranscript message messageSecret transcript)

/-- The affine-message real branch is exactly the LWE real branch followed by message shifting. -/
theorem affineIKSK_real_evalDist {R EncryptionKey MessageSecret : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (messageSampler : ProbComp MessageSecret)
    (message : MessageSecret → Fin samples → R)
    (errorSampler : ProbComp R) :
    𝒟[LearningWithErrors.distr
          (FormalProof4FHE.LWE.embeddedBatchProblem dimension samples
            encryptionKeySampler embedEncryptionKey errorSampler) >>=
        fun transcript ↦
          messageSampler >>= fun messageSecret ↦
          pure (addMessageToTranscript message messageSecret transcript)] =
      𝒟[LearningWithErrors.distr
        (affineIKSKProblem dimension samples encryptionKeySampler embedEncryptionKey
          messageSampler message errorSampler)] := by
  let challenges : ProbComp (Matrix (Fin dimension) (Fin samples) R) :=
    $ᵗ Matrix (Fin dimension) (Fin samples) R
  let errors : ProbComp (Fin samples → R) :=
    ProbComp.sampleIID samples errorSampler
  let finish : Matrix (Fin dimension) (Fin samples) R → EncryptionKey →
      MessageSecret → (Fin samples → R) →
      ProbComp (FormalProof4FHE.LWE.BatchTranscript R dimension samples) :=
    fun challenge encryptionKey messageSecret error ↦
      pure (challenge,
        vecMul (embedEncryptionKey encryptionKey) challenge + message messageSecret + error)
  have left_eq :
      (LearningWithErrors.distr
          (FormalProof4FHE.LWE.embeddedBatchProblem dimension samples
            encryptionKeySampler embedEncryptionKey errorSampler) >>=
        fun transcript ↦
          messageSampler >>= fun messageSecret ↦
          pure (addMessageToTranscript message messageSecret transcript)) =
      (challenges >>= fun challenge ↦
        encryptionKeySampler >>= fun encryptionKey ↦
        errors >>= fun error ↦
        messageSampler >>= fun messageSecret ↦
        finish challenge encryptionKey messageSecret error) := by
    simp [LearningWithErrors.distr, FormalProof4FHE.LWE.embeddedBatchProblem,
      addMessageToTranscript, challenges, errors, finish, add_comm,
      add_left_comm, bind_assoc, monad_norm]
  have right_eq :
      LearningWithErrors.distr
          (affineIKSKProblem dimension samples encryptionKeySampler embedEncryptionKey
            messageSampler message errorSampler) =
      (challenges >>= fun challenge ↦
        encryptionKeySampler >>= fun encryptionKey ↦
        messageSampler >>= fun messageSecret ↦
        errors >>= fun error ↦
        finish challenge encryptionKey messageSecret error) := by
    simp [LearningWithErrors.distr, affineIKSKProblem, challenges, errors, finish,
      add_assoc, bind_assoc, monad_norm]
  rw [left_eq, right_eq]
  refine evalDist_bind_congr' challenges fun challenge ↦ ?_
  refine evalDist_bind_congr' encryptionKeySampler fun encryptionKey ↦ ?_
  exact probOutput_bind_bind_swap errors messageSampler
    (fun error messageSecret ↦ finish challenge encryptionKey messageSecret error)
    |> evalDist_ext

/-- The affine-message uniform branch is unchanged: translating a uniform output vector by the
complete message vector is a permutation. -/
theorem affineIKSK_uniform_evalDist {R EncryptionKey MessageSecret : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (messageSampler : ProbComp MessageSecret)
    (message : MessageSecret → Fin samples → R)
    (errorSampler : ProbComp R)
    (hMessage : Pr[⊥ | messageSampler] = 0) :
    𝒟[LearningWithErrors.uniformDistr
          (FormalProof4FHE.LWE.embeddedBatchProblem dimension samples
            encryptionKeySampler embedEncryptionKey errorSampler) >>=
        fun transcript ↦
          messageSampler >>= fun messageSecret ↦
          pure (addMessageToTranscript message messageSecret transcript)] =
      𝒟[LearningWithErrors.uniformDistr
        (affineIKSKProblem dimension samples encryptionKeySampler embedEncryptionKey
          messageSampler message errorSampler)] := by
  let challenges : ProbComp (Matrix (Fin dimension) (Fin samples) R) :=
    $ᵗ Matrix (Fin dimension) (Fin samples) R
  let uniformOutputs : ProbComp (Fin samples → R) :=
    $ᵗ (Fin samples → R)
  have hfixed : ∀ (challenge : Matrix (Fin dimension) (Fin samples) R)
      (messageSecret : MessageSecret),
      𝒟[uniformOutputs >>= fun output ↦
          pure (challenge, output + message messageSecret)] =
        𝒟[uniformOutputs >>= fun output ↦ pure (challenge, output)] := by
    intro challenge messageSecret
    simpa only [uniformOutputs, id_eq] using
      (evalDist_bind_bijective_add_right_uniform
        (α := Fin samples → R) (β := Fin samples → R)
        id Function.bijective_id (message messageSecret)
        (fun output ↦ pure (challenge, output)))
  have left_eq :
      (LearningWithErrors.uniformDistr
          (FormalProof4FHE.LWE.embeddedBatchProblem dimension samples
            encryptionKeySampler embedEncryptionKey errorSampler) >>=
        fun transcript ↦
          messageSampler >>= fun messageSecret ↦
          pure (addMessageToTranscript message messageSecret transcript)) =
      (challenges >>= fun challenge ↦
        uniformOutputs >>= fun output ↦
        messageSampler >>= fun messageSecret ↦
        pure (challenge, output + message messageSecret)) := by
    simp [LearningWithErrors.uniformDistr, FormalProof4FHE.LWE.embeddedBatchProblem,
      addMessageToTranscript, challenges, uniformOutputs, bind_assoc, monad_norm]
  have right_eq :
      LearningWithErrors.uniformDistr
          (affineIKSKProblem dimension samples encryptionKeySampler embedEncryptionKey
            messageSampler message errorSampler) =
      (challenges >>= fun challenge ↦
        uniformOutputs >>= fun output ↦ pure (challenge, output)) := by
    simp [LearningWithErrors.uniformDistr, affineIKSKProblem, challenges, uniformOutputs,
      monad_norm]
  rw [left_eq, right_eq]
  refine evalDist_bind_congr' challenges fun challenge ↦ ?_
  calc
    _ = 𝒟[messageSampler >>= fun messageSecret ↦
        uniformOutputs >>= fun output ↦
        pure (challenge, output + message messageSecret)] :=
      probOutput_bind_bind_swap uniformOutputs messageSampler
        (fun output messageSecret ↦
          pure (challenge, output + message messageSecret))
        |> evalDist_ext
    _ = 𝒟[messageSampler >>= fun _ ↦
        uniformOutputs >>= fun output ↦ pure (challenge, output)] := by
      refine evalDist_bind_congr' messageSampler fun messageSecret ↦ ?_
      exact hfixed challenge messageSecret
    _ = 𝒟[uniformOutputs >>= fun output ↦ pure (challenge, output)] :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        messageSampler hMessage _

/-- Real-game equality for the exact affine IKSK reduction. -/
theorem affineIKSK_game0_evalDist_eq {R EncryptionKey MessageSecret : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (messageSampler : ProbComp MessageSecret)
    (message : MessageSecret → Fin samples → R)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (affineIKSKProblem dimension samples encryptionKeySampler embedEncryptionKey
        messageSampler message errorSampler)) :
    𝒟[LearningWithErrors.game0
        (affineIKSKProblem dimension samples encryptionKeySampler embedEncryptionKey
          messageSampler message errorSampler) adversary] =
      𝒟[LearningWithErrors.game0
        (FormalProof4FHE.LWE.embeddedBatchProblem dimension samples
          encryptionKeySampler embedEncryptionKey errorSampler)
        (affineIKSKReduction messageSampler message adversary)] := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  simp only [affineIKSKReduction]
  rw [show (LearningWithErrors.distr
        (FormalProof4FHE.LWE.embeddedBatchProblem dimension samples
          encryptionKeySampler embedEncryptionKey errorSampler) >>=
      fun transcript ↦
        messageSampler >>= fun messageSecret ↦
        adversary (addMessageToTranscript message messageSecret transcript)) =
      ((LearningWithErrors.distr
          (FormalProof4FHE.LWE.embeddedBatchProblem dimension samples
            encryptionKeySampler embedEncryptionKey errorSampler) >>=
        fun transcript ↦
          messageSampler >>= fun messageSecret ↦
          pure (addMessageToTranscript message messageSecret transcript)) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    affineIKSK_real_evalDist dimension samples encryptionKeySampler embedEncryptionKey
      messageSampler message errorSampler]

/-- Uniform-game equality for the exact affine IKSK reduction. -/
theorem affineIKSK_game1_evalDist_eq {R EncryptionKey MessageSecret : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (messageSampler : ProbComp MessageSecret)
    (message : MessageSecret → Fin samples → R)
    (errorSampler : ProbComp R)
    (hMessage : Pr[⊥ | messageSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (affineIKSKProblem dimension samples encryptionKeySampler embedEncryptionKey
        messageSampler message errorSampler)) :
    𝒟[LearningWithErrors.game1
        (affineIKSKProblem dimension samples encryptionKeySampler embedEncryptionKey
          messageSampler message errorSampler) adversary] =
      𝒟[LearningWithErrors.game1
        (FormalProof4FHE.LWE.embeddedBatchProblem dimension samples
          encryptionKeySampler embedEncryptionKey errorSampler)
        (affineIKSKReduction messageSampler message adversary)] := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [affineIKSKReduction]
  rw [show (LearningWithErrors.uniformDistr
        (FormalProof4FHE.LWE.embeddedBatchProblem dimension samples
          encryptionKeySampler embedEncryptionKey errorSampler) >>=
      fun transcript ↦
        messageSampler >>= fun messageSecret ↦
        adversary (addMessageToTranscript message messageSecret transcript)) =
      ((LearningWithErrors.uniformDistr
          (FormalProof4FHE.LWE.embeddedBatchProblem dimension samples
            encryptionKeySampler embedEncryptionKey errorSampler) >>=
        fun transcript ↦
          messageSampler >>= fun messageSecret ↦
          pure (addMessageToTranscript message messageSecret transcript)) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    affineIKSK_uniform_evalDist dimension samples encryptionKeySampler embedEncryptionKey
      messageSampler message errorSampler hMessage]

/-- Exact whole-batch reduction of independently encoded IKSK messages to LWE under the
encryption key. -/
theorem affineIKSK_advantage_eq_lwe {R EncryptionKey MessageSecret : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (messageSampler : ProbComp MessageSecret)
    (message : MessageSecret → Fin samples → R)
    (errorSampler : ProbComp R)
    (hMessage : Pr[⊥ | messageSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (affineIKSKProblem dimension samples encryptionKeySampler embedEncryptionKey
        messageSampler message errorSampler)) :
    LearningWithErrors.advantage
        (affineIKSKProblem dimension samples encryptionKeySampler embedEncryptionKey
          messageSampler message errorSampler) adversary =
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.embeddedBatchProblem dimension samples
          encryptionKeySampler embedEncryptionKey errorSampler)
        (affineIKSKReduction messageSampler message adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (affineIKSK_game0_evalDist_eq dimension samples encryptionKeySampler
        embedEncryptionKey messageSampler message errorSampler adversary) true,
    evalDist_ext_iff.mp
      (affineIKSK_game1_evalDist_eq dimension samples encryptionKeySampler
        embedEncryptionKey messageSampler message errorSampler hMessage adversary) true]

section FullIndependentComparison

/-- Independently sample the two blocks of a conventional full-size input key. -/
def independentInputSampler {PrefixSecret SuffixSecret : Type}
    (prefixSampler : ProbComp PrefixSecret) (suffixSampler : ProbComp SuffixSecret) :
    ProbComp (PrefixSecret × SuffixSecret) := do
  let firstInput ← prefixSampler
  let secondInput ← suffixSampler
  return (firstInput, secondInput)

/-- Concatenate the gadget-message blocks for the independent input-key prefix and suffix. -/
def fullIndependentMessage {R PrefixSecret SuffixSecret : Type}
    {discarded retained : ℕ}
    (prefixMessage : PrefixSecret → Fin discarded → R)
    (suffixMessage : SuffixSecret → Fin retained → R)
    (input : PrefixSecret × SuffixSecret) : Fin (discarded + retained) → R :=
  FormalProof4FHE.LWE.appendBatchOutput
    (prefixMessage input.1, suffixMessage input.2)

/-- The conventional full-size IKSK between two independent keys.  The independently sampled
input prefix contributes `discarded` entries, and its suffix contributes `retained` entries. -/
def fullIndependentIKSKProblem
    {R EncryptionKey PrefixSecret SuffixSecret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension discarded retained : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (prefixSampler : ProbComp PrefixSecret)
    (suffixSampler : ProbComp SuffixSecret)
    (prefixMessage : PrefixSecret → Fin discarded → R)
    (suffixMessage : SuffixSecret → Fin retained → R)
    (errorSampler : ProbComp R) :=
  affineIKSKProblem dimension (discarded + retained)
    encryptionKeySampler embedEncryptionKey
    (independentInputSampler prefixSampler suffixSampler)
    (fullIndependentMessage prefixMessage suffixMessage) errorSampler

/-- The optimized shared-randomness IKSK.  The conceptual input key is
`encryptionKey || suffix`, but only gadget encodings of the independent suffix are published. -/
def sharedIKSKProblem
    {R EncryptionKey SuffixSecret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension retained : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (suffixSampler : ProbComp SuffixSecret)
    (suffixMessage : SuffixSecret → Fin retained → R)
    (errorSampler : ProbComp R) :=
  affineIKSKProblem dimension retained encryptionKeySampler embedEncryptionKey
    suffixSampler suffixMessage errorSampler

/-- A full-size IKSK transcript projects to the entries encrypting the input-key suffix. -/
def fullIKSKSuffixProjection {R : Type} {dimension discarded retained : ℕ}
    (transcript : FormalProof4FHE.LWE.BatchTranscript R dimension (discarded + retained)) :
    FormalProof4FHE.LWE.BatchTranscript R dimension retained :=
  FormalProof4FHE.LWE.retainBatchSuffix transcript

/-- Convert a shared-IKSK distinguisher into a full-independent-IKSK distinguisher by discarding
the entries for the independent input prefix. -/
def fullIndependentProjectionReduction
    {R EncryptionKey PrefixSecret SuffixSecret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    {dimension discarded retained : ℕ}
    {encryptionKeySampler : ProbComp EncryptionKey}
    {embedEncryptionKey : EncryptionKey → Fin dimension → R}
    {prefixSampler : ProbComp PrefixSecret}
    {suffixSampler : ProbComp SuffixSecret}
    {prefixMessage : PrefixSecret → Fin discarded → R}
    {suffixMessage : SuffixSecret → Fin retained → R}
    {errorSampler : ProbComp R}
    (adversary : LearningWithErrors.Adversary
      (sharedIKSKProblem dimension retained encryptionKeySampler embedEncryptionKey
        suffixSampler suffixMessage errorSampler)) :
    LearningWithErrors.Adversary
      (fullIndependentIKSKProblem dimension discarded retained
        encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
        prefixMessage suffixMessage errorSampler) :=
  fun transcript ↦ adversary (fullIKSKSuffixProjection transcript)

/-- Pointwise algebraic identity behind the projection theorem: after discarding the full IKSK's
prefix entries, its suffix is exactly an IKSK for the independently sampled suffix. -/
theorem fullIKSKSuffixProjection_real {R : Type} [Ring R]
    {dimension discarded retained : ℕ}
    (encryptionKey : Fin dimension → R)
    (prefixMessage : Fin discarded → R) (suffixMessage : Fin retained → R)
    (challenge : Matrix (Fin dimension) (Fin (discarded + retained)) R)
    (error : Fin (discarded + retained) → R) :
    fullIKSKSuffixProjection
        (challenge,
          (vecMul encryptionKey challenge +
            FormalProof4FHE.LWE.appendBatchOutput (prefixMessage, suffixMessage)) + error) =
      ((FormalProof4FHE.LWE.splitBatchColumns challenge).2,
        (vecMul encryptionKey (FormalProof4FHE.LWE.splitBatchColumns challenge).2 +
          suffixMessage) + (FormalProof4FHE.LWE.splitBatchOutput error).2) := by
  simpa [fullIKSKSuffixProjection, FormalProof4FHE.LWE.splitBatchOutput_add,
    FormalProof4FHE.LWE.splitBatchOutput_appendBatchOutput, add_assoc] using
    (FormalProof4FHE.LWE.retainBatchSuffix_real encryptionKey challenge
      (FormalProof4FHE.LWE.appendBatchOutput (prefixMessage, suffixMessage) + error))

/-- The real shared IKSK is exactly the suffix projection of the conventional full-size IKSK for
an independent input key. -/
theorem sharedIKSK_real_evalDist_eq_project_fullIndependent
    {R EncryptionKey PrefixSecret SuffixSecret : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension discarded retained : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (prefixSampler : ProbComp PrefixSecret)
    (suffixSampler : ProbComp SuffixSecret)
    (prefixMessage : PrefixSecret → Fin discarded → R)
    (suffixMessage : SuffixSecret → Fin retained → R)
    (errorSampler : ProbComp R)
    (hPrefix : Pr[⊥ | prefixSampler] = 0)
    (hError : Pr[⊥ | errorSampler] = 0) :
    𝒟[LearningWithErrors.distr
          (fullIndependentIKSKProblem dimension discarded retained
            encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
            prefixMessage suffixMessage errorSampler) >>=
        fun transcript ↦ pure (fullIKSKSuffixProjection transcript)] =
      𝒟[LearningWithErrors.distr
        (sharedIKSKProblem dimension retained encryptionKeySampler embedEncryptionKey
          suffixSampler suffixMessage errorSampler)] := by
  let fullChallenge : ProbComp
      (Matrix (Fin dimension) (Fin (discarded + retained)) R) :=
    $ᵗ Matrix (Fin dimension) (Fin (discarded + retained)) R
  let retainedChallenge : ProbComp (Matrix (Fin dimension) (Fin retained) R) :=
    (fun matrix ↦ (FormalProof4FHE.LWE.splitBatchColumns matrix).2) <$> fullChallenge
  let targetChallenge : ProbComp (Matrix (Fin dimension) (Fin retained) R) :=
    $ᵗ Matrix (Fin dimension) (Fin retained) R
  let fullError : ProbComp (Fin (discarded + retained) → R) :=
    ProbComp.sampleIID (discarded + retained) errorSampler
  let retainedError : ProbComp (Fin retained → R) :=
    (fun error ↦ (FormalProof4FHE.LWE.splitBatchOutput error).2) <$> fullError
  let targetError : ProbComp (Fin retained → R) :=
    ProbComp.sampleIID retained errorSampler
  let finish : Matrix (Fin dimension) (Fin retained) R → EncryptionKey →
      SuffixSecret → (Fin retained → R) →
      ProbComp (FormalProof4FHE.LWE.BatchTranscript R dimension retained) :=
    fun challenge encryptionKey suffix error ↦
      pure (challenge,
        (vecMul (embedEncryptionKey encryptionKey) challenge + suffixMessage suffix) + error)
  have hChallenge : 𝒟[retainedChallenge] = 𝒟[targetChallenge] := by
    simpa only [retainedChallenge, fullChallenge, targetChallenge] using
      (FormalProof4FHE.LWE.retainBatchSuffix_uniformMatrix_evalDist
        (R := R) dimension discarded retained)
  have hErrors : 𝒟[retainedError] = 𝒟[targetError] := by
    simpa only [retainedError, fullError, targetError] using
      (FormalProof4FHE.LWE.retainBatchSuffix_sampleIID_evalDist
        discarded retained errorSampler hError)
  have left_eq :
      (LearningWithErrors.distr
          (fullIndependentIKSKProblem dimension discarded retained
            encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
            prefixMessage suffixMessage errorSampler) >>=
        fun transcript ↦ pure (fullIKSKSuffixProjection transcript)) =
      (retainedChallenge >>= fun challenge ↦
        encryptionKeySampler >>= fun encryptionKey ↦
        prefixSampler >>= fun _ ↦
        suffixSampler >>= fun suffix ↦
        retainedError >>= fun error ↦
        finish challenge encryptionKey suffix error) := by
    simp [LearningWithErrors.distr, fullIndependentIKSKProblem, affineIKSKProblem,
      independentInputSampler, fullIndependentMessage, fullIKSKSuffixProjection_real,
      retainedChallenge, fullChallenge, retainedError, fullError, finish,
      bind_assoc, monad_norm]
  have right_eq :
      LearningWithErrors.distr
          (sharedIKSKProblem dimension retained encryptionKeySampler embedEncryptionKey
            suffixSampler suffixMessage errorSampler) =
      (targetChallenge >>= fun challenge ↦
        encryptionKeySampler >>= fun encryptionKey ↦
        suffixSampler >>= fun suffix ↦
        targetError >>= fun error ↦
        finish challenge encryptionKey suffix error) := by
    simp [LearningWithErrors.distr, sharedIKSKProblem, affineIKSKProblem,
      targetChallenge, targetError, finish, bind_assoc, monad_norm]
  rw [left_eq, right_eq]
  calc
    _ = 𝒟[retainedChallenge >>= fun challenge ↦
        encryptionKeySampler >>= fun encryptionKey ↦
        suffixSampler >>= fun suffix ↦
        retainedError >>= fun error ↦
        finish challenge encryptionKey suffix error] := by
      refine evalDist_bind_congr' retainedChallenge fun challenge ↦ ?_
      refine evalDist_bind_congr' encryptionKeySampler fun encryptionKey ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        prefixSampler hPrefix _
    _ = 𝒟[targetChallenge >>= fun challenge ↦
        encryptionKeySampler >>= fun encryptionKey ↦
        suffixSampler >>= fun suffix ↦
        retainedError >>= fun error ↦
        finish challenge encryptionKey suffix error] :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hChallenge _
    _ = _ := by
      refine evalDist_bind_congr' targetChallenge fun challenge ↦ ?_
      refine evalDist_bind_congr' encryptionKeySampler fun encryptionKey ↦ ?_
      refine evalDist_bind_congr' suffixSampler fun suffix ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hErrors _

/-- The uniform shared IKSK is exactly the suffix projection of a uniform full-size IKSK. -/
theorem sharedIKSK_uniform_evalDist_eq_project_fullIndependent
    {R EncryptionKey PrefixSecret SuffixSecret : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension discarded retained : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (prefixSampler : ProbComp PrefixSecret)
    (suffixSampler : ProbComp SuffixSecret)
    (prefixMessage : PrefixSecret → Fin discarded → R)
    (suffixMessage : SuffixSecret → Fin retained → R)
    (errorSampler : ProbComp R) :
    𝒟[LearningWithErrors.uniformDistr
          (fullIndependentIKSKProblem dimension discarded retained
            encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
            prefixMessage suffixMessage errorSampler) >>=
        fun transcript ↦ pure (fullIKSKSuffixProjection transcript)] =
      𝒟[LearningWithErrors.uniformDistr
        (sharedIKSKProblem dimension retained encryptionKeySampler embedEncryptionKey
          suffixSampler suffixMessage errorSampler)] := by
  simpa only [LearningWithErrors.uniformDistr, fullIndependentIKSKProblem,
    sharedIKSKProblem, affineIKSKProblem, FormalProof4FHE.LWE.embeddedBatchProblem,
    fullIKSKSuffixProjection] using
    (FormalProof4FHE.LWE.retainBatchSuffix_uniform_evalDist
      (R := R) (Secret := EncryptionKey × (PrefixSecret × SuffixSecret))
      dimension discarded retained
      (independentInputSampler encryptionKeySampler
        (independentInputSampler prefixSampler suffixSampler))
      (fun secret ↦ embedEncryptionKey secret.1) errorSampler)

/-- Real-game equality for the lossless projection from shared to full-independent IKSK. -/
theorem sharedIKSK_game0_evalDist_eq_fullIndependent
    {R EncryptionKey PrefixSecret SuffixSecret : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension discarded retained : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (prefixSampler : ProbComp PrefixSecret)
    (suffixSampler : ProbComp SuffixSecret)
    (prefixMessage : PrefixSecret → Fin discarded → R)
    (suffixMessage : SuffixSecret → Fin retained → R)
    (errorSampler : ProbComp R)
    (hPrefix : Pr[⊥ | prefixSampler] = 0)
    (hError : Pr[⊥ | errorSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (sharedIKSKProblem dimension retained encryptionKeySampler embedEncryptionKey
        suffixSampler suffixMessage errorSampler)) :
    𝒟[LearningWithErrors.game0
        (sharedIKSKProblem dimension retained encryptionKeySampler embedEncryptionKey
          suffixSampler suffixMessage errorSampler) adversary] =
      𝒟[LearningWithErrors.game0
        (fullIndependentIKSKProblem dimension discarded retained
          encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
          prefixMessage suffixMessage errorSampler)
        (fullIndependentProjectionReduction adversary)] := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  simp only [fullIndependentProjectionReduction]
  rw [show (LearningWithErrors.distr
        (fullIndependentIKSKProblem dimension discarded retained
          encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
          prefixMessage suffixMessage errorSampler) >>=
      fun transcript ↦ adversary (fullIKSKSuffixProjection transcript)) =
      ((LearningWithErrors.distr
          (fullIndependentIKSKProblem dimension discarded retained
            encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
            prefixMessage suffixMessage errorSampler) >>=
        fun transcript ↦ pure (fullIKSKSuffixProjection transcript)) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    sharedIKSK_real_evalDist_eq_project_fullIndependent dimension discarded retained
      encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
      prefixMessage suffixMessage errorSampler hPrefix hError]

/-- Uniform-game equality for the lossless projection from shared to full-independent IKSK. -/
theorem sharedIKSK_game1_evalDist_eq_fullIndependent
    {R EncryptionKey PrefixSecret SuffixSecret : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension discarded retained : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (prefixSampler : ProbComp PrefixSecret)
    (suffixSampler : ProbComp SuffixSecret)
    (prefixMessage : PrefixSecret → Fin discarded → R)
    (suffixMessage : SuffixSecret → Fin retained → R)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (sharedIKSKProblem dimension retained encryptionKeySampler embedEncryptionKey
        suffixSampler suffixMessage errorSampler)) :
    𝒟[LearningWithErrors.game1
        (sharedIKSKProblem dimension retained encryptionKeySampler embedEncryptionKey
          suffixSampler suffixMessage errorSampler) adversary] =
      𝒟[LearningWithErrors.game1
        (fullIndependentIKSKProblem dimension discarded retained
          encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
          prefixMessage suffixMessage errorSampler)
        (fullIndependentProjectionReduction adversary)] := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [fullIndependentProjectionReduction]
  rw [show (LearningWithErrors.uniformDistr
        (fullIndependentIKSKProblem dimension discarded retained
          encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
          prefixMessage suffixMessage errorSampler) >>=
      fun transcript ↦ adversary (fullIKSKSuffixProjection transcript)) =
      ((LearningWithErrors.uniformDistr
          (fullIndependentIKSKProblem dimension discarded retained
            encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
            prefixMessage suffixMessage errorSampler) >>=
        fun transcript ↦ pure (fullIKSKSuffixProjection transcript)) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    sharedIKSK_uniform_evalDist_eq_project_fullIndependent dimension discarded retained
      encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
      prefixMessage suffixMessage errorSampler]

/-- **No-new-assumption theorem.**  Every shared-randomness IKSK distinguisher has exactly the
advantage of its suffix-projection reduction against the conventional full-size IKSK for two
independent keys. -/
theorem sharedIKSK_advantage_eq_fullIndependent
    {R EncryptionKey PrefixSecret SuffixSecret : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension discarded retained : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (prefixSampler : ProbComp PrefixSecret)
    (suffixSampler : ProbComp SuffixSecret)
    (prefixMessage : PrefixSecret → Fin discarded → R)
    (suffixMessage : SuffixSecret → Fin retained → R)
    (errorSampler : ProbComp R)
    (hPrefix : Pr[⊥ | prefixSampler] = 0)
    (hError : Pr[⊥ | errorSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (sharedIKSKProblem dimension retained encryptionKeySampler embedEncryptionKey
        suffixSampler suffixMessage errorSampler)) :
    LearningWithErrors.advantage
        (sharedIKSKProblem dimension retained encryptionKeySampler embedEncryptionKey
          suffixSampler suffixMessage errorSampler) adversary =
      LearningWithErrors.advantage
        (fullIndependentIKSKProblem dimension discarded retained
          encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
          prefixMessage suffixMessage errorSampler)
        (fullIndependentProjectionReduction adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (sharedIKSK_game0_evalDist_eq_fullIndependent dimension discarded retained
        encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
        prefixMessage suffixMessage errorSampler hPrefix hError adversary) true,
    evalDist_ext_iff.mp
      (sharedIKSK_game1_evalDist_eq_fullIndependent dimension discarded retained
        encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
        prefixMessage suffixMessage errorSampler adversary) true]

/-- Hardness of the conventional full-size IKSK transfers without any loss to the shared IKSK.
The only side condition on adversary classes is the standard closure condition that the explicit
suffix-projection reduction is admitted by `fullAllowed`. -/
theorem sharedIKSK_hardAgainst_of_fullIndependent
    {R EncryptionKey PrefixSecret SuffixSecret : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension discarded retained : ℕ)
    (encryptionKeySampler : ProbComp EncryptionKey)
    (embedEncryptionKey : EncryptionKey → Fin dimension → R)
    (prefixSampler : ProbComp PrefixSecret)
    (suffixSampler : ProbComp SuffixSecret)
    (prefixMessage : PrefixSecret → Fin discarded → R)
    (suffixMessage : SuffixSecret → Fin retained → R)
    (errorSampler : ProbComp R)
    (hPrefix : Pr[⊥ | prefixSampler] = 0)
    (hError : Pr[⊥ | errorSampler] = 0)
    (sharedAllowed : LearningWithErrors.Adversary
      (sharedIKSKProblem dimension retained encryptionKeySampler embedEncryptionKey
        suffixSampler suffixMessage errorSampler) → Prop)
    (fullAllowed : LearningWithErrors.Adversary
      (fullIndependentIKSKProblem dimension discarded retained
        encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
        prefixMessage suffixMessage errorSampler) → Prop)
    (bound : ℝ)
    (hReductionClosed : ∀ adversary, sharedAllowed adversary →
      fullAllowed (fullIndependentProjectionReduction adversary))
    (hFull : FormalProof4FHE.LWE.HardAgainst
      (fullIndependentIKSKProblem dimension discarded retained
        encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
        prefixMessage suffixMessage errorSampler) fullAllowed bound) :
    FormalProof4FHE.LWE.HardAgainst
      (sharedIKSKProblem dimension retained encryptionKeySampler embedEncryptionKey
        suffixSampler suffixMessage errorSampler) sharedAllowed bound := by
  intro adversary hAllowed
  rw [sharedIKSK_advantage_eq_fullIndependent dimension discarded retained
    encryptionKeySampler embedEncryptionKey prefixSampler suffixSampler
    prefixMessage suffixMessage errorSampler hPrefix hError adversary]
  exact hFull _ (hReductionClosed adversary hAllowed)

end FullIndependentComparison

section GadgetLayouts

/-- Gadget encodings for one ciphertext per input coordinate and level.  Coordinates are grouped
contiguously, and `finProdFinEquiv` supplies the checked flattening. -/
def leveledMessage {R : Type} [Mul R] (coordinateCount levelCount : ℕ)
    (gadget : Fin levelCount → R) (secret : Fin coordinateCount → R) :
    Fin (coordinateCount * levelCount) → R := fun index ↦
  let pair := finProdFinEquiv.symm index
  secret pair.1 * gadget pair.2

/-- Gadget encodings for the table layout used by `NewSwitchKeyGen` in ePrint 2023/958: one
ciphertext for every input coordinate, level, and digit value. -/
def digitTableMessage {R : Type} [Mul R]
    (coordinateCount levelCount digitCount : ℕ)
    (gadget : Fin levelCount → Fin digitCount → R)
    (secret : Fin coordinateCount → R) :
    Fin (coordinateCount * (levelCount * digitCount)) → R := fun index ↦
  let outer := finProdFinEquiv.symm index
  let inner := finProdFinEquiv.symm outer.2
  secret outer.1 * gadget inner.1 inner.2

/-- The conventional and suffix-only leveled IKSK sample counts split exactly by distributivity. -/
theorem fullLeveledSampleCount_eq
    (outputCoordinates suffixCoordinates levelCount : ℕ) :
    outputCoordinates * levelCount + suffixCoordinates * levelCount =
      (outputCoordinates + suffixCoordinates) * levelCount := by
  exact (Nat.add_mul outputCoordinates suffixCoordinates levelCount).symm

/-- The corresponding exact count identity for the level-by-digit table layout. -/
theorem fullDigitTableSampleCount_eq
    (outputCoordinates suffixCoordinates levelCount digitCount : ℕ) :
    outputCoordinates * (levelCount * digitCount) +
        suffixCoordinates * (levelCount * digitCount) =
      (outputCoordinates + suffixCoordinates) * (levelCount * digitCount) := by
  exact (Nat.add_mul outputCoordinates suffixCoordinates
    (levelCount * digitCount)).symm

end GadgetLayouts

section TwoPairComposition

/-- Sample two public views independently.  The two component types and parameter sets may be
different. -/
def sampleViewPair {First Second : Type}
    (first : ProbComp First) (second : ProbComp Second) : ProbComp (First × Second) := do
  let firstView ← first
  let secondView ← second
  return (firstView, secondView)

/-- Apply the corresponding full-to-shared projection to each of two public IKSK components. -/
def projectViewPair {FullFirst FullSecond SharedFirst SharedSecond : Type}
    (firstProjection : FullFirst → SharedFirst)
    (secondProjection : FullSecond → SharedSecond)
    (view : FullFirst × FullSecond) : SharedFirst × SharedSecond :=
  (firstProjection view.1, secondProjection view.2)

/-- A distinguisher's two-component real-versus-uniform advantage. -/
noncomputable def twoPairAdvantage {First Second : Type}
    (realFirst uniformFirst : ProbComp First)
    (realSecond uniformSecond : ProbComp Second)
    (adversary : First × Second → ProbComp Bool) : ℝ :=
  (sampleViewPair realFirst realSecond >>= adversary).boolDistAdvantage
    (sampleViewPair uniformFirst uniformSecond >>= adversary)

/-- Project both components before invoking a two-shared-IKSK distinguisher. -/
def twoPairProjectionReduction
    {FullFirst FullSecond SharedFirst SharedSecond : Type}
    (firstProjection : FullFirst → SharedFirst)
    (secondProjection : FullSecond → SharedSecond)
    (adversary : SharedFirst × SharedSecond → ProbComp Bool) :
    FullFirst × FullSecond → ProbComp Bool :=
  fun view ↦ adversary (projectViewPair firstProjection secondProjection view)

/-- Componentwise projection commutes exactly with independently sampling two public views. -/
theorem sampleViewPair_project_evalDist
    {FullFirst FullSecond SharedFirst SharedSecond : Type}
    (fullFirst : ProbComp FullFirst) (fullSecond : ProbComp FullSecond)
    (sharedFirst : ProbComp SharedFirst) (sharedSecond : ProbComp SharedSecond)
    (firstProjection : FullFirst → SharedFirst)
    (secondProjection : FullSecond → SharedSecond)
    (hFirst : 𝒟[firstProjection <$> fullFirst] = 𝒟[sharedFirst])
    (hSecond : 𝒟[secondProjection <$> fullSecond] = 𝒟[sharedSecond]) :
    𝒟[projectViewPair firstProjection secondProjection <$>
        sampleViewPair fullFirst fullSecond] =
      𝒟[sampleViewPair sharedFirst sharedSecond] := by
  have left_eq :
      (projectViewPair firstProjection secondProjection <$>
        sampleViewPair fullFirst fullSecond) =
      ((firstProjection <$> fullFirst) >>= fun firstView ↦
        (secondProjection <$> fullSecond) >>= fun secondView ↦
        pure (firstView, secondView)) := by
    simp [sampleViewPair, projectViewPair, bind_assoc, monad_norm]
  rw [left_eq]
  calc
    _ = 𝒟[sharedFirst >>= fun firstView ↦
        (secondProjection <$> fullSecond) >>= fun secondView ↦
        pure (firstView, secondView)] :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hFirst _
    _ = 𝒟[sharedFirst >>= fun firstView ↦
        sharedSecond >>= fun secondView ↦ pure (firstView, secondView)] := by
      refine evalDist_bind_congr' sharedFirst fun firstView ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hSecond _
    _ = _ := by rfl

/-- Exact two-pair comparison.  If both shared components are exact projections of their
full-independent counterparts on the real and uniform branches, projecting them jointly preserves
the complete two-pair advantage.  In particular there is no factor-two hybrid loss. -/
theorem twoPairProjection_advantage_eq
    {FullFirst FullSecond SharedFirst SharedSecond : Type}
    (fullRealFirst fullUniformFirst : ProbComp FullFirst)
    (fullRealSecond fullUniformSecond : ProbComp FullSecond)
    (sharedRealFirst sharedUniformFirst : ProbComp SharedFirst)
    (sharedRealSecond sharedUniformSecond : ProbComp SharedSecond)
    (firstProjection : FullFirst → SharedFirst)
    (secondProjection : FullSecond → SharedSecond)
    (hRealFirst : 𝒟[firstProjection <$> fullRealFirst] = 𝒟[sharedRealFirst])
    (hUniformFirst : 𝒟[firstProjection <$> fullUniformFirst] = 𝒟[sharedUniformFirst])
    (hRealSecond : 𝒟[secondProjection <$> fullRealSecond] = 𝒟[sharedRealSecond])
    (hUniformSecond : 𝒟[secondProjection <$> fullUniformSecond] = 𝒟[sharedUniformSecond])
    (adversary : SharedFirst × SharedSecond → ProbComp Bool) :
    twoPairAdvantage sharedRealFirst sharedUniformFirst sharedRealSecond sharedUniformSecond
        adversary =
      twoPairAdvantage fullRealFirst fullUniformFirst fullRealSecond fullUniformSecond
        (twoPairProjectionReduction firstProjection secondProjection adversary) := by
  have hReal := sampleViewPair_project_evalDist
    fullRealFirst fullRealSecond sharedRealFirst sharedRealSecond
    firstProjection secondProjection hRealFirst hRealSecond
  have hUniform := sampleViewPair_project_evalDist
    fullUniformFirst fullUniformSecond sharedUniformFirst sharedUniformSecond
    firstProjection secondProjection hUniformFirst hUniformSecond
  unfold twoPairAdvantage ProbComp.boolDistAdvantage twoPairProjectionReduction
  have realGame_eq :
      𝒟[sampleViewPair fullRealFirst fullRealSecond >>= fun view ↦
          adversary (projectViewPair firstProjection secondProjection view)] =
        𝒟[sampleViewPair sharedRealFirst sharedRealSecond >>= adversary] := by
    rw [show (sampleViewPair fullRealFirst fullRealSecond >>= fun view ↦
        adversary (projectViewPair firstProjection secondProjection view)) =
      ((projectViewPair firstProjection secondProjection <$>
        sampleViewPair fullRealFirst fullRealSecond) >>= adversary) by
      simp [bind_assoc, monad_norm], evalDist_bind, hReal, ← evalDist_bind]
  have uniformGame_eq :
      𝒟[sampleViewPair fullUniformFirst fullUniformSecond >>= fun view ↦
          adversary (projectViewPair firstProjection secondProjection view)] =
        𝒟[sampleViewPair sharedUniformFirst sharedUniformSecond >>= adversary] := by
    rw [show (sampleViewPair fullUniformFirst fullUniformSecond >>= fun view ↦
        adversary (projectViewPair firstProjection secondProjection view)) =
      ((projectViewPair firstProjection secondProjection <$>
        sampleViewPair fullUniformFirst fullUniformSecond) >>= adversary) by
      simp [bind_assoc, monad_norm], evalDist_bind, hUniform, ← evalDist_bind]
  rw [evalDist_ext_iff.mp realGame_eq true, evalDist_ext_iff.mp uniformGame_eq true]

end TwoPairComposition

section BlockBinarySpecialization

/-- Shared-randomness IKSK whose encryption key is sampled from the compact block-binary key
space. -/
def blockBinarySharedIKSKProblem {R SuffixSecret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount samples : ℕ)
    (suffixSampler : ProbComp SuffixSecret)
    (suffixMessage : SuffixSecret → Fin samples → R)
    (errorSampler : ProbComp R) :=
  sharedIKSKProblem (blockCount * blockLength) samples
    ($ᵗ (FormalProof4FHE.BlockBinary.Key blockLength blockCount))
    (FormalProof4FHE.BlockBinary.expand R)
    suffixSampler suffixMessage errorSampler

/-- Exact reduction from a shared IKSK under a block-binary encryption key to block-binary LWE. -/
def blockBinarySharedIKSKReduction {R SuffixSecret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    {blockLength blockCount samples : ℕ}
    (suffixSampler : ProbComp SuffixSecret)
    (suffixMessage : SuffixSecret → Fin samples → R)
    {errorSampler : ProbComp R}
    (adversary : LearningWithErrors.Adversary
      (blockBinarySharedIKSKProblem blockLength blockCount samples
        suffixSampler suffixMessage errorSampler)) :
    LearningWithErrors.Adversary
      (FormalProof4FHE.BlockBinary.problem
        blockLength blockCount samples errorSampler) :=
  affineIKSKReduction suffixSampler suffixMessage adversary

/-- A shared IKSK under a block-binary encryption key has exactly the advantage of the constructed
block-binary-LWE distinguisher. -/
theorem blockBinarySharedIKSK_advantage_eq {R SuffixSecret : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount samples : ℕ)
    (suffixSampler : ProbComp SuffixSecret)
    (suffixMessage : SuffixSecret → Fin samples → R)
    (errorSampler : ProbComp R)
    (hSuffix : Pr[⊥ | suffixSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (blockBinarySharedIKSKProblem blockLength blockCount samples
        suffixSampler suffixMessage errorSampler)) :
    LearningWithErrors.advantage
        (blockBinarySharedIKSKProblem blockLength blockCount samples
          suffixSampler suffixMessage errorSampler) adversary =
      LearningWithErrors.advantage
        (FormalProof4FHE.BlockBinary.problem
          blockLength blockCount samples errorSampler)
        (blockBinarySharedIKSKReduction suffixSampler suffixMessage adversary) := by
  simpa [blockBinarySharedIKSKProblem, blockBinarySharedIKSKReduction,
    sharedIKSKProblem, FormalProof4FHE.LWE.embeddedBatchProblem,
    FormalProof4FHE.BlockBinary.problem] using
    (affineIKSK_advantage_eq_lwe
      (R := R)
      (dimension := blockCount * blockLength) (samples := samples)
      ($ᵗ (FormalProof4FHE.BlockBinary.Key blockLength blockCount))
      (FormalProof4FHE.BlockBinary.expand R)
      suffixSampler suffixMessage errorSampler hSuffix adversary)

/-- Fully discharged nonlinear ordinary-LWE bound for a shared IKSK under a block-binary
encryption key.  The IKSK layer itself is lossless; every term is inherited from the previously
proved block-binary reduction. -/
theorem blockBinarySharedIKSK_advantage_le_of_ordinaryLWEBounds_nonlinear
    {R SuffixSecret : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension samples : ℕ)
    (suffixSampler : ProbComp SuffixSecret)
    (suffixMessage : SuffixSecret → Fin samples → R)
    (narrowErrorSampler errorSampler : ProbComp R)
    (hSuffix : Pr[⊥ | suffixSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (blockBinarySharedIKSKProblem blockLength blockCount samples
        suffixSampler suffixMessage errorSampler))
    (narrowBound wideBound : ℝ)
    (hNarrow : ∀ reduction : LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem extractedDimension samples
        ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler),
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension samples
          ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
        reduction ≤ narrowBound)
    (hWide : ∀ reduction : LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem extractedDimension samples
        ($ᵗ (Fin extractedDimension → R)) errorSampler),
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension samples
          ($ᵗ (Fin extractedDimension → R)) errorSampler)
        reduction ≤ wideBound) :
    LearningWithErrors.advantage
        (blockBinarySharedIKSKProblem blockLength blockCount samples
          suffixSampler suffixMessage errorSampler) adversary ≤
      min 1
        (2 * ((blockCount * blockLength : ℕ) : ℝ) * narrowBound +
          FormalProof4FHE.BlockBinary.nonlinearNoiseAbsorptionCost
            blockLength blockCount extractedDimension samples
            narrowErrorSampler errorSampler +
          Real.sqrt
              (((Fintype.card R : ℝ) ^ extractedDimension - 1) /
                (blockLength + 1 : ℝ) ^ blockCount) /
            2 +
          wideBound) := by
  rw [blockBinarySharedIKSK_advantage_eq blockLength blockCount samples
    suffixSampler suffixMessage errorSampler hSuffix adversary]
  exact FormalProof4FHE.BlockBinary.advantage_le_of_ordinaryLWEBounds_nonlinear
    blockLength blockCount extractedDimension samples narrowErrorSampler errorSampler
    (blockBinarySharedIKSKReduction suffixSampler suffixMessage adversary)
    narrowBound wideBound hNarrow hWide

end BlockBinarySpecialization

end FormalProof4FHE.SharedRandomness.KeySwitching
