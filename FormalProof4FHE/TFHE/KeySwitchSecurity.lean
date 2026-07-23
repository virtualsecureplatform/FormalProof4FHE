/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.Native

/-!
# Security of the Native TFHE Key-Switch Component

After the bootstrapping-key messages have been replaced by zero, the native TFHE key-switch key
encrypts gadget multiples of an independently sampled extracted ring key under the scalar TLWE
key.  This file proves the cloud-key-only replacement hop from those real key-switch messages to
zero messages.

The proof uses a shared uniform-transcript hybrid.  On the real-message side, a reduction samples
the ring key and its zero-message bootstrapping key, then adds the complete gadget-message vector
to one binary-secret batch-LWE challenge.  On the zero-message side, a second reduction passes the
same challenge unchanged.  Conditional translation of the uniform output vector proves that the
two reductions have exactly the same uniform branch.  Therefore the native replacement advantage
is at most the sum of their two ordinary binary-secret LWE advantages.

This theorem is intentionally stated for the cloud-key-only view.  A later TFHE IND-CPA
instantiation must place the challenge TLWE ciphertext in the same batch-LWE reduction; an
arbitrary payload depending on the hidden TLWE key cannot be sampled by a black-box LWE
distinguisher.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.KeySwitchSecurity

/-- Binary-secret batch LWE underlying native scalar TLWE rows. -/
def binaryLweProblem (q dimension samples : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q)) :=
  FormalProof4FHE.LWE.embeddedBatchProblem dimension samples
    (sampleLweSecret dimension) embedBinarySecret errorSampler

/-- Add all native gadget-scaled extracted-key messages to a batch-LWE transcript. -/
def addKeySwitchMessages
    (q sourceDimension keySwitchLevels : ℕ)
    (gadget : Fin keySwitchLevels → ZMod q)
    (sourceSecret : BinarySecret sourceDimension)
    {targetDimension : ℕ}
    (transcript : TLWE.BatchCiphertext (ZMod q) targetDimension
      (sourceDimension * keySwitchLevels)) :
    TLWE.BatchCiphertext (ZMod q) targetDimension
      (sourceDimension * keySwitchLevels) :=
  (transcript.1, transcript.2 +
    keySwitchMessages sourceDimension keySwitchLevels gadget sourceSecret)

/-- Shifting a zero-message assembled batch produces exactly the native real-message batch. -/
@[simp]
theorem addKeySwitchMessages_batchAssemble_zero
    (q targetDimension sourceDimension keySwitchLevels : ℕ)
    (gadget : Fin keySwitchLevels → ZMod q)
    (sourceSecret : BinarySecret sourceDimension)
    (targetSecret : Fin targetDimension → ZMod q)
    (challenge : Matrix (Fin targetDimension)
      (Fin (sourceDimension * keySwitchLevels)) (ZMod q))
    (error : Fin (sourceDimension * keySwitchLevels) → ZMod q) :
    addKeySwitchMessages q sourceDimension keySwitchLevels gadget sourceSecret
        (TLWE.batchAssemble targetSecret challenge 0 error) =
      TLWE.batchAssemble targetSecret challenge
        (keySwitchMessages sourceDimension keySwitchLevels gadget sourceSecret) error := by
  apply Prod.ext
  · rfl
  · funext row
    simp only [addKeySwitchMessages, TLWE.batchAssemble, Pi.add_apply,
      Pi.zero_apply]
    abel

/-- Raw ordinary-LWE transcript form of the same whole-batch message shift. -/
@[simp]
theorem addKeySwitchMessages_lweTranscript
    (q targetDimension sourceDimension keySwitchLevels : ℕ)
    (gadget : Fin keySwitchLevels → ZMod q)
    (sourceSecret : BinarySecret sourceDimension)
    (targetSecret : Fin targetDimension → ZMod q)
    (challenge : Matrix (Fin targetDimension)
      (Fin (sourceDimension * keySwitchLevels)) (ZMod q))
    (error : Fin (sourceDimension * keySwitchLevels) → ZMod q) :
    addKeySwitchMessages q sourceDimension keySwitchLevels gadget sourceSecret
        (challenge, vecMul targetSecret challenge + error) =
      TLWE.batchAssemble targetSecret challenge
        (keySwitchMessages sourceDimension keySwitchLevels gadget sourceSecret) error := by
  apply Prod.ext
  · rfl
  · funext row
    simp only [addKeySwitchMessages, TLWE.batchAssemble, Pi.add_apply]
    abel

/-- A zero-message bootstrapping key bundled with the ring key that generated it.  This complete
context is independent of the scalar TLWE encryption key. -/
noncomputable def zeroBootstrapContext
    (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree) :
    ProbComp (RingBinarySecret ringRank degree ×
      BootstrappingKey q degree ringRank tgswLevels lweDimension) := do
  let ringSecret ← sampleRingSecret ringRank degree
  let bootstrapKey ← generateZeroBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget ringSecret
  return (ringSecret, bootstrapKey)

/-- Reorder four independent draws from
`first; second; third; fourth` to `third; first; fourth; second`. -/
theorem evalDist_bind_four_reorder
    {First Second Third Fourth Output : Type}
    (first : ProbComp First) (second : ProbComp Second)
    (third : ProbComp Third) (fourth : ProbComp Fourth)
    (finish : First → Second → Third → Fourth → ProbComp Output) :
    evalDist (first >>= fun firstValue ↦
      second >>= fun secondValue ↦
      third >>= fun thirdValue ↦
      fourth >>= fun fourthValue ↦
      finish firstValue secondValue thirdValue fourthValue) =
    evalDist (third >>= fun thirdValue ↦
      first >>= fun firstValue ↦
      fourth >>= fun fourthValue ↦
      second >>= fun secondValue ↦
      finish firstValue secondValue thirdValue fourthValue) := by
  calc
    _ = evalDist (first >>= fun firstValue ↦
        third >>= fun thirdValue ↦
        second >>= fun secondValue ↦
        fourth >>= fun fourthValue ↦
        finish firstValue secondValue thirdValue fourthValue) := by
      refine evalDist_bind_congr' first fun firstValue ↦ ?_
      exact evalDist_bind_bind_swap second third
        (fun secondValue thirdValue ↦ fourth >>= fun fourthValue ↦
          finish firstValue secondValue thirdValue fourthValue)
    _ = evalDist (third >>= fun thirdValue ↦
        first >>= fun firstValue ↦
        second >>= fun secondValue ↦
        fourth >>= fun fourthValue ↦
        finish firstValue secondValue thirdValue fourthValue) :=
      evalDist_bind_bind_swap first third
        (fun firstValue thirdValue ↦ second >>= fun secondValue ↦
          fourth >>= fun fourthValue ↦
          finish firstValue secondValue thirdValue fourthValue)
    _ = _ := by
      refine evalDist_bind_congr' third fun thirdValue ↦ ?_
      refine evalDist_bind_congr' first fun firstValue ↦ ?_
      exact evalDist_bind_bind_swap second fourth
        (fun secondValue fourthValue ↦
          finish firstValue secondValue thirdValue fourthValue)

/-- Conditional translation of a uniform output vector remains uniform even when the translation
is correlated with an independently sampled public context. -/
theorem uniformTranscript_context_shift_evalDist
    {R Context Output : Type} [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ) (contextSampler : ProbComp Context)
    (message : Context → Fin samples → R)
    (finish : Context → FormalProof4FHE.LWE.BatchTranscript R dimension samples →
      ProbComp Output) :
    evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge ↦
      ($ᵗ (Fin samples → R)) >>= fun output ↦
      contextSampler >>= fun context ↦
      finish context (challenge, output + message context)) =
    evalDist (($ᵗ Matrix (Fin dimension) (Fin samples) R) >>= fun challenge ↦
      ($ᵗ (Fin samples → R)) >>= fun output ↦
      contextSampler >>= fun context ↦
      finish context (challenge, output)) := by
  refine evalDist_bind_congr' ($ᵗ Matrix (Fin dimension) (Fin samples) R) fun challenge ↦ ?_
  calc
    _ = evalDist (contextSampler >>= fun context ↦
        ($ᵗ (Fin samples → R)) >>= fun output ↦
        finish context (challenge, output + message context)) :=
      evalDist_bind_bind_swap ($ᵗ (Fin samples → R)) contextSampler
        (fun output context ↦ finish context (challenge, output + message context))
    _ = evalDist (contextSampler >>= fun context ↦
        ($ᵗ (Fin samples → R)) >>= fun output ↦
        finish context (challenge, output)) := by
      refine evalDist_bind_congr' contextSampler fun context ↦ ?_
      simpa only [id_eq] using
        (evalDist_bind_bijective_add_right_uniform
          (α := Fin samples → R) (β := Fin samples → R)
          id Function.bijective_id (message context)
          (fun output ↦ finish context (challenge, output)))
    _ = _ :=
      (evalDist_bind_bind_swap ($ᵗ (Fin samples → R)) contextSampler
        (fun output context ↦ finish context (challenge, output))).symm

section NativeReduction

variable {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
  [NeZero q]

/-- LWE reduction for the real-message endpoint of native key-switch replacement. -/
noncomputable def realMessageReduction
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Circular.Adversary Unit
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) :
    LearningWithErrors.Adversary
      (binaryLweProblem q lweDimension
        ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler) :=
  fun transcript ↦ do
    let context ← zeroBootstrapContext q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget
    adversary ⟨(), context.2,
      addKeySwitchMessages q (ringRank * degree) keySwitchLevels keySwitchGadget
        (keyExtract context.1) transcript⟩

/-- LWE reduction for the zero-message endpoint of native key-switch replacement. -/
noncomputable def zeroMessageReduction
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (adversary : Circular.Adversary Unit
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) :
    LearningWithErrors.Adversary
      (binaryLweProblem q lweDimension
        ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler) :=
  fun transcript ↦ do
    let context ← zeroBootstrapContext q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget
    adversary ⟨(), context.2, transcript⟩

/-- The native bootstrapping-zero/key-switch-real endpoint is exactly the real LWE game of the
message-adding reduction. -/
theorem bootstrapZeroGame_evalDist_eq_lwe_game0
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Circular.Adversary Unit
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) :
    evalDist (Circular.bootstrapZeroGame
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload adversary) =
      evalDist (LearningWithErrors.game0
        (binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (realMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget adversary)) := by
  let scalarSecrets := sampleLweSecret lweDimension
  let contexts := zeroBootstrapContext q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget
  let challenges : ProbComp (Matrix (Fin lweDimension)
      (Fin ((ringRank * degree) * keySwitchLevels)) (ZMod q)) :=
    $ᵗ Matrix (Fin lweDimension) (Fin ((ringRank * degree) * keySwitchLevels)) (ZMod q)
  let errors := ProbComp.sampleIID ((ringRank * degree) * keySwitchLevels)
    keySwitchErrorSampler
  let finish := fun (lweSecret : BinarySecret lweDimension)
      (context : RingBinarySecret ringRank degree ×
        BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (challenge : Matrix (Fin lweDimension)
        (Fin ((ringRank * degree) * keySwitchLevels)) (ZMod q))
      (error : Fin ((ringRank * degree) * keySwitchLevels) → ZMod q) ↦
    adversary ⟨(), context.2,
      TLWE.batchAssemble (embedBinarySecret lweSecret) challenge
        (keySwitchMessages (ringRank * degree) keySwitchLevels keySwitchGadget
          (keyExtract context.1)) error⟩
  have native_eq : Circular.bootstrapZeroGame
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload adversary =
      (scalarSecrets >>= fun lweSecret ↦
        contexts >>= fun context ↦
        challenges >>= fun challenge ↦
        errors >>= fun error ↦
        finish lweSecret context challenge error) := by
    simp [Circular.bootstrapZeroGame, Circular.bootstrapZeroView,
      Circular.evaluationKeyOnlyPayload, nativeCycleSpec, scalarSecrets, contexts,
      zeroBootstrapContext, generateKeySwitchKey, TLWE.batchEncrypt, finish,
      bind_assoc, monad_norm]
    rfl
  have lwe_eq : LearningWithErrors.game0
        (binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (realMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget adversary) =
      (challenges >>= fun challenge ↦
        scalarSecrets >>= fun lweSecret ↦
        errors >>= fun error ↦
        contexts >>= fun context ↦
        finish lweSecret context challenge error) := by
    simp [LearningWithErrors.game0, LearningWithErrors.distr, binaryLweProblem,
      FormalProof4FHE.LWE.embeddedBatchProblem, realMessageReduction,
      scalarSecrets, contexts, challenges, errors,
      finish, bind_assoc, monad_norm]
  rw [native_eq, lwe_eq]
  exact evalDist_bind_four_reorder scalarSecrets contexts challenges errors finish

/-- The native all-zero-message endpoint is exactly the real LWE game of the pass-through
reduction. -/
theorem zeroGame_evalDist_eq_lwe_game0
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Circular.Adversary Unit
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) :
    evalDist (Circular.zeroGame
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload adversary) =
      evalDist (LearningWithErrors.game0
        (binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (zeroMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget adversary)) := by
  let scalarSecrets := sampleLweSecret lweDimension
  let contexts := zeroBootstrapContext q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget
  let challenges : ProbComp (Matrix (Fin lweDimension)
      (Fin ((ringRank * degree) * keySwitchLevels)) (ZMod q)) :=
    $ᵗ Matrix (Fin lweDimension) (Fin ((ringRank * degree) * keySwitchLevels)) (ZMod q)
  let errors := ProbComp.sampleIID ((ringRank * degree) * keySwitchLevels)
    keySwitchErrorSampler
  let finish := fun (lweSecret : BinarySecret lweDimension)
      (context : RingBinarySecret ringRank degree ×
        BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (challenge : Matrix (Fin lweDimension)
        (Fin ((ringRank * degree) * keySwitchLevels)) (ZMod q))
      (error : Fin ((ringRank * degree) * keySwitchLevels) → ZMod q) ↦
    adversary ⟨(), context.2,
      TLWE.batchAssemble (embedBinarySecret lweSecret) challenge 0 error⟩
  have native_eq : Circular.zeroGame
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload adversary =
      (scalarSecrets >>= fun lweSecret ↦
        contexts >>= fun context ↦
        challenges >>= fun challenge ↦
        errors >>= fun error ↦
        finish lweSecret context challenge error) := by
    simp [Circular.zeroGame, Circular.zeroView, Circular.evaluationKeyOnlyPayload,
      nativeCycleSpec, scalarSecrets, contexts, zeroBootstrapContext,
      generateZeroKeySwitchKey, TLWE.batchEncrypt, finish, bind_assoc, monad_norm]
    rfl
  have lwe_eq : LearningWithErrors.game0
        (binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (zeroMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget adversary) =
      (challenges >>= fun challenge ↦
        scalarSecrets >>= fun lweSecret ↦
        errors >>= fun error ↦
        contexts >>= fun context ↦
        finish lweSecret context challenge error) := by
    simp [LearningWithErrors.game0, LearningWithErrors.distr, binaryLweProblem,
      FormalProof4FHE.LWE.embeddedBatchProblem, zeroMessageReduction,
      scalarSecrets, contexts, challenges, errors, finish, bind_assoc, monad_norm]
  rw [native_eq, lwe_eq]
  exact evalDist_bind_four_reorder scalarSecrets contexts challenges errors finish

/-- The two LWE reductions share exactly the same uniform branch. -/
theorem reductions_game1_evalDist_eq
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Circular.Adversary Unit
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) :
    evalDist (LearningWithErrors.game1
        (binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (realMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget adversary)) =
      evalDist (LearningWithErrors.game1
        (binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (zeroMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget adversary)) := by
  let contexts := zeroBootstrapContext q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget
  have real_eq : LearningWithErrors.game1
        (binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (realMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget adversary) =
      (($ᵗ Matrix (Fin lweDimension)
          (Fin ((ringRank * degree) * keySwitchLevels)) (ZMod q)) >>= fun challenge ↦
        ($ᵗ (Fin ((ringRank * degree) * keySwitchLevels) → ZMod q)) >>= fun output ↦
        contexts >>= fun context ↦
        adversary ⟨(), context.2,
          (challenge, output + keySwitchMessages (ringRank * degree) keySwitchLevels
            keySwitchGadget (keyExtract context.1))⟩) := by
    simp [LearningWithErrors.game1, LearningWithErrors.uniformDistr, binaryLweProblem,
      FormalProof4FHE.LWE.embeddedBatchProblem, realMessageReduction,
      addKeySwitchMessages, contexts, bind_assoc, monad_norm]
  have zero_eq : LearningWithErrors.game1
        (binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (zeroMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget adversary) =
      (($ᵗ Matrix (Fin lweDimension)
          (Fin ((ringRank * degree) * keySwitchLevels)) (ZMod q)) >>= fun challenge ↦
        ($ᵗ (Fin ((ringRank * degree) * keySwitchLevels) → ZMod q)) >>= fun output ↦
        contexts >>= fun context ↦
        adversary ⟨(), context.2, (challenge, output)⟩) := by
    simp [LearningWithErrors.game1, LearningWithErrors.uniformDistr, binaryLweProblem,
      FormalProof4FHE.LWE.embeddedBatchProblem, zeroMessageReduction,
      contexts, bind_assoc, monad_norm]
  rw [real_eq, zero_eq]
  exact uniformTranscript_context_shift_evalDist
    lweDimension ((ringRank * degree) * keySwitchLevels) contexts
    (fun context ↦ keySwitchMessages (ringRank * degree) keySwitchLevels
      keySwitchGadget (keyExtract context.1))
    (fun context transcript ↦ adversary ⟨(), context.2, transcript⟩)

/-- **Native key-switch replacement theorem.**  In the cloud-key-only game, after all
bootstrapping-key messages have been replaced by zero, replacing the direct TLWE key-switch
messages costs at most two binary-secret batch-LWE advantages. -/
theorem keySwitchReplacementAdvantage_le_two_lwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Circular.Adversary Unit
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) :
    Circular.keySwitchReplacementAdvantage
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload adversary ≤
      LearningWithErrors.advantage
        (binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (realMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget adversary) +
      LearningWithErrors.advantage
        (binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (zeroMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold Circular.keySwitchReplacementAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (bootstrapZeroGame_evalDist_eq_lwe_game0 ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget adversary) true,
    evalDist_ext_iff.mp
      (zeroGame_evalDist_eq_lwe_game0 ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget adversary) true]
  let realProbability : ℝ := (Pr[= true | LearningWithErrors.game0
    (binaryLweProblem q lweDimension ((ringRank * degree) * keySwitchLevels)
      keySwitchErrorSampler)
    (realMessageReduction ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget adversary)]).toReal
  let uniformRealProbability : ℝ := (Pr[= true | LearningWithErrors.game1
    (binaryLweProblem q lweDimension ((ringRank * degree) * keySwitchLevels)
      keySwitchErrorSampler)
    (realMessageReduction ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget adversary)]).toReal
  let uniformZeroProbability : ℝ := (Pr[= true | LearningWithErrors.game1
    (binaryLweProblem q lweDimension ((ringRank * degree) * keySwitchLevels)
      keySwitchErrorSampler)
    (zeroMessageReduction ringErrorSampler keySwitchErrorSampler
      tgswGadget adversary)]).toReal
  let zeroProbability : ℝ := (Pr[= true | LearningWithErrors.game0
    (binaryLweProblem q lweDimension ((ringRank * degree) * keySwitchLevels)
      keySwitchErrorSampler)
    (zeroMessageReduction ringErrorSampler keySwitchErrorSampler
      tgswGadget adversary)]).toReal
  have hUniform : uniformRealProbability = uniformZeroProbability := by
    exact congrArg ENNReal.toReal (evalDist_ext_iff.mp
      (reductions_game1_evalDist_eq ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget adversary) true)
  change |realProbability - zeroProbability| ≤
    |realProbability - uniformRealProbability| +
      |zeroProbability - uniformZeroProbability|
  rw [hUniform, abs_sub_comm zeroProbability uniformZeroProbability]
  exact abs_sub_le realProbability uniformZeroProbability zeroProbability

/-- Native cloud-key circular advantage with the direct key-switch hop expanded into its two
binary-secret LWE terms. Only the structured bootstrapping replacement remains unexpanded in this
module; `TFHE.BootstrappingSecurity` gives its exact direct-bilinear KDM presentation. -/
theorem circularAdvantage_le_bootstrap_add_two_lwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Circular.Adversary Unit
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)) :
    Circular.circularAdvantage
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload adversary ≤
      Circular.bootstrapReplacementAdvantage
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload adversary +
      LearningWithErrors.advantage
        (binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (realMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget adversary) +
      LearningWithErrors.advantage
        (binaryLweProblem q lweDimension
          ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
        (zeroMessageReduction ringErrorSampler keySwitchErrorSampler
          tgswGadget adversary) := by
  have hCircular := Circular.circularAdvantage_le_replacements
    (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    Circular.evaluationKeyOnlyPayload adversary
  have hKeySwitch := keySwitchReplacementAdvantage_le_two_lwe
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary
  linarith

/-- Concrete bound form: a bound for the native structured bootstrap replacement plus one
binary-secret LWE hardness bound for both explicit reductions yields cloud-key circular security. -/
theorem circularAdvantage_le_of_bootstrap_and_lwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Circular.Adversary Unit
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels))
    (lweAllowed : LearningWithErrors.Adversary
      (binaryLweProblem q lweDimension
        ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler) → Prop)
    (bootstrapBound lweBound : ℝ)
    (hBootstrap : Circular.bootstrapReplacementAdvantage
      (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      Circular.evaluationKeyOnlyPayload adversary ≤ bootstrapBound)
    (hRealAllowed : lweAllowed
      (realMessageReduction ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget adversary))
    (hZeroAllowed : lweAllowed
      (zeroMessageReduction ringErrorSampler keySwitchErrorSampler
        tgswGadget adversary))
    (hLWE : FormalProof4FHE.LWE.HardAgainst
      (binaryLweProblem q lweDimension
        ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
      lweAllowed lweBound) :
    Circular.circularAdvantage
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload adversary ≤ bootstrapBound + 2 * lweBound := by
  have hExpanded := circularAdvantage_le_bootstrap_add_two_lwe
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary
  have hReal := hLWE _ hRealAllowed
  have hZero := hLWE _ hZeroAllowed
  linarith

/-- Adversary-class form of the preceding conditional native cloud-key security theorem. -/
theorem circularHardAgainst_of_bootstrap_and_lwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tfheAllowed : Circular.Adversary Unit
      (BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) → Prop)
    (lweAllowed : LearningWithErrors.Adversary
      (binaryLweProblem q lweDimension
        ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler) → Prop)
    (bootstrapBound lweBound : ℝ)
    (hBootstrap : ∀ adversary, tfheAllowed adversary →
      Circular.bootstrapReplacementAdvantage
        (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        Circular.evaluationKeyOnlyPayload adversary ≤ bootstrapBound)
    (hRealClosed : ∀ adversary, tfheAllowed adversary → lweAllowed
      (realMessageReduction ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget adversary))
    (hZeroClosed : ∀ adversary, tfheAllowed adversary → lweAllowed
      (zeroMessageReduction ringErrorSampler keySwitchErrorSampler
        tgswGadget adversary))
    (hLWE : FormalProof4FHE.LWE.HardAgainst
      (binaryLweProblem q lweDimension
        ((ringRank * degree) * keySwitchLevels) keySwitchErrorSampler)
      lweAllowed lweBound) :
    Circular.CircularHardAgainst
      (nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      Circular.evaluationKeyOnlyPayload tfheAllowed (bootstrapBound + 2 * lweBound) := by
  intro adversary hadversary
  exact circularAdvantage_le_of_bootstrap_and_lwe
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary
    lweAllowed bootstrapBound lweBound (hBootstrap adversary hadversary)
    (hRealClosed adversary hadversary) (hZeroClosed adversary hadversary) hLWE

end NativeReduction

end FormalProof4FHE.TFHE.Native.KeySwitchSecurity
