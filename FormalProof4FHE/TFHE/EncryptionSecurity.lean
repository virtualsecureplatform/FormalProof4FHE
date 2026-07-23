/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.TwoBlock
import FormalProof4FHE.TFHE.Encryption
import FormalProof4FHE.TFHE.KeySwitchSecurity

/-!
# LWE Security of Native TFHE Encryption

This file discharges the ordinary-LWE base case of native TFHE's adaptive one-time encryption
game.  In the all-zero-message cloud-key hybrid, the scalar key is used by two public families:

* all zero-message direct-TLWE rows of the key-switch key; and
* the fresh scalar TLWE encryption challenge chosen after the cloud key is visible.

They must be placed in one shared-secret LWE instance.  Treating the challenge independently
would lose the correlation through the hidden scalar key.  The reduction therefore consumes an
unequal two-block transcript: the first block has all key-switch rows, while the second has one
challenge row.  The two blocks retain separate error samplers, matching TFHE parameter sets in
which key-switch and input ciphertext noise differ.

The real LWE branch is exactly the native zero-cloud game.  In the uniform branch, the one-row
transcript is a one-time pad for the adaptively selected encoded message, so the adversary wins
with probability one half.  Consequently the absolute signed IND-CPA advantage of the zero-cloud
game is exactly the constructed heterogeneous binary-secret LWE advantage.  When both noise
samplers coincide, `LWE.TwoBlock.advantage_eq_batch` further identifies this with ordinary batch
LWE on the sum of the sample counts.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Security

/-- Reorder six independent samplers from `first; second; third; fourth; fifth; sixth` to
`third; fifth; first; fourth; sixth; second`. -/
theorem evalDist_bind_six_reorder
    {First Second Third Fourth Fifth Sixth Output : Type}
    (first : ProbComp First) (second : ProbComp Second)
    (third : ProbComp Third) (fourth : ProbComp Fourth)
    (fifth : ProbComp Fifth) (sixth : ProbComp Sixth)
    (finish : First → Second → Third → Fourth → Fifth → Sixth → ProbComp Output) :
    evalDist (first >>= fun firstValue ↦
      second >>= fun secondValue ↦
      third >>= fun thirdValue ↦
      fourth >>= fun fourthValue ↦
      fifth >>= fun fifthValue ↦
      sixth >>= fun sixthValue ↦
      finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue) =
    evalDist (third >>= fun thirdValue ↦
      fifth >>= fun fifthValue ↦
      first >>= fun firstValue ↦
      fourth >>= fun fourthValue ↦
      sixth >>= fun sixthValue ↦
      second >>= fun secondValue ↦
      finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue) := by
  calc
    _ = evalDist (first >>= fun firstValue ↦
        third >>= fun thirdValue ↦
        second >>= fun secondValue ↦
        fourth >>= fun fourthValue ↦
        fifth >>= fun fifthValue ↦
        sixth >>= fun sixthValue ↦
        finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue) := by
      refine evalDist_bind_congr' first fun firstValue ↦ ?_
      exact evalDist_bind_bind_swap second third
        (fun secondValue thirdValue ↦
          fourth >>= fun fourthValue ↦
          fifth >>= fun fifthValue ↦
          sixth >>= fun sixthValue ↦
          finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue)
    _ = evalDist (third >>= fun thirdValue ↦
        first >>= fun firstValue ↦
        second >>= fun secondValue ↦
        fourth >>= fun fourthValue ↦
        fifth >>= fun fifthValue ↦
        sixth >>= fun sixthValue ↦
        finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue) :=
      evalDist_bind_bind_swap first third
        (fun firstValue thirdValue ↦
          second >>= fun secondValue ↦
          fourth >>= fun fourthValue ↦
          fifth >>= fun fifthValue ↦
          sixth >>= fun sixthValue ↦
          finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue)
    _ = evalDist (third >>= fun thirdValue ↦
        first >>= fun firstValue ↦
        second >>= fun secondValue ↦
        fifth >>= fun fifthValue ↦
        fourth >>= fun fourthValue ↦
        sixth >>= fun sixthValue ↦
        finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue) := by
      refine evalDist_bind_congr' third fun thirdValue ↦ ?_
      refine evalDist_bind_congr' first fun firstValue ↦ ?_
      refine evalDist_bind_congr' second fun secondValue ↦ ?_
      exact evalDist_bind_bind_swap fourth fifth
        (fun fourthValue fifthValue ↦
          sixth >>= fun sixthValue ↦
          finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue)
    _ = evalDist (third >>= fun thirdValue ↦
        first >>= fun firstValue ↦
        fifth >>= fun fifthValue ↦
        second >>= fun secondValue ↦
        fourth >>= fun fourthValue ↦
        sixth >>= fun sixthValue ↦
        finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue) := by
      refine evalDist_bind_congr' third fun thirdValue ↦ ?_
      refine evalDist_bind_congr' first fun firstValue ↦ ?_
      exact evalDist_bind_bind_swap second fifth
        (fun secondValue fifthValue ↦
          fourth >>= fun fourthValue ↦
          sixth >>= fun sixthValue ↦
          finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue)
    _ = evalDist (third >>= fun thirdValue ↦
        fifth >>= fun fifthValue ↦
        first >>= fun firstValue ↦
        second >>= fun secondValue ↦
        fourth >>= fun fourthValue ↦
        sixth >>= fun sixthValue ↦
        finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue) := by
      refine evalDist_bind_congr' third fun thirdValue ↦ ?_
      exact evalDist_bind_bind_swap first fifth
        (fun firstValue fifthValue ↦
          second >>= fun secondValue ↦
          fourth >>= fun fourthValue ↦
          sixth >>= fun sixthValue ↦
          finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue)
    _ = evalDist (third >>= fun thirdValue ↦
        fifth >>= fun fifthValue ↦
        first >>= fun firstValue ↦
        fourth >>= fun fourthValue ↦
        second >>= fun secondValue ↦
        sixth >>= fun sixthValue ↦
        finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue) := by
      refine evalDist_bind_congr' third fun thirdValue ↦ ?_
      refine evalDist_bind_congr' fifth fun fifthValue ↦ ?_
      refine evalDist_bind_congr' first fun firstValue ↦ ?_
      exact evalDist_bind_bind_swap second fourth
        (fun secondValue fourthValue ↦
          sixth >>= fun sixthValue ↦
          finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue)
    _ = _ := by
      refine evalDist_bind_congr' third fun thirdValue ↦ ?_
      refine evalDist_bind_congr' fifth fun fifthValue ↦ ?_
      refine evalDist_bind_congr' first fun firstValue ↦ ?_
      refine evalDist_bind_congr' fourth fun fourthValue ↦ ?_
      exact evalDist_bind_bind_swap second sixth
        (fun secondValue sixthValue ↦
          finish firstValue secondValue thirdValue fourthValue fifthValue sixthValue)

section Native

variable {Message : Type}
  {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]

/-- Number of direct TLWE rows in the native key-switch table. -/
abbrev keySwitchSamples (ringRank degree keySwitchLevels : ℕ) :=
  (ringRank * degree) * keySwitchLevels

/-- The shared-secret, two-noise binary-LWE problem containing the zero-message key-switch table
and one fresh encryption row. -/
def jointLweProblem
    (q lweDimension keySwitchSamples : ℕ) [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)) :=
  FormalProof4FHE.LWE.TwoBlock.heterogeneousProblem
    lweDimension keySwitchSamples 1
    (Native.sampleLweSecret lweDimension) embedBinarySecret
    keySwitchErrorSampler inputErrorSampler

/-- Interpret a one-row batch transcript as a scalar TLWE ciphertext and add an encoded message
to its body. -/
def challengeCiphertext
    (encode : Message → ZMod q) (message : Message)
    (transcript : FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1) :
    ScalarCiphertext q lweDimension :=
  ⟨fun coordinate ↦ transcript.1 coordinate 0,
    transcript.2 0 + encode message⟩

/-- Inverse of `challengeCiphertext` for a fixed message. -/
def challengeTranscript
    (encode : Message → ZMod q) (message : Message)
    (ciphertext : ScalarCiphertext q lweDimension) :
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1 :=
  (fun coordinate _ ↦ ciphertext.mask coordinate,
    fun _ ↦ ciphertext.body - encode message)

/-- Add a scalar offset to the body of a one-row transcript while retaining its public mask. -/
def shiftInputTranscript
    (offset : ZMod q)
    (transcript : FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1) :
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1 :=
  (transcript.1, fun sample ↦ transcript.2 sample + offset)

/-- Inverse body translation for a one-row transcript. -/
def unshiftInputTranscript
    (offset : ZMod q)
    (transcript : FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1) :
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1 :=
  (transcript.1, fun sample ↦ transcript.2 sample - offset)

omit [NeZero q] in
@[simp]
theorem shiftInputTranscript_unshiftInputTranscript
    (offset : ZMod q)
    (transcript : FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1) :
    shiftInputTranscript offset (unshiftInputTranscript offset transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  apply Prod.ext
  · rfl
  · funext sample
    simp [shiftInputTranscript, unshiftInputTranscript]

omit [NeZero q] in
@[simp]
theorem unshiftInputTranscript_shiftInputTranscript
    (offset : ZMod q)
    (transcript : FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1) :
    unshiftInputTranscript offset (shiftInputTranscript offset transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  apply Prod.ext
  · rfl
  · funext sample
    simp [shiftInputTranscript, unshiftInputTranscript]

omit [NeZero q] in
/-- Body translation is a permutation of one-row public transcripts. -/
theorem shiftInputTranscript_bijective (offset : ZMod q) :
    Function.Bijective
      (shiftInputTranscript (lweDimension := lweDimension) offset) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨unshiftInputTranscript offset, ?_, ?_⟩
  · exact unshiftInputTranscript_shiftInputTranscript offset
  · exact shiftInputTranscript_unshiftInputTranscript offset

/-- Read a one-row transcript as a scalar ciphertext without changing its body. -/
def unshiftedCiphertext
    (transcript : FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1) :
    ScalarCiphertext q lweDimension :=
  ⟨fun coordinate ↦ transcript.1 coordinate 0, transcript.2 0⟩

/-- Extract the only column of a one-column matrix. -/
def singleMask {R : Type} {dimension : ℕ}
    (challenge : Matrix (Fin dimension) (Fin 1) R) : Fin dimension → R :=
  fun coordinate ↦ challenge coordinate 0

/-- Turn a mask vector into a one-column matrix. -/
def singleColumn {R : Type} {dimension : ℕ}
    (mask : Fin dimension → R) : Matrix (Fin dimension) (Fin 1) R :=
  fun coordinate _ ↦ mask coordinate

@[simp]
theorem singleMask_singleColumn {R : Type} {dimension : ℕ}
    (mask : Fin dimension → R) : singleMask (singleColumn mask) = mask := by
  rfl

@[simp]
theorem singleColumn_singleMask {R : Type} {dimension : ℕ}
    (challenge : Matrix (Fin dimension) (Fin 1) R) :
    singleColumn (singleMask challenge) = challenge := by
  funext coordinate sample
  have hsample : sample = (0 : Fin 1) := Fin.eq_zero sample
  subst hsample
  rfl

/-- One-column matrices and scalar mask vectors are in bijection. -/
theorem singleMask_bijective {R : Type} {dimension : ℕ} :
    Function.Bijective
      (singleMask : Matrix (Fin dimension) (Fin 1) R → Fin dimension → R) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨singleColumn, ?_, ?_⟩
  · exact singleColumn_singleMask
  · exact singleMask_singleColumn

/-- Read the sole coordinate of a singleton vector. -/
def headOutput {R : Type} (output : Fin 1 → R) : R := output 0

/-- Place a scalar in the singleton vector space. -/
def singletonOutput {R : Type} (value : R) : Fin 1 → R := fun _ ↦ value

@[simp]
theorem headOutput_singletonOutput {R : Type} (value : R) :
    headOutput (singletonOutput value) = value := by
  rfl

@[simp]
theorem singletonOutput_headOutput {R : Type} (output : Fin 1 → R) :
    singletonOutput (headOutput output) = output := by
  funext sample
  have hsample : sample = (0 : Fin 1) := Fin.eq_zero sample
  subst hsample
  rfl

/-- Singleton vectors and scalars are in bijection. -/
theorem headOutput_bijective {R : Type} :
    Function.Bijective (headOutput : (Fin 1 → R) → R) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨singletonOutput, ?_, ?_⟩
  · exact singletonOutput_headOutput
  · exact headOutput_singletonOutput

/-- Sampling one IID coordinate and reading it is exactly one draw from the scalar sampler. -/
theorem headOutput_sampleIID_one_evalDist {R : Type} [Finite R]
    (sampler : ProbComp R) :
    𝒟[headOutput <$> ProbComp.sampleIID 1 sampler] = 𝒟[sampler] := by
  refine evalDist_ext fun value ↦ ?_
  calc
    Pr[= value | headOutput <$> ProbComp.sampleIID 1 sampler] =
        Pr[= singletonOutput value | ProbComp.sampleIID 1 sampler] := by
      simpa using
        (probOutput_map_injective (ProbComp.sampleIID 1 sampler)
          headOutput_bijective.injective (singletonOutput value))
    _ = ∏ sample : Fin 1,
          Pr[= singletonOutput value sample | sampler] :=
      FormalProof4FHE.SharedRandomness.probOutput_sampleIID
        1 sampler (singletonOutput value)
    _ = Pr[= value | sampler] := by simp [singletonOutput]

/-- Mapping a one-column uniform matrix to its sole mask column gives the uniform mask sampler. -/
theorem singleMask_uniform_evalDist {R : Type} [Finite R] [SampleableType R]
    (dimension : ℕ) :
    𝒟[singleMask <$> ($ᵗ Matrix (Fin dimension) (Fin 1) R)] =
      𝒟[$ᵗ (Fin dimension → R)] :=
  evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin dimension) (Fin 1) R)
    (β := Fin dimension → R) singleMask singleMask_bijective

/-- A one-column uniform matrix with one IID error coordinate is distributionally identical,
after reading its sole entries, to the native scalar TLWE mask-and-error sampler. -/
theorem inputMaterial_evalDist {R : Type} [Finite R] [SampleableType R]
    (dimension : ℕ) (errorSampler : ProbComp R) :
    𝒟[($ᵗ Matrix (Fin dimension) (Fin 1) R) >>= fun challenge ↦
        ProbComp.sampleIID 1 errorSampler >>= fun error ↦
        pure (singleMask challenge, headOutput error)] =
      𝒟[($ᵗ (Fin dimension → R)) >>= fun mask ↦
        errorSampler >>= fun error ↦ pure (mask, error)] := by
  let mappedChallenge : ProbComp (Fin dimension → R) :=
    singleMask <$> ($ᵗ Matrix (Fin dimension) (Fin 1) R)
  let mappedError : ProbComp R :=
    headOutput <$> ProbComp.sampleIID 1 errorSampler
  have hChallenge : 𝒟[mappedChallenge] = 𝒟[$ᵗ (Fin dimension → R)] := by
    simpa only [mappedChallenge] using
      (singleMask_uniform_evalDist (R := R) dimension)
  have hError : 𝒟[mappedError] = 𝒟[errorSampler] := by
    simpa only [mappedError] using headOutput_sampleIID_one_evalDist errorSampler
  have left_eq :
      (($ᵗ Matrix (Fin dimension) (Fin 1) R) >>= fun challenge ↦
        ProbComp.sampleIID 1 errorSampler >>= fun error ↦
        pure (singleMask challenge, headOutput error)) =
      (mappedChallenge >>= fun mask ↦
        mappedError >>= fun error ↦ pure (mask, error)) := by
    simp [mappedChallenge, mappedError, bind_assoc, monad_norm]
  rw [left_eq]
  calc
    _ = 𝒟[($ᵗ (Fin dimension → R)) >>= fun mask ↦
        mappedError >>= fun error ↦ pure (mask, error)] :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hChallenge _
    _ = _ := by
      refine evalDist_bind_congr' ($ᵗ (Fin dimension → R)) fun mask ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hError _

omit [NeZero q] in
/-- Adding a message during scalar conversion is the same as first translating the transcript
body. -/
theorem challengeCiphertext_eq_unshifted_shift
    (encode : Message → ZMod q) (message : Message)
    (transcript : FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1) :
    challengeCiphertext encode message transcript =
      unshiftedCiphertext (shiftInputTranscript (encode message) transcript) := by
  rfl

omit [NeZero q] in
@[simp]
theorem challengeCiphertext_challengeTranscript
    (encode : Message → ZMod q) (message : Message)
    (ciphertext : ScalarCiphertext q lweDimension) :
    challengeCiphertext encode message (challengeTranscript encode message ciphertext) =
      ciphertext := by
  rcases ciphertext with ⟨mask, body⟩
  simp [challengeCiphertext, challengeTranscript]

omit [NeZero q] in
@[simp]
theorem challengeTranscript_challengeCiphertext
    (encode : Message → ZMod q) (message : Message)
    (transcript : FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1) :
    challengeTranscript encode message (challengeCiphertext encode message transcript) =
      transcript := by
  rcases transcript with ⟨challenge, output⟩
  apply Prod.ext
  · funext coordinate sample
    have hsample : sample = (0 : Fin 1) := Fin.eq_zero sample
    subst hsample
    rfl
  · funext sample
    have hsample : sample = (0 : Fin 1) := Fin.eq_zero sample
    subst hsample
    simp [challengeCiphertext, challengeTranscript]

omit [NeZero q] in
/-- For every fixed encoded message, converting and shifting a one-row transcript is a
bijection onto scalar TLWE ciphertexts. -/
theorem challengeCiphertext_bijective
    (encode : Message → ZMod q) (message : Message) :
    Function.Bijective
      (challengeCiphertext (lweDimension := lweDimension) encode message) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨challengeTranscript encode message, ?_, ?_⟩
  · exact challengeTranscript_challengeCiphertext encode message
  · exact challengeCiphertext_challengeTranscript encode message

omit [NeZero q] in
/-- On a real zero-message LWE row, `challengeCiphertext` is exactly scalar TLWE assembly with
the selected message and input error. -/
theorem challengeCiphertext_real
    (encode : Message → ZMod q) (message : Message)
    (secret : Fin lweDimension → ZMod q)
    (challenge : Matrix (Fin lweDimension) (Fin 1) (ZMod q))
    (error : Fin 1 → ZMod q) :
    challengeCiphertext encode message
        (challenge, vecMul secret challenge + error) =
      TLWE.assemble secret (fun coordinate ↦ challenge coordinate 0)
        (encode message) (error 0) := by
  have hbody :
      vecMul secret challenge 0 + error 0 + encode message =
        dotProduct secret (fun coordinate ↦ challenge coordinate 0) +
          encode message + error 0 := by
    change dotProduct secret (fun coordinate ↦ challenge coordinate 0) +
        error 0 + encode message =
      dotProduct secret (fun coordinate ↦ challenge coordinate 0) +
        encode message + error 0
    abel
  exact congrArg
    (fun body ↦ (⟨fun coordinate ↦ challenge coordinate 0, body⟩ :
      ScalarCiphertext q lweDimension)) hbody

/-- Extract the key-switch transcript from an unequal two-block public transcript. -/
def keySwitchTranscript {samples : ℕ}
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript
      (ZMod q) lweDimension samples 1) :
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension samples :=
  (FormalProof4FHE.LWE.TwoBlock.toTranscriptPair transcript).1

/-- Extract the single encryption row from an unequal two-block public transcript. -/
def inputTranscript {samples : ℕ}
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript
      (ZMod q) lweDimension samples 1) :
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1 :=
  (FormalProof4FHE.LWE.TwoBlock.toTranscriptPair transcript).2

/-- Translate only the first output block of an unequal two-block transcript. -/
def shiftFirstBlock {R : Type} [Add R]
    {dimension firstSamples secondSamples : ℕ}
    (message : Fin firstSamples → R)
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript
      R dimension firstSamples secondSamples) :
    FormalProof4FHE.LWE.TwoBlock.Transcript R dimension firstSamples secondSamples :=
  (transcript.1, (transcript.2.1 + message, transcript.2.2))

/-- Inverse translation of the first output block. -/
def unshiftFirstBlock {R : Type} [Sub R]
    {dimension firstSamples secondSamples : ℕ}
    (message : Fin firstSamples → R)
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript
      R dimension firstSamples secondSamples) :
    FormalProof4FHE.LWE.TwoBlock.Transcript R dimension firstSamples secondSamples :=
  (transcript.1, (transcript.2.1 - message, transcript.2.2))

@[simp]
theorem shiftFirstBlock_unshiftFirstBlock {R : Type} [AddGroup R]
    {dimension firstSamples secondSamples : ℕ}
    (message : Fin firstSamples → R)
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript
      R dimension firstSamples secondSamples) :
    shiftFirstBlock message (unshiftFirstBlock message transcript) = transcript := by
  rcases transcript with ⟨challenge, firstOutput, secondOutput⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext sample
      simp [shiftFirstBlock, unshiftFirstBlock]
    · rfl

@[simp]
theorem unshiftFirstBlock_shiftFirstBlock {R : Type} [AddGroup R]
    {dimension firstSamples secondSamples : ℕ}
    (message : Fin firstSamples → R)
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript
      R dimension firstSamples secondSamples) :
    unshiftFirstBlock message (shiftFirstBlock message transcript) = transcript := by
  rcases transcript with ⟨challenge, firstOutput, secondOutput⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext sample
      simp [shiftFirstBlock, unshiftFirstBlock]
    · rfl

/-- First-block translation is a permutation of unequal two-block transcripts. -/
theorem shiftFirstBlock_bijective {R : Type} [AddGroup R]
    {dimension firstSamples secondSamples : ℕ}
    (message : Fin firstSamples → R) :
    Function.Bijective
      (shiftFirstBlock (dimension := dimension) (secondSamples := secondSamples) message) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨unshiftFirstBlock message, ?_, ?_⟩
  · exact unshiftFirstBlock_shiftFirstBlock message
  · exact shiftFirstBlock_unshiftFirstBlock message

omit [NeZero q] in
@[simp]
theorem inputTranscript_shiftFirstBlock
    {firstSamples : ℕ}
    (message : Fin firstSamples → ZMod q)
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript
      (ZMod q) lweDimension firstSamples 1) :
    inputTranscript (shiftFirstBlock message transcript) = inputTranscript transcript := by
  rfl

omit [NeZero q] in
/-- Translating the first real zero-message block yields the standard fixed-message TLWE batch
assembly. -/
theorem keySwitchTranscript_shiftFirstBlock_real
    {firstSamples : ℕ}
    (message : Fin firstSamples → ZMod q)
    (secret : Fin lweDimension → ZMod q)
    (firstChallenge : Matrix (Fin lweDimension) (Fin firstSamples) (ZMod q))
    (secondChallenge : Matrix (Fin lweDimension) (Fin 1) (ZMod q))
    (firstError : Fin firstSamples → ZMod q)
    (secondError : Fin 1 → ZMod q) :
    keySwitchTranscript
        (shiftFirstBlock message
          ((firstChallenge, secondChallenge),
            (vecMul secret firstChallenge + firstError,
              vecMul secret secondChallenge + secondError))) =
      TLWE.batchAssemble secret firstChallenge message firstError := by
  apply Prod.ext
  · rfl
  · funext sample
    simp only [keySwitchTranscript, shiftFirstBlock,
      FormalProof4FHE.LWE.TwoBlock.toTranscriptPair,
      TLWE.batchAssemble, Pi.add_apply]
    abel

omit [NeZero q] in
/-- The second real block, read through `inputTranscript`, gives the expected assembled scalar
TLWE challenge after adding the selected encoded message. -/
theorem challengeCiphertext_inputTranscript_real
    {firstSamples : ℕ}
    (encode : Message → ZMod q) (selected : Message)
    (secret : Fin lweDimension → ZMod q)
    (firstChallenge : Matrix (Fin lweDimension) (Fin firstSamples) (ZMod q))
    (secondChallenge : Matrix (Fin lweDimension) (Fin 1) (ZMod q))
    (firstError : Fin firstSamples → ZMod q)
    (secondError : Fin 1 → ZMod q) :
    challengeCiphertext encode selected
        (inputTranscript
          ((firstChallenge, secondChallenge),
            (vecMul secret firstChallenge + firstError,
              vecMul secret secondChallenge + secondError))) =
      TLWE.assemble secret (singleMask secondChallenge)
        (encode selected) (secondError 0) := by
  change challengeCiphertext encode selected
      (secondChallenge, vecMul secret secondChallenge + secondError) =
    TLWE.assemble secret (fun coordinate ↦ secondChallenge coordinate 0)
      (encode selected) (secondError 0)
  exact challengeCiphertext_real encode selected secret secondChallenge secondError

/-- Run the adaptive one-time challenge from an already supplied zero/shifted two-block public
transcript and bootstrapping key. -/
def transcriptGame
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (bootstrapKey : Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
    (transcript : FormalProof4FHE.LWE.TwoBlock.Transcript (ZMod q) lweDimension
      (keySwitchSamples ringRank degree keySwitchLevels) 1) : ProbComp Bool := do
  let bit ← $ᵗ Bool
  let (message₀, message₁, state) ← adversary.chooseMessages
    ⟨bootstrapKey, keySwitchTranscript transcript⟩
  let ciphertext := challengeCiphertext encode
    (if bit then message₀ else message₁) (inputTranscript transcript)
  let guess ← adversary.distinguish state ciphertext
  return (bit == guess)

/-- A context-dependent translation of the first block of an independently uniform unequal
transcript preserves the complete downstream distribution. -/
theorem uniformTranscript_context_shiftFirst_evalDist
    {R Context Output : Type} [AddGroup R] [Finite R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (contextSampler : ProbComp Context)
    (message : Context → Fin firstSamples → R)
    (finish : Context →
      FormalProof4FHE.LWE.TwoBlock.Transcript
        R dimension firstSamples secondSamples → ProbComp Output) :
    evalDist (($ᵗ (FormalProof4FHE.LWE.TwoBlock.Transcript
        R dimension firstSamples secondSamples)) >>= fun transcript ↦
      contextSampler >>= fun context ↦
      finish context (shiftFirstBlock (message context) transcript)) =
    evalDist (($ᵗ (FormalProof4FHE.LWE.TwoBlock.Transcript
        R dimension firstSamples secondSamples)) >>= fun transcript ↦
      contextSampler >>= fun context ↦ finish context transcript) := by
  calc
    _ = evalDist (contextSampler >>= fun context ↦
        ($ᵗ (FormalProof4FHE.LWE.TwoBlock.Transcript
          R dimension firstSamples secondSamples)) >>= fun transcript ↦
        finish context (shiftFirstBlock (message context) transcript)) :=
      evalDist_bind_bind_swap
        ($ᵗ (FormalProof4FHE.LWE.TwoBlock.Transcript
          R dimension firstSamples secondSamples)) contextSampler
        (fun transcript context ↦
          finish context (shiftFirstBlock (message context) transcript))
    _ = evalDist (contextSampler >>= fun context ↦
        ($ᵗ (FormalProof4FHE.LWE.TwoBlock.Transcript
          R dimension firstSamples secondSamples)) >>= fun transcript ↦
        finish context transcript) := by
      refine evalDist_bind_congr' contextSampler fun context ↦ ?_
      rw [show (($ᵗ (FormalProof4FHE.LWE.TwoBlock.Transcript
          R dimension firstSamples secondSamples)) >>= fun transcript ↦
          finish context (shiftFirstBlock (message context) transcript)) =
        ((shiftFirstBlock (dimension := dimension) (secondSamples := secondSamples)
            (message context) <$>
          ($ᵗ (FormalProof4FHE.LWE.TwoBlock.Transcript
            R dimension firstSamples secondSamples))) >>= finish context) by
          simp [monad_norm],
        evalDist_bind,
        evalDist_map_bijective_uniform_cross
          (α := FormalProof4FHE.LWE.TwoBlock.Transcript
            R dimension firstSamples secondSamples)
          (β := FormalProof4FHE.LWE.TwoBlock.Transcript
            R dimension firstSamples secondSamples)
          (shiftFirstBlock (dimension := dimension) (secondSamples := secondSamples)
            (message context))
          (shiftFirstBlock_bijective (dimension := dimension)
            (secondSamples := secondSamples) (message context)),
        ← evalDist_bind]
    _ = _ :=
      (evalDist_bind_bind_swap
        ($ᵗ (FormalProof4FHE.LWE.TwoBlock.Transcript
          R dimension firstSamples secondSamples)) contextSampler
        (fun transcript context ↦ finish context transcript)).symm

/-- Binary-LWE distinguisher for the native all-zero-cloud adaptive encryption game.  The
independently sampled context contains the ring key and its zero-message bootstrapping key; the
LWE transcript supplies both scalar-key-dependent public blocks. -/
noncomputable def zeroCloudReduction
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    LearningWithErrors.Adversary
      (jointLweProblem q lweDimension
        (keySwitchSamples ringRank degree keySwitchLevels)
        keySwitchErrorSampler inputErrorSampler) :=
  fun transcript ↦ do
    let context ← Native.KeySwitchSecurity.zeroBootstrapContext
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
    let bit ← $ᵗ Bool
    let (message₀, message₁, state) ← adversary.chooseMessages
      ⟨context.2, keySwitchTranscript transcript⟩
    let ciphertext := challengeCiphertext encode
      (if bit then message₀ else message₁) (inputTranscript transcript)
    let guess ← adversary.distinguish state ciphertext
    return (bit == guess)

/-- Joint-LWE reduction for a context-dependent message vector in the key-switch block. -/
noncomputable def keySwitchMessageReduction
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : RingBinarySecret ringRank degree →
      Fin (keySwitchSamples ringRank degree keySwitchLevels) → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    LearningWithErrors.Adversary
      (jointLweProblem q lweDimension
        (keySwitchSamples ringRank degree keySwitchLevels)
        keySwitchErrorSampler inputErrorSampler) :=
  fun transcript ↦ do
    let context ← Native.KeySwitchSecurity.zeroBootstrapContext
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
    transcriptGame encode adversary context.2
      (shiftFirstBlock (message context.1) transcript)

/-- Native low-level game with a zero-message bootstrapping key and an arbitrary
ring-secret-dependent message vector in the direct-TLWE key-switch table. -/
noncomputable def keySwitchMessageGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : RingBinarySecret ringRank degree →
      Fin (keySwitchSamples ringRank degree keySwitchLevels) → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool := do
  let lweSecret ← Native.sampleLweSecret lweDimension
  let ringSecret ← Native.sampleRingSecret ringRank degree
  let bootstrapKey ← Native.generateZeroBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget ringSecret
  let switchKey ← TLWE.batchEncrypt lweDimension
    (keySwitchSamples ringRank degree keySwitchLevels) keySwitchErrorSampler
    (embedBinarySecret lweSecret) (message ringSecret)
  Encryption.oneTimeContinuation inputErrorSampler encode adversary
    lweSecret ringSecret bootstrapKey switchKey

/-- The concrete real key-switch messages used after bootstrapping-key messages are zero. -/
def nativeKeySwitchMessage
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret ringRank degree) :
    Fin (keySwitchSamples ringRank degree keySwitchLevels) → ZMod q :=
  Native.keySwitchMessages (ringRank * degree) keySwitchLevels keySwitchGadget
    (keyExtract ringSecret)

/-- The native bootstrap-zero endpoint is the arbitrary-message game instantiated with the
actual gadget-scaled extracted ring secret. -/
theorem bootstrapZeroGame_eq_keySwitchMessageGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Encryption.bootstrapZeroGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary =
      keySwitchMessageGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary := by
  simp [Encryption.bootstrapZeroGame, Circular.bootstrapZeroContinuationGame,
    Native.nativeCycleSpec, keySwitchMessageGame, nativeKeySwitchMessage,
    Native.generateKeySwitchKey]

/-- The native zero-cloud endpoint is the arbitrary-message game instantiated with zero. -/
theorem zeroCloudGame_eq_keySwitchMessageGame_zero
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Encryption.zeroCloudGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary =
      keySwitchMessageGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget (fun _ ↦ 0) encode adversary := by
  simp [Encryption.zeroCloudGame, Circular.zeroContinuationGame,
    Native.nativeCycleSpec, keySwitchMessageGame,
    Native.generateZeroKeySwitchKey]

/-- The arbitrary-message native endpoint is exactly the real branch of its translated
two-block LWE reduction. -/
theorem keySwitchMessageGame_evalDist_eq_game0
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : RingBinarySecret ringRank degree →
      Fin (keySwitchSamples ringRank degree keySwitchLevels) → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    𝒟[keySwitchMessageGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget message encode adversary] =
      𝒟[LearningWithErrors.game0
        (jointLweProblem q lweDimension
          (keySwitchSamples ringRank degree keySwitchLevels)
          keySwitchErrorSampler inputErrorSampler)
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget message encode adversary)] := by
  let samples := keySwitchSamples ringRank degree keySwitchLevels
  let FirstChallenge := Matrix (Fin lweDimension) (Fin samples) (ZMod q)
  let SecondChallenge := Matrix (Fin lweDimension) (Fin 1) (ZMod q)
  let FirstError := Fin samples → ZMod q
  let SecondError := Fin 1 → ZMod q
  let scalarSecrets := Native.sampleLweSecret lweDimension
  let contexts := Native.KeySwitchSecurity.zeroBootstrapContext
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
  let firstChallenges : ProbComp FirstChallenge := $ᵗ FirstChallenge
  let secondChallenges : ProbComp SecondChallenge := $ᵗ SecondChallenge
  let firstErrors : ProbComp FirstError :=
    ProbComp.sampleIID samples keySwitchErrorSampler
  let secondErrors : ProbComp SecondError :=
    ProbComp.sampleIID 1 inputErrorSampler
  let nativeInputs : ProbComp ((Fin lweDimension → ZMod q) × ZMod q) := do
    let mask ← $ᵗ (Fin lweDimension → ZMod q)
    let error ← inputErrorSampler
    return (mask, error)
  let batchInputs : ProbComp ((Fin lweDimension → ZMod q) × ZMod q) := do
    let challenge ← secondChallenges
    let error ← secondErrors
    return (singleMask challenge, headOutput error)
  let preGame := fun (lweSecret : BinarySecret lweDimension)
      (context : RingBinarySecret ringRank degree ×
        Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (challenge : FirstChallenge) (error : FirstError) ↦ do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages
      ⟨context.2, TLWE.batchAssemble (embedBinarySecret lweSecret) challenge
        (message context.1) error⟩
    return (bit, messages)
  let final := fun (lweSecret : BinarySecret lweDimension)
      (pre : Bool × (Message × Message × adversary.State))
      (input : (Fin lweDimension → ZMod q) × ZMod q) ↦ do
    let selected := if pre.1 then pre.2.1 else pre.2.2.1
    let ciphertext := TLWE.assemble (embedBinarySecret lweSecret) input.1
      (encode selected) input.2
    let guess ← adversary.distinguish pre.2.2.2 ciphertext
    return (pre.1 == guess)
  let finish := fun (lweSecret : BinarySecret lweDimension)
      (context : RingBinarySecret ringRank degree ×
        Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (challenge : FirstChallenge) (error : FirstError)
      (input : (Fin lweDimension → ZMod q) × ZMod q) ↦
    preGame lweSecret context challenge error >>= fun pre ↦
      final lweSecret pre input
  have native_eq :
      keySwitchMessageGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget message encode adversary =
        (scalarSecrets >>= fun lweSecret ↦
          contexts >>= fun context ↦
          firstChallenges >>= fun challenge ↦
          firstErrors >>= fun error ↦
          preGame lweSecret context challenge error >>= fun pre ↦
          nativeInputs >>= fun input ↦
          final lweSecret pre input) := by
    simp [keySwitchMessageGame, Encryption.oneTimeContinuation,
      TLWE.batchEncrypt, Encryption.encrypt, TLWE.encrypt,
      scalarSecrets, contexts, Native.KeySwitchSecurity.zeroBootstrapContext,
      samples, keySwitchSamples, FirstChallenge, FirstError,
      firstChallenges, firstErrors, nativeInputs, preGame, final,
      bind_assoc, monad_norm]
  have lwe_eq :
      LearningWithErrors.game0
          (jointLweProblem q lweDimension samples
            keySwitchErrorSampler inputErrorSampler)
          (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget message encode adversary) =
        (firstChallenges >>= fun challenge ↦
          secondChallenges >>= fun inputChallenge ↦
          scalarSecrets >>= fun lweSecret ↦
          firstErrors >>= fun error ↦
          secondErrors >>= fun inputError ↦
          contexts >>= fun context ↦
          finish lweSecret context challenge error
            (singleMask inputChallenge, headOutput inputError)) := by
    have uniformChallengeProduct :
        ($ᵗ (FormalProof4FHE.LWE.TwoBlock.Challenge
          (ZMod q) lweDimension samples 1) :
          ProbComp (FormalProof4FHE.LWE.TwoBlock.Challenge
            (ZMod q) lweDimension samples 1)) =
        Prod.mk <$> firstChallenges <*> secondChallenges := rfl
    rw [LearningWithErrors.game0]
    simp only [jointLweProblem]
    unfold LearningWithErrors.distr
    simp only [FormalProof4FHE.LWE.TwoBlock.heterogeneousProblem]
    rw [uniformChallengeProduct]
    simp [keySwitchMessageReduction, transcriptGame,
      keySwitchTranscript_shiftFirstBlock_real, inputTranscript_shiftFirstBlock,
      challengeCiphertext_inputTranscript_real,
      samples, keySwitchSamples, FirstChallenge, SecondChallenge, FirstError, SecondError,
      scalarSecrets, contexts, firstChallenges, secondChallenges,
      firstErrors, secondErrors, finish, preGame, final,
      headOutput,
      bind_assoc, monad_norm]
  rw [native_eq, lwe_eq]
  calc
    _ = 𝒟[scalarSecrets >>= fun lweSecret ↦
        contexts >>= fun context ↦
        firstChallenges >>= fun challenge ↦
        firstErrors >>= fun error ↦
        nativeInputs >>= fun input ↦
        finish lweSecret context challenge error input] := by
      refine evalDist_bind_congr' scalarSecrets fun lweSecret ↦ ?_
      refine evalDist_bind_congr' contexts fun context ↦ ?_
      refine evalDist_bind_congr' firstChallenges fun challenge ↦ ?_
      refine evalDist_bind_congr' firstErrors fun error ↦ ?_
      exact evalDist_bind_bind_swap
        (preGame lweSecret context challenge error) nativeInputs
        (fun pre input ↦ final lweSecret pre input)
    _ = 𝒟[scalarSecrets >>= fun lweSecret ↦
        contexts >>= fun context ↦
        firstChallenges >>= fun challenge ↦
        firstErrors >>= fun error ↦
        batchInputs >>= fun input ↦
        finish lweSecret context challenge error input] := by
      have hInput : 𝒟[batchInputs] = 𝒟[nativeInputs] := by
        simpa only [batchInputs, nativeInputs, secondChallenges, secondErrors] using
          (inputMaterial_evalDist (R := ZMod q) lweDimension inputErrorSampler)
      refine evalDist_bind_congr' scalarSecrets fun lweSecret ↦ ?_
      refine evalDist_bind_congr' contexts fun context ↦ ?_
      refine evalDist_bind_congr' firstChallenges fun challenge ↦ ?_
      refine evalDist_bind_congr' firstErrors fun error ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hInput.symm _
    _ = 𝒟[scalarSecrets >>= fun lweSecret ↦
        contexts >>= fun context ↦
        firstChallenges >>= fun challenge ↦
        firstErrors >>= fun error ↦
        secondChallenges >>= fun inputChallenge ↦
        secondErrors >>= fun inputError ↦
        finish lweSecret context challenge error
          (singleMask inputChallenge, headOutput inputError)] := by
      simp [batchInputs, bind_assoc, monad_norm]
    _ = _ :=
      evalDist_bind_six_reorder scalarSecrets contexts firstChallenges firstErrors
        secondChallenges secondErrors
        (fun lweSecret context challenge error inputChallenge inputError ↦
          finish lweSecret context challenge error
            (singleMask inputChallenge, headOutput inputError))

/-- Every context-dependent key-switch message translation has the same uniform LWE branch as
the unshifted zero-cloud reduction. -/
theorem keySwitchMessageReduction_game1_evalDist_eq_zeroCloud
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (message : RingBinarySecret ringRank degree →
      Fin (keySwitchSamples ringRank degree keySwitchLevels) → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    𝒟[LearningWithErrors.game1
        (jointLweProblem q lweDimension
          (keySwitchSamples ringRank degree keySwitchLevels)
          keySwitchErrorSampler inputErrorSampler)
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget message encode adversary)] =
      𝒟[LearningWithErrors.game1
        (jointLweProblem q lweDimension
          (keySwitchSamples ringRank degree keySwitchLevels)
          keySwitchErrorSampler inputErrorSampler)
        (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget encode adversary)] := by
  let samples := keySwitchSamples ringRank degree keySwitchLevels
  let contexts := Native.KeySwitchSecurity.zeroBootstrapContext
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [jointLweProblem]
  rw [FormalProof4FHE.LWE.TwoBlock.heterogeneousUniformDistr_eq_uniformSample]
  have hShift := uniformTranscript_context_shiftFirst_evalDist
    lweDimension samples 1 contexts (fun context ↦ message context.1)
    (fun context transcript ↦ transcriptGame encode adversary context.2 transcript)
  simpa [samples, contexts, keySwitchMessageReduction,
      zeroCloudReduction, transcriptGame, bind_assoc, monad_norm] using hShift

/-- The native bootstrap-zero adaptive endpoint is the real branch of the translated joint-LWE
reduction with the actual extracted-key gadget messages. -/
theorem bootstrapZeroGame_evalDist_eq_jointLwe_game0
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    𝒟[Encryption.bootstrapZeroGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary] =
      𝒟[LearningWithErrors.game0
        (jointLweProblem q lweDimension
          (keySwitchSamples ringRank degree keySwitchLevels)
          keySwitchErrorSampler inputErrorSampler)
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)] := by
  rw [bootstrapZeroGame_eq_keySwitchMessageGame]
  exact keySwitchMessageGame_evalDist_eq_game0
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
    (nativeKeySwitchMessage keySwitchGadget) encode adversary

/-- Translating the first block by the zero vector gives exactly the unshifted zero-cloud
reduction. -/
theorem keySwitchMessageReduction_zero_eq_zeroCloud
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget (fun _ ↦ 0) encode adversary =
      zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget encode adversary := by
  funext transcript
  simp [keySwitchMessageReduction, zeroCloudReduction, transcriptGame,
    shiftFirstBlock, keySwitchTranscript, inputTranscript,
    FormalProof4FHE.LWE.TwoBlock.toTranscriptPair, monad_norm]

/-- The native zero-cloud adaptive endpoint is the real branch of the unshifted joint-LWE
reduction. -/
theorem zeroCloudGame_evalDist_eq_jointLwe_game0_from_messages
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    𝒟[Encryption.zeroCloudGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary] =
      𝒟[LearningWithErrors.game0
        (jointLweProblem q lweDimension
          (keySwitchSamples ringRank degree keySwitchLevels)
          keySwitchErrorSampler inputErrorSampler)
        (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget encode adversary)] := by
  rw [zeroCloudGame_eq_keySwitchMessageGame_zero,
    ← keySwitchMessageReduction_zero_eq_zeroCloud ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget encode adversary]
  exact keySwitchMessageGame_evalDist_eq_game0
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
    (fun _ ↦ 0) encode adversary

/-- **Contextual native key-switch replacement theorem.**  Even when the adversary chooses its
TLWE challenge messages after seeing the cloud key, replacing the direct key-switch table by its
zero-message version costs at most two shared-secret, two-noise binary-LWE advantages.  Both
reductions include the fresh challenge row in their second block. -/
theorem keySwitchReplacementAdvantage_le_two_jointLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Encryption.keySwitchReplacementAdvantage ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤
      LearningWithErrors.advantage
        (jointLweProblem q lweDimension
          (keySwitchSamples ringRank degree keySwitchLevels)
          keySwitchErrorSampler inputErrorSampler)
        (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary) +
      LearningWithErrors.advantage
        (jointLweProblem q lweDimension
          (keySwitchSamples ringRank degree keySwitchLevels)
          keySwitchErrorSampler inputErrorSampler)
        (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget encode adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold Encryption.keySwitchReplacementAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (bootstrapZeroGame_evalDist_eq_jointLwe_game0 ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary)
      true,
    evalDist_ext_iff.mp
      (zeroCloudGame_evalDist_eq_jointLwe_game0_from_messages ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary)
      true]
  let realProbability : ℝ := (Pr[= true | LearningWithErrors.game0
    (jointLweProblem q lweDimension
      (keySwitchSamples ringRank degree keySwitchLevels)
      keySwitchErrorSampler inputErrorSampler)
    (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)]).toReal
  let uniformRealProbability : ℝ := (Pr[= true | LearningWithErrors.game1
    (jointLweProblem q lweDimension
      (keySwitchSamples ringRank degree keySwitchLevels)
      keySwitchErrorSampler inputErrorSampler)
    (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)]).toReal
  let uniformZeroProbability : ℝ := (Pr[= true | LearningWithErrors.game1
    (jointLweProblem q lweDimension
      (keySwitchSamples ringRank degree keySwitchLevels)
      keySwitchErrorSampler inputErrorSampler)
    (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget encode adversary)]).toReal
  let zeroProbability : ℝ := (Pr[= true | LearningWithErrors.game0
    (jointLweProblem q lweDimension
      (keySwitchSamples ringRank degree keySwitchLevels)
      keySwitchErrorSampler inputErrorSampler)
    (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget encode adversary)]).toReal
  have hUniform : uniformRealProbability = uniformZeroProbability := by
    exact congrArg ENNReal.toReal (evalDist_ext_iff.mp
      (keySwitchMessageReduction_game1_evalDist_eq_zeroCloud
        ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        (nativeKeySwitchMessage keySwitchGadget) encode adversary) true)
  change |realProbability - zeroProbability| ≤
    |realProbability - uniformRealProbability| +
      |zeroProbability - uniformZeroProbability|
  rw [hUniform, abs_sub_comm zeroProbability uniformZeroProbability]
  exact abs_sub_le realProbability uniformZeroProbability zeroProbability

/-- A fair bit agrees with an independent Boolean computation with probability one half. -/
theorem fairBit_eq_independentGuess (guessGame : ProbComp Bool) :
    Pr[= true | do
      let bit ← $ᵗ Bool
      let guess ← guessGame
      return (bit == guess)] = 1 / 2 := by
  calc
    _ = Pr[= true | do
        let guess ← guessGame
        let bit ← $ᵗ Bool
        return (bit == guess)] :=
      probOutput_bind_bind_swap ($ᵗ Bool) guessGame
        (fun bit guess ↦ pure (bit == guess)) true
    _ = Pr[= true | guessGame >>= fun _ ↦ ($ᵗ Bool)] := by
      refine probOutput_bind_congr' guessGame true fun guess ↦ ?_
      cases guess <;> simp
    _ = 1 / 2 := by simp

/-- For a fixed cloud key, a uniform one-row transcript masks the adaptively selected encoded
message.  The resulting ciphertext is independent of the hidden bit, so the winning probability
is exactly one half. -/
theorem uniformChallenge_probOutput_true
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (cloudKey : Encryption.NativeCloudKey q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Pr[= true | do
      let bit ← $ᵗ Bool
      let (message₀, message₁, state) ← adversary.chooseMessages cloudKey
      let transcript ←
        $ᵗ (FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1)
      let ciphertext := challengeCiphertext encode
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
      (transcript : FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1) ↦ do
    let message := if pre.1 then pre.2.1 else pre.2.2.1
    let ciphertext := challengeCiphertext encode message transcript
    let guess ← adversary.distinguish pre.2.2.2 ciphertext
    return (pre.1 == guess)
  let unshiftedCont := fun
      (pre : Bool × (Message × Message × adversary.State))
      (transcript : FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1) ↦ do
    let guess ← adversary.distinguish pre.2.2.2 (unshiftedCiphertext transcript)
    return (pre.1 == guess)
  calc
    _ = Pr[= true | preGame >>= fun pre ↦
          ($ᵗ (FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1)) >>=
            fun transcript ↦ shiftedCont pre transcript] := by
      simp [preGame, shiftedCont, monad_norm]
    _ = Pr[= true | preGame >>= fun pre ↦
          ($ᵗ (FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1)) >>=
            fun transcript ↦ unshiftedCont pre transcript] := by
      refine probOutput_bind_congr' preGame true fun pre ↦ ?_
      let message := if pre.1 then pre.2.1 else pre.2.2.1
      simpa [shiftedCont, unshiftedCont, message,
          challengeCiphertext_eq_unshifted_shift] using
        (probOutput_bind_bijective_uniform_cross
          (FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1)
          (shiftInputTranscript (lweDimension := lweDimension) (encode message))
          (shiftInputTranscript_bijective
            (lweDimension := lweDimension) (encode message))
          (fun transcript ↦ do
            let guess ← adversary.distinguish pre.2.2.2
              (unshiftedCiphertext transcript)
            return (pre.1 == guess)) true)
    _ = Pr[= true | adversary.chooseMessages cloudKey >>= fun messages ↦
          ($ᵗ Bool) >>= fun bit ↦
          ($ᵗ (FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1)) >>=
            fun transcript ↦ unshiftedCont (bit, messages) transcript] := by
      simpa [preGame, unshiftedCont, monad_norm] using
        (probOutput_bind_bind_swap ($ᵗ Bool) (adversary.chooseMessages cloudKey)
          (fun bit messages ↦ do
            let transcript ←
              $ᵗ (FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1)
            unshiftedCont (bit, messages) transcript) true)
    _ = 1 / 2 := by
      rw [probOutput_bind_eq_tsum]
      calc
        _ = ∑' messages, Pr[= messages | adversary.chooseMessages cloudKey] * (1 / 2) := by
          refine tsum_congr fun messages : Message × Message × adversary.State ↦ ?_
          congr 1
          simpa [unshiftedCont, monad_norm] using
            (fairBit_eq_independentGuess
              (do
                let transcript ←
                  $ᵗ (FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1)
                adversary.distinguish messages.2.2 (unshiftedCiphertext transcript)))
        _ = 1 / 2 := by
          rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

/-- The uniform branch of the joint two-block LWE reduction is the information-theoretic
one-time-pad game and succeeds with probability exactly one half. -/
theorem jointLwe_game1_probOutput_true
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Pr[= true | LearningWithErrors.game1
      (jointLweProblem q lweDimension
        (keySwitchSamples ringRank degree keySwitchLevels)
        keySwitchErrorSampler inputErrorSampler)
      (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget encode adversary)] = 1 / 2 := by
  let samples := keySwitchSamples ringRank degree keySwitchLevels
  let FirstTranscript :=
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension samples
  let SecondTranscript :=
    FormalProof4FHE.LWE.BatchTranscript (ZMod q) lweDimension 1
  let firstTranscripts : ProbComp FirstTranscript := $ᵗ FirstTranscript
  let secondTranscripts : ProbComp SecondTranscript := $ᵗ SecondTranscript
  let contexts := Native.KeySwitchSecurity.zeroBootstrapContext
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
  let finish := fun
      (context : RingBinarySecret ringRank degree ×
        Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (first : FirstTranscript) (bit : Bool)
      (messages : Message × Message × adversary.State)
      (second : SecondTranscript) ↦ do
    let ciphertext := challengeCiphertext encode
      (if bit then messages.1 else messages.2.1) second
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
            (ZMod q) lweDimension samples 1)
          (β := FirstTranscript × SecondTranscript)
          FormalProof4FHE.LWE.TwoBlock.toTranscriptPair
          (FormalProof4FHE.LWE.TwoBlock.toTranscriptPair_bijective
            (R := ZMod q) (dimension := lweDimension)
            (firstSamples := samples) (secondSamples := 1))
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
        zeroCloudReduction, keySwitchTranscript, inputTranscript,
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
              rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp [contexts]), one_mul]
        _ = 1 / 2 := by
          rw [ENNReal.tsum_mul_right,
            tsum_probOutput_eq_one' (by simp [firstTranscripts]), one_mul]

/-- The native all-zero-message cloud-key game is exactly the real branch of the joint
two-block binary-LWE reduction. -/
theorem zeroCloudGame_evalDist_eq_jointLwe_game0
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    𝒟[Encryption.zeroCloudGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary] =
      𝒟[LearningWithErrors.game0
        (jointLweProblem q lweDimension
          (keySwitchSamples ringRank degree keySwitchLevels)
          keySwitchErrorSampler inputErrorSampler)
        (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget encode adversary)] := by
  let samples := keySwitchSamples ringRank degree keySwitchLevels
  let FirstChallenge := Matrix (Fin lweDimension) (Fin samples) (ZMod q)
  let SecondChallenge := Matrix (Fin lweDimension) (Fin 1) (ZMod q)
  let FirstError := Fin samples → ZMod q
  let SecondError := Fin 1 → ZMod q
  let scalarSecrets := Native.sampleLweSecret lweDimension
  let contexts := Native.KeySwitchSecurity.zeroBootstrapContext
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
  let firstChallenges : ProbComp FirstChallenge := $ᵗ FirstChallenge
  let secondChallenges : ProbComp SecondChallenge := $ᵗ SecondChallenge
  let firstErrors : ProbComp FirstError :=
    ProbComp.sampleIID samples keySwitchErrorSampler
  let secondErrors : ProbComp SecondError :=
    ProbComp.sampleIID 1 inputErrorSampler
  let nativeInputs : ProbComp ((Fin lweDimension → ZMod q) × ZMod q) := do
    let mask ← $ᵗ (Fin lweDimension → ZMod q)
    let error ← inputErrorSampler
    return (mask, error)
  let batchInputs : ProbComp ((Fin lweDimension → ZMod q) × ZMod q) := do
    let challenge ← secondChallenges
    let error ← secondErrors
    return (singleMask challenge, headOutput error)
  let preGame := fun (lweSecret : BinarySecret lweDimension)
      (context : RingBinarySecret ringRank degree ×
        Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (challenge : FirstChallenge) (error : FirstError) ↦ do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages
      ⟨context.2, (challenge, vecMul (embedBinarySecret lweSecret) challenge + error)⟩
    return (bit, messages)
  let final := fun (lweSecret : BinarySecret lweDimension)
      (pre : Bool × (Message × Message × adversary.State))
      (input : (Fin lweDimension → ZMod q) × ZMod q) ↦ do
    let message := if pre.1 then pre.2.1 else pre.2.2.1
    let ciphertext := TLWE.assemble (embedBinarySecret lweSecret) input.1
      (encode message) input.2
    let guess ← adversary.distinguish pre.2.2.2 ciphertext
    return (pre.1 == guess)
  let finish := fun (lweSecret : BinarySecret lweDimension)
      (context : RingBinarySecret ringRank degree ×
        Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (challenge : FirstChallenge) (error : FirstError)
      (input : (Fin lweDimension → ZMod q) × ZMod q) ↦
    preGame lweSecret context challenge error >>= fun pre ↦
      final lweSecret pre input
  have native_eq :
      Encryption.zeroCloudGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary =
        (scalarSecrets >>= fun lweSecret ↦
          contexts >>= fun context ↦
          firstChallenges >>= fun challenge ↦
          firstErrors >>= fun error ↦
          preGame lweSecret context challenge error >>= fun pre ↦
          nativeInputs >>= fun input ↦
          final lweSecret pre input) := by
    simp [Encryption.zeroCloudGame, Circular.zeroContinuationGame,
      Native.nativeCycleSpec, Encryption.oneTimeContinuation,
      Native.generateZeroKeySwitchKey, TLWE.batchEncrypt,
      Encryption.encrypt, TLWE.encrypt, scalarSecrets, contexts,
      Native.KeySwitchSecurity.zeroBootstrapContext,
      samples, keySwitchSamples, FirstChallenge, FirstError,
      firstChallenges, firstErrors, nativeInputs, preGame, final,
      bind_assoc, monad_norm]
  have lwe_eq :
      LearningWithErrors.game0
          (jointLweProblem q lweDimension samples
            keySwitchErrorSampler inputErrorSampler)
          (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget encode adversary) =
        (firstChallenges >>= fun challenge ↦
          secondChallenges >>= fun inputChallenge ↦
          scalarSecrets >>= fun lweSecret ↦
          firstErrors >>= fun error ↦
          secondErrors >>= fun inputError ↦
          contexts >>= fun context ↦
          finish lweSecret context challenge error
            (singleMask inputChallenge, headOutput inputError)) := by
    have uniformChallengeProduct :
        ($ᵗ (FormalProof4FHE.LWE.TwoBlock.Challenge
          (ZMod q) lweDimension samples 1) :
          ProbComp (FormalProof4FHE.LWE.TwoBlock.Challenge
            (ZMod q) lweDimension samples 1)) =
        Prod.mk <$> firstChallenges <*> secondChallenges := rfl
    rw [LearningWithErrors.game0]
    simp only [jointLweProblem]
    unfold LearningWithErrors.distr
    simp only [FormalProof4FHE.LWE.TwoBlock.heterogeneousProblem]
    rw [uniformChallengeProduct]
    simp [zeroCloudReduction, keySwitchTranscript, inputTranscript,
      FormalProof4FHE.LWE.TwoBlock.toTranscriptPair,
      samples, keySwitchSamples, FirstChallenge, SecondChallenge, FirstError, SecondError,
      scalarSecrets, contexts, firstChallenges, secondChallenges,
      firstErrors, secondErrors, finish, preGame, final,
      challengeCiphertext_real, headOutput,
      bind_assoc, monad_norm]
    rfl
  rw [native_eq, lwe_eq]
  calc
    _ = 𝒟[scalarSecrets >>= fun lweSecret ↦
        contexts >>= fun context ↦
        firstChallenges >>= fun challenge ↦
        firstErrors >>= fun error ↦
        nativeInputs >>= fun input ↦
        finish lweSecret context challenge error input] := by
      refine evalDist_bind_congr' scalarSecrets fun lweSecret ↦ ?_
      refine evalDist_bind_congr' contexts fun context ↦ ?_
      refine evalDist_bind_congr' firstChallenges fun challenge ↦ ?_
      refine evalDist_bind_congr' firstErrors fun error ↦ ?_
      exact evalDist_bind_bind_swap
        (preGame lweSecret context challenge error) nativeInputs
        (fun pre input ↦ final lweSecret pre input)
    _ = 𝒟[scalarSecrets >>= fun lweSecret ↦
        contexts >>= fun context ↦
        firstChallenges >>= fun challenge ↦
        firstErrors >>= fun error ↦
        batchInputs >>= fun input ↦
        finish lweSecret context challenge error input] := by
      have hInput : 𝒟[batchInputs] = 𝒟[nativeInputs] := by
        simpa only [batchInputs, nativeInputs, secondChallenges, secondErrors] using
          (inputMaterial_evalDist (R := ZMod q) lweDimension inputErrorSampler)
      refine evalDist_bind_congr' scalarSecrets fun lweSecret ↦ ?_
      refine evalDist_bind_congr' contexts fun context ↦ ?_
      refine evalDist_bind_congr' firstChallenges fun challenge ↦ ?_
      refine evalDist_bind_congr' firstErrors fun error ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hInput.symm _
    _ = 𝒟[scalarSecrets >>= fun lweSecret ↦
        contexts >>= fun context ↦
        firstChallenges >>= fun challenge ↦
        firstErrors >>= fun error ↦
        secondChallenges >>= fun inputChallenge ↦
        secondErrors >>= fun inputError ↦
        finish lweSecret context challenge error
          (singleMask inputChallenge, headOutput inputError)] := by
      simp [batchInputs, bind_assoc, monad_norm]
    _ = _ :=
      evalDist_bind_six_reorder scalarSecrets contexts firstChallenges firstErrors
        secondChallenges secondErrors
        (fun lweSecret context challenge error inputChallenge inputError ↦
          finish lweSecret context challenge error
            (singleMask inputChallenge, headOutput inputError))

/-- **Zero-cloud TFHE encryption security.**  The absolute signed advantage of the native
all-zero-message cloud-key game is exactly the advantage of the constructed heterogeneous
binary-secret LWE distinguisher. -/
theorem abs_signedAdvantage_zeroCloud_eq_jointLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
      (Encryption.zeroCloudGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| =
      LearningWithErrors.advantage
        (jointLweProblem q lweDimension
          (keySwitchSamples ringRank degree keySwitchLevels)
          keySwitchErrorSampler inputErrorSampler)
        (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget encode adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold Encryption.signedAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (zeroCloudGame_evalDist_eq_jointLwe_game0 ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary)
      true,
    jointLwe_game1_probOutput_true ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget encode adversary]
  norm_num

/-- With equal key-switch and input error samplers, the preceding heterogeneous assumption is
exactly ordinary binary-secret batch LWE with `keySwitchSamples + 1` samples. -/
theorem abs_signedAdvantage_zeroCloud_eq_batchLwe_of_same_noise
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
      (Encryption.zeroCloudGame ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| =
      LearningWithErrors.advantage
        (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
          (keySwitchSamples ringRank degree keySwitchLevels + 1) errorSampler)
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (zeroCloudReduction ringErrorSampler errorSampler errorSampler
            tgswGadget encode adversary)) := by
  rw [abs_signedAdvantage_zeroCloud_eq_jointLwe]
  change LearningWithErrors.advantage
      (FormalProof4FHE.LWE.TwoBlock.problem lweDimension
        (keySwitchSamples ringRank degree keySwitchLevels) 1
        (Native.sampleLweSecret lweDimension) embedBinarySecret errorSampler)
      (zeroCloudReduction ringErrorSampler errorSampler errorSampler
        tgswGadget encode adversary) = _
  simpa [Native.KeySwitchSecurity.binaryLweProblem] using
    (FormalProof4FHE.LWE.TwoBlock.advantage_eq_batch
      lweDimension (keySwitchSamples ringRank degree keySwitchLevels) 1
      (Native.sampleLweSecret lweDimension) embedBinarySecret errorSampler
      (zeroCloudReduction ringErrorSampler errorSampler errorSampler
        tgswGadget encode adversary))

/-- End-to-end native one-time encryption bound with the zero-cloud base term discharged.  The
two remaining protocol-specific terms are the contextual TRGSW bootstrap replacement and the
contextual direct-TLWE key-switch replacement. -/
theorem abs_signedAdvantage_real_le_bootstrap_add_keySwitch_add_jointLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
      (Encryption.realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      Encryption.bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        Encryption.keySwitchReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (jointLweProblem q lweDimension
            (keySwitchSamples ringRank degree keySwitchLevels)
            keySwitchErrorSampler inputErrorSampler)
          (zeroCloudReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget encode adversary) := by
  simpa [abs_signedAdvantage_zeroCloud_eq_jointLwe ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary] using
    (Encryption.abs_signedAdvantage_real_le_bootstrap_add_keySwitch_add_zero
      ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
      encode adversary)

/-- The uniform branch of the actual-message contextual reduction succeeds with probability one
half, because it is distributionally identical to the already-proved zero-cloud uniform branch. -/
theorem nativeKeySwitchReduction_game1_probOutput_true
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Pr[= true | LearningWithErrors.game1
      (jointLweProblem q lweDimension
        (keySwitchSamples ringRank degree keySwitchLevels)
        keySwitchErrorSampler inputErrorSampler)
      (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)] = 1 / 2 := by
  rw [evalDist_ext_iff.mp
      (keySwitchMessageReduction_game1_evalDist_eq_zeroCloud
        ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        (nativeKeySwitchMessage keySwitchGadget) encode adversary) true,
    jointLwe_game1_probOutput_true ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget encode adversary]

/-- The absolute signed advantage of the bootstrap-zero native adaptive game is exactly one
actual-message joint-LWE advantage. -/
theorem abs_signedAdvantage_bootstrapZero_eq_jointLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
      (Encryption.bootstrapZeroGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| =
      LearningWithErrors.advantage
        (jointLweProblem q lweDimension
          (keySwitchSamples ringRank degree keySwitchLevels)
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

/-- **TFHE one-time encryption security up to circular TRGSW.**  The honest native game is
bounded by the contextual bootstrapping-key replacement cost plus one shared-secret, two-noise
binary-LWE advantage containing all key-switch rows and the adaptive challenge row.  Thus the
only non-LWE cryptographic premise left in this encryption theorem is structured TRGSW circular
security. `TFHE.BootstrappingSecurity` identifies this term exactly with direct bilinear cross-key
module-LWE KDM. -/
theorem abs_signedAdvantage_real_le_bootstrap_add_jointLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
      (Encryption.realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      Encryption.bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (jointLweProblem q lweDimension
            (keySwitchSamples ringRank degree keySwitchLevels)
            keySwitchErrorSampler inputErrorSampler)
          (keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary) := by
  rw [← abs_signedAdvantage_bootstrapZero_eq_jointLwe ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary]
  unfold Encryption.signedAdvantage Encryption.bootstrapReplacementAdvantage
    ProbComp.boolDistAdvantage
  exact abs_sub_le
    (Pr[= true | Encryption.realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode adversary]).toReal
    (Pr[= true | Encryption.bootstrapZeroGame ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget encode adversary]).toReal
    (1 / 2 : ℝ)

/-- Equal-noise specialization of the final theorem: the computational term is ordinary
binary-secret batch LWE with exactly `keySwitchSamples + 1` samples. -/
theorem abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_same_noise
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
      (Encryption.realGame ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      Encryption.bootstrapReplacementAdvantage ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (keySwitchSamples ringRank degree keySwitchLevels + 1) errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
              tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)) := by
  have h := abs_signedAdvantage_real_le_bootstrap_add_jointLwe
    ringErrorSampler errorSampler errorSampler tgswGadget keySwitchGadget encode adversary
  have hBatch := FormalProof4FHE.LWE.TwoBlock.advantage_eq_batch
    lweDimension (keySwitchSamples ringRank degree keySwitchLevels) 1
    (Native.sampleLweSecret lweDimension) embedBinarySecret errorSampler
    (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
      tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary)
  change |Encryption.signedAdvantage
      (Encryption.realGame ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
    Encryption.bootstrapReplacementAdvantage ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary +
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.TwoBlock.problem lweDimension
          (keySwitchSamples ringRank degree keySwitchLevels) 1
          (Native.sampleLweSecret lweDimension) embedBinarySecret errorSampler)
        (keySwitchMessageReduction ringErrorSampler errorSampler errorSampler
          tgswGadget (nativeKeySwitchMessage keySwitchGadget) encode adversary) at h
  rw [hBatch] at h
  simpa [Native.KeySwitchSecurity.binaryLweProblem] using h

end Native

end FormalProof4FHE.TFHE.Encryption.Security
