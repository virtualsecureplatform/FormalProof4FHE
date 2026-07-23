/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.SampleRestriction

/-!
# Unequal Two-Block LWE

This file packages two independently sampled blocks of ordinary matrix-LWE samples that share a
single secret.  Unlike the equal-size presentation used by the shared-randomness reduction, the
two blocks may contain different numbers of samples.  This is the shape needed by native TFHE:
the first block contains all direct-TLWE key-switch rows and the second block contains a fresh
encryption challenge.

Splitting an ordinary `firstSamples + secondSamples` transcript is a bijective preprocessing
step.  The real and uniform branches are therefore distributionally identical, and a two-block
distinguisher has exactly the advantage of its ordinary batch-LWE reduction.  The statement is
generic in the secret type and its coefficient embedding, so it applies directly to binary-secret
LWE.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.TwoBlock

/-- Two public matrices with possibly different column counts. -/
abbrev Challenge (R : Type) (dimension firstSamples secondSamples : ℕ) :=
  Matrix (Fin dimension) (Fin firstSamples) R ×
    Matrix (Fin dimension) (Fin secondSamples) R

/-- Two right-hand-side vectors with possibly different lengths. -/
abbrev Output (R : Type) (firstSamples secondSamples : ℕ) :=
  (Fin firstSamples → R) × (Fin secondSamples → R)

/-- The public transcript of the unequal two-block problem. -/
abbrev Transcript (R : Type) (dimension firstSamples secondSamples : ℕ) :=
  Challenge R dimension firstSamples secondSamples × Output R firstSamples secondSamples

/-- Embedded-secret LWE presented as two blocks sharing one secret, with a separate scalar error
sampler for each block.  This is the natural generalized-LWE statement when two protocol objects
use different noise parameters. -/
def heterogeneousProblem {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (firstErrorSampler secondErrorSampler : ProbComp R) :
    LearningWithErrors.Problem
      (Challenge R dimension firstSamples secondSamples) Secret
      (Output R firstSamples secondSamples) where
  sampleChallenge := $ᵗ (Challenge R dimension firstSamples secondSamples)
  sampleSecret := secretSampler
  sampleError := do
    let firstError ← ProbComp.sampleIID firstSamples firstErrorSampler
    let secondError ← ProbComp.sampleIID secondSamples secondErrorSampler
    return (firstError, secondError)
  noiseless := fun secret challenge ↦
    (vecMul (embed secret) challenge.1, vecMul (embed secret) challenge.2)
  sampleUniform := $ᵗ (Output R firstSamples secondSamples)

/-- Same-noise specialization of `heterogeneousProblem`. -/
def problem {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R) :
    LearningWithErrors.Problem
      (Challenge R dimension firstSamples secondSamples) Secret
      (Output R firstSamples secondSamples) :=
  heterogeneousProblem dimension firstSamples secondSamples secretSampler embed
    errorSampler errorSampler

/-- Split an ordinary combined transcript into unequal consecutive blocks. -/
def splitTranscript {R : Type} {dimension firstSamples secondSamples : ℕ}
    (transcript : BatchTranscript R dimension (firstSamples + secondSamples)) :
    Transcript R dimension firstSamples secondSamples :=
  (splitBatchColumns transcript.1, splitBatchOutput transcript.2)

/-- Reassemble an unequal two-block transcript into one ordinary batch. -/
def appendTranscript {R : Type} {dimension firstSamples secondSamples : ℕ}
    (transcript : Transcript R dimension firstSamples secondSamples) :
    BatchTranscript R dimension (firstSamples + secondSamples) :=
  (appendBatchColumns transcript.1, appendBatchOutput transcript.2)

/-- Regroup a two-block transcript into two ordinary public transcripts. -/
def toTranscriptPair {R : Type} {dimension firstSamples secondSamples : ℕ}
    (transcript : Transcript R dimension firstSamples secondSamples) :
    BatchTranscript R dimension firstSamples × BatchTranscript R dimension secondSamples :=
  ((transcript.1.1, transcript.2.1), (transcript.1.2, transcript.2.2))

/-- Regroup two ordinary public transcripts into the challenge/output layout of the two-block
problem. -/
def ofTranscriptPair {R : Type} {dimension firstSamples secondSamples : ℕ}
    (transcripts :
      BatchTranscript R dimension firstSamples × BatchTranscript R dimension secondSamples) :
    Transcript R dimension firstSamples secondSamples :=
  ((transcripts.1.1, transcripts.2.1), (transcripts.1.2, transcripts.2.2))

@[simp]
theorem toTranscriptPair_ofTranscriptPair
    {R : Type} {dimension firstSamples secondSamples : ℕ}
    (transcripts :
      BatchTranscript R dimension firstSamples × BatchTranscript R dimension secondSamples) :
    toTranscriptPair (ofTranscriptPair transcripts) = transcripts := by
  rcases transcripts with ⟨⟨firstChallenge, firstOutput⟩, secondChallenge, secondOutput⟩
  rfl

@[simp]
theorem ofTranscriptPair_toTranscriptPair
    {R : Type} {dimension firstSamples secondSamples : ℕ}
    (transcript : Transcript R dimension firstSamples secondSamples) :
    ofTranscriptPair (toTranscriptPair transcript) = transcript := by
  rcases transcript with ⟨⟨firstChallenge, secondChallenge⟩, firstOutput, secondOutput⟩
  rfl

/-- Regrouping a two-block transcript into its two ordinary blocks is bijective. -/
theorem toTranscriptPair_bijective
    {R : Type} {dimension firstSamples secondSamples : ℕ} :
    Function.Bijective
      (toTranscriptPair : Transcript R dimension firstSamples secondSamples →
        BatchTranscript R dimension firstSamples ×
          BatchTranscript R dimension secondSamples) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨ofTranscriptPair, ?_, ?_⟩
  · exact ofTranscriptPair_toTranscriptPair
  · exact toTranscriptPair_ofTranscriptPair

@[simp]
theorem splitTranscript_appendTranscript
    {R : Type} {dimension firstSamples secondSamples : ℕ}
    (transcript : Transcript R dimension firstSamples secondSamples) :
    splitTranscript (appendTranscript transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  simp [splitTranscript, appendTranscript]

@[simp]
theorem appendTranscript_splitTranscript
    {R : Type} {dimension firstSamples secondSamples : ℕ}
    (transcript : BatchTranscript R dimension (firstSamples + secondSamples)) :
    appendTranscript (splitTranscript transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  simp [splitTranscript, appendTranscript]

/-- Unequal transcript splitting is a bijection. -/
theorem splitTranscript_bijective
    {R : Type} {dimension firstSamples secondSamples : ℕ} :
    Function.Bijective
      (splitTranscript :
        BatchTranscript R dimension (firstSamples + secondSamples) →
          Transcript R dimension firstSamples secondSamples) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨appendTranscript, ?_, ?_⟩
  · exact appendTranscript_splitTranscript
  · exact splitTranscript_appendTranscript

/-- The heterogeneous two-block uniform branch is the canonical uniform transcript sampler. -/
theorem heterogeneousUniformDistr_eq_uniformSample {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (firstErrorSampler secondErrorSampler : ProbComp R) :
    LearningWithErrors.uniformDistr
        (heterogeneousProblem dimension firstSamples secondSamples secretSampler embed
          firstErrorSampler secondErrorSampler) =
      ($ᵗ (Transcript R dimension firstSamples secondSamples)) := by
  unfold LearningWithErrors.uniformDistr heterogeneousProblem
  have uniformProduct :
      ($ᵗ (Transcript R dimension firstSamples secondSamples) :
        ProbComp (Transcript R dimension firstSamples secondSamples)) =
      Prod.mk <$> ($ᵗ (Challenge R dimension firstSamples secondSamples)) <*>
        ($ᵗ (Output R firstSamples secondSamples)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- The same-noise two-block uniform branch is the canonical uniform transcript sampler. -/
theorem uniformDistr_eq_uniformSample {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R) :
    LearningWithErrors.uniformDistr
        (problem dimension firstSamples secondSamples secretSampler embed errorSampler) =
      ($ᵗ (Transcript R dimension firstSamples secondSamples)) := by
  exact heterogeneousUniformDistr_eq_uniformSample dimension firstSamples secondSamples
    secretSampler embed errorSampler errorSampler

/-- The ordinary embedded batch uniform branch is its canonical transcript sampler. -/
theorem batchUniformDistr_eq_uniformSample {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R) (errorSampler : ProbComp R) :
    LearningWithErrors.uniformDistr
        (embeddedBatchProblem dimension samples secretSampler embed errorSampler) =
      ($ᵗ (BatchTranscript R dimension samples)) := by
  unfold LearningWithErrors.uniformDistr embeddedBatchProblem
  have uniformProduct :
      ($ᵗ (BatchTranscript R dimension samples) :
        ProbComp (BatchTranscript R dimension samples)) =
      Prod.mk <$> ($ᵗ Matrix (Fin dimension) (Fin samples) R) <*>
        ($ᵗ (Fin samples → R)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- Splitting maps the ordinary uniform branch exactly to the unequal two-block branch. -/
theorem split_uniform_evalDist {R Secret : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R) :
    𝒟[LearningWithErrors.uniformDistr
          (embeddedBatchProblem dimension (firstSamples + secondSamples)
            secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (splitTranscript transcript)] =
      𝒟[LearningWithErrors.uniformDistr
        (problem dimension firstSamples secondSamples secretSampler embed errorSampler)] := by
  rw [batchUniformDistr_eq_uniformSample, uniformDistr_eq_uniformSample]
  rw [show (do
      let transcript ←
        ($ᵗ (BatchTranscript R dimension (firstSamples + secondSamples)))
      pure (splitTranscript transcript)) =
      splitTranscript <$>
        ($ᵗ (BatchTranscript R dimension (firstSamples + secondSamples))) by
    simp [monad_norm]]
  exact evalDist_map_bijective_uniform_cross
    (α := BatchTranscript R dimension (firstSamples + secondSamples))
    (β := Transcript R dimension firstSamples secondSamples)
    splitTranscript splitTranscript_bijective

/-- Deterministically assemble a real unequal two-block transcript. -/
def realTranscript {R Secret : Type} [Semiring R]
    {dimension firstSamples secondSamples : ℕ}
    (embed : Secret → Fin dimension → R)
    (challenge : Challenge R dimension firstSamples secondSamples)
    (secret : Secret) (errors : Output R firstSamples secondSamples) :
    Transcript R dimension firstSamples secondSamples :=
  (challenge,
    (vecMul (embed secret) challenge.1 + errors.1,
      vecMul (embed secret) challenge.2 + errors.2))

/-- Splitting a real combined transcript splits both its signal and error coordinates. -/
theorem splitTranscript_real {R Secret : Type} [Semiring R]
    {dimension firstSamples secondSamples : ℕ}
    (embed : Secret → Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin (firstSamples + secondSamples)) R)
    (secret : Secret) (error : Fin (firstSamples + secondSamples) → R) :
    splitTranscript (challenge, vecMul (embed secret) challenge + error) =
      realTranscript embed (splitBatchColumns challenge) secret (splitBatchOutput error) := by
  apply Prod.ext
  · rfl
  · simp only [splitTranscript, realTranscript, splitBatchOutput_add,
      splitBatchOutput_vecMul]

/-- Splitting maps the ordinary real branch exactly to the unequal two-block real branch. -/
theorem split_real_evalDist {R Secret : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R) :
    𝒟[LearningWithErrors.distr
          (embeddedBatchProblem dimension (firstSamples + secondSamples)
            secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (splitTranscript transcript)] =
      𝒟[LearningWithErrors.distr
        (problem dimension firstSamples secondSamples secretSampler embed errorSampler)] := by
  let combinedChallenge :
      ProbComp (Matrix (Fin dimension) (Fin (firstSamples + secondSamples)) R) :=
    $ᵗ Matrix (Fin dimension) (Fin (firstSamples + secondSamples)) R
  let mappedChallenge : ProbComp (Challenge R dimension firstSamples secondSamples) :=
    splitBatchColumns <$> combinedChallenge
  let targetChallenge : ProbComp (Challenge R dimension firstSamples secondSamples) :=
    $ᵗ (Challenge R dimension firstSamples secondSamples)
  let combinedErrors : ProbComp (Fin (firstSamples + secondSamples) → R) :=
    ProbComp.sampleIID (firstSamples + secondSamples) errorSampler
  let mappedErrors : ProbComp (Output R firstSamples secondSamples) :=
    splitBatchOutput <$> combinedErrors
  let targetErrors : ProbComp (Output R firstSamples secondSamples) := do
    let firstError ← ProbComp.sampleIID firstSamples errorSampler
    let secondError ← ProbComp.sampleIID secondSamples errorSampler
    return (firstError, secondError)
  have hChallenge : 𝒟[mappedChallenge] = 𝒟[targetChallenge] := by
    exact evalDist_map_bijective_uniform_cross
      (α := Matrix (Fin dimension) (Fin (firstSamples + secondSamples)) R)
      (β := Challenge R dimension firstSamples secondSamples)
      splitBatchColumns splitBatchColumns_bijective
  have hErrors : 𝒟[mappedErrors] = 𝒟[targetErrors] := by
    simpa only [mappedErrors, combinedErrors, targetErrors] using
      (splitBatchOutput_sampleIID_evalDist firstSamples secondSamples errorSampler)
  have left_eq :
      (LearningWithErrors.distr
          (embeddedBatchProblem dimension (firstSamples + secondSamples)
            secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (splitTranscript transcript)) =
      (mappedChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        mappedErrors >>= fun errors ↦
        pure (realTranscript embed challenge secret errors)) := by
    simp [LearningWithErrors.distr, embeddedBatchProblem,
      mappedChallenge, combinedChallenge, mappedErrors, combinedErrors,
      splitTranscript_real, bind_assoc, monad_norm]
  have right_eq :
      LearningWithErrors.distr
          (problem dimension firstSamples secondSamples secretSampler embed errorSampler) =
      (targetChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        targetErrors >>= fun errors ↦
        pure (realTranscript embed challenge secret errors)) := by
    simp [LearningWithErrors.distr, problem, heterogeneousProblem, targetChallenge, targetErrors,
      realTranscript, monad_norm]
  rw [left_eq, right_eq]
  calc
    _ = 𝒟[targetChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        mappedErrors >>= fun errors ↦
        pure (realTranscript embed challenge secret errors)] :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hChallenge _
    _ = _ := by
      refine evalDist_bind_congr' targetChallenge fun challenge ↦ ?_
      refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hErrors _

/-- Preprocess one ordinary combined transcript for an unequal two-block distinguisher. -/
def reduction {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    {dimension firstSamples secondSamples : ℕ}
    {secretSampler : ProbComp Secret} {embed : Secret → Fin dimension → R}
    {errorSampler : ProbComp R}
    (adversary : LearningWithErrors.Adversary
      (problem dimension firstSamples secondSamples secretSampler embed errorSampler)) :
    LearningWithErrors.Adversary
      (embeddedBatchProblem dimension (firstSamples + secondSamples)
        secretSampler embed errorSampler) :=
  fun transcript ↦ adversary (splitTranscript transcript)

/-- Exact real-game equality for unequal-block preprocessing. -/
theorem game0_evalDist_eq {R Secret : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem dimension firstSamples secondSamples secretSampler embed errorSampler)) :
    𝒟[LearningWithErrors.game0
        (problem dimension firstSamples secondSamples secretSampler embed errorSampler)
        adversary] =
      𝒟[LearningWithErrors.game0
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed errorSampler)
        (reduction adversary)] := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  simp only [reduction]
  rw [show (LearningWithErrors.distr
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed errorSampler) >>=
      fun transcript ↦ adversary (splitTranscript transcript)) =
    ((LearningWithErrors.distr
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed errorSampler) >>=
      fun transcript ↦ pure (splitTranscript transcript)) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    split_real_evalDist dimension firstSamples secondSamples secretSampler embed errorSampler]

/-- Exact uniform-game equality for unequal-block preprocessing. -/
theorem game1_evalDist_eq {R Secret : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem dimension firstSamples secondSamples secretSampler embed errorSampler)) :
    𝒟[LearningWithErrors.game1
        (problem dimension firstSamples secondSamples secretSampler embed errorSampler)
        adversary] =
      𝒟[LearningWithErrors.game1
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed errorSampler)
        (reduction adversary)] := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [reduction]
  rw [show (LearningWithErrors.uniformDistr
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed errorSampler) >>=
      fun transcript ↦ adversary (splitTranscript transcript)) =
    ((LearningWithErrors.uniformDistr
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed errorSampler) >>=
      fun transcript ↦ pure (splitTranscript transcript)) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    split_uniform_evalDist dimension firstSamples secondSamples secretSampler embed errorSampler]

/-- **Exact unequal-block reduction.**  A distinguisher for two independent blocks sharing one
secret has exactly the advantage of its preprocessing reduction against ordinary batch LWE with
the sum of the two sample counts. -/
theorem advantage_eq_batch {R Secret : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem dimension firstSamples secondSamples secretSampler embed errorSampler)) :
    LearningWithErrors.advantage
        (problem dimension firstSamples secondSamples secretSampler embed errorSampler)
        adversary =
      LearningWithErrors.advantage
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed errorSampler)
        (reduction adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (game0_evalDist_eq dimension firstSamples secondSamples secretSampler embed
        errorSampler adversary) true,
    evalDist_ext_iff.mp
      (game1_evalDist_eq dimension firstSamples secondSamples secretSampler embed
        errorSampler adversary) true]

end FormalProof4FHE.LWE.TwoBlock
