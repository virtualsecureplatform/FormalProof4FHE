/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.TwoBlock
import FormalProof4FHE.Probability.FiniteProduct

/-!
# Parallel Batches Sharing One LWE Secret

This file proves that a finite family of equal-size matrix-LWE batches sharing one secret is only
a reshaping of one conventional combined batch.  Challenges, errors, outputs, and complete
transcripts are flattened through `finProdFinEquiv`; both real and uniform game distributions are
preserved exactly, so the distinguishing advantages are equal with no hybrid loss.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.ParallelBatch

/-- Eta-expanded pointwise addition contracts to function-space addition. -/
theorem pointwiseAdd_eq_add {Index Value : Type} [Add Value]
    (left right : Index → Value) :
    (fun index ↦ left index + right index) = left + right := by
  rfl

/-- A family of `blocks` public matrices, each carrying `samples` columns. -/
abbrev Challenge (R : Type) (dimension blocks samples : ℕ) :=
  Fin blocks → Matrix (Fin dimension) (Fin samples) R

/-- A family of `blocks` output vectors. -/
abbrev Output (R : Type) (blocks samples : ℕ) :=
  Fin blocks → Fin samples → R

/-- The corresponding parallel transcript. -/
abbrev Transcript (R : Type) (dimension blocks samples : ℕ) :=
  Challenge R dimension blocks samples × Output R blocks samples

/-- Split the columns of one combined matrix into equal-size blocks. -/
def challengeEquiv (R : Type) (dimension blocks samples : ℕ) :
    Matrix (Fin dimension) (Fin (blocks * samples)) R ≃
      Challenge R dimension blocks samples where
  toFun challenge := fun block row sample ↦
    challenge row (finProdFinEquiv (block, sample))
  invFun challenge := fun row index ↦
    let pair := finProdFinEquiv.symm index
    challenge pair.1 row pair.2
  left_inv challenge := by
    funext row index
    change challenge row (finProdFinEquiv (finProdFinEquiv.symm index)) =
      challenge row index
    rw [Equiv.apply_symm_apply]
  right_inv challenge := by
    funext block row sample
    simp

/-- Split one combined output vector into equal-size blocks. -/
def outputEquiv (R : Type) (blocks samples : ℕ) :
    (Fin (blocks * samples) → R) ≃ Output R blocks samples where
  toFun output := fun block sample ↦ output (finProdFinEquiv (block, sample))
  invFun output := fun index ↦
    let pair := finProdFinEquiv.symm index
    output pair.1 pair.2
  left_inv output := by
    funext index
    change output (finProdFinEquiv (finProdFinEquiv.symm index)) = output index
    rw [Equiv.apply_symm_apply]
  right_inv output := by
    funext block sample
    simp

/-- Split both components of one combined batch transcript. -/
def transcriptEquiv (R : Type) (dimension blocks samples : ℕ) :
    BatchTranscript R dimension (blocks * samples) ≃
      Transcript R dimension blocks samples :=
  (challengeEquiv R dimension blocks samples).prodCongr
    (outputEquiv R blocks samples)

/-- Embedded-secret LWE presented as equal-size parallel batches sharing one secret. -/
noncomputable def problem {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (dimension blocks samples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R) :
    LearningWithErrors.Problem
      (Challenge R dimension blocks samples) Secret (Output R blocks samples) where
  sampleChallenge := Fin.mOfFn blocks fun _ ↦
    $ᵗ Matrix (Fin dimension) (Fin samples) R
  sampleSecret := secretSampler
  sampleError := Fin.mOfFn blocks fun _ ↦ ProbComp.sampleIID samples errorSampler
  noiseless := fun secret challenge block ↦ vecMul (embed secret) (challenge block)
  sampleUniform := Fin.mOfFn blocks fun _ ↦ $ᵗ (Fin samples → R)

/-- Preprocess one conventional combined batch transcript for a parallel-batch adversary. -/
def reduction {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    {dimension blocks samples : ℕ}
    {secretSampler : ProbComp Secret} {embed : Secret → Fin dimension → R}
    {errorSampler : ProbComp R}
    (adversary : LearningWithErrors.Adversary
      (problem dimension blocks samples secretSampler embed errorSampler)) :
    LearningWithErrors.Adversary
      (embeddedBatchProblem dimension (blocks * samples)
        secretSampler embed errorSampler) :=
  fun transcript ↦ adversary (transcriptEquiv R dimension blocks samples transcript)

/-- Flattening `blocks` independent IID vectors gives one IID vector of product length. -/
theorem outputEquiv_sampleIID_evalDist {R : Type} [Finite R]
    (blocks samples : ℕ) (sampler : ProbComp R) :
    evalDist (outputEquiv R blocks samples <$>
      ProbComp.sampleIID (blocks * samples) sampler) =
    evalDist (Fin.mOfFn blocks fun _ ↦ ProbComp.sampleIID samples sampler) := by
  letI : Fintype R := Fintype.ofFinite R
  letI : DecidableEq R := Classical.decEq R
  apply evalDist_ext
  intro values
  rw [probOutput_map_equiv]
  simp only [ProbComp.sampleIID,
    FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn]
  calc
    (∏ index : Fin (blocks * samples),
        Pr[= (outputEquiv R blocks samples).symm values index | sampler]) =
      ∏ pair : Fin blocks × Fin samples, Pr[= values pair.1 pair.2 | sampler] := by
        apply Fintype.prod_equiv finProdFinEquiv.symm
        intro index
        rfl
    _ = ∏ block, ∏ sample, Pr[= values block sample | sampler] :=
      Fintype.prod_prod_type _

/-- The parallel challenge sampler is the image of one uniform combined challenge under the
column-splitting equivalence. -/
theorem challengeEquiv_uniform_evalDist {R : Type} [Fintype R] [SampleableType R]
    (dimension blocks samples : ℕ) :
    evalDist (challengeEquiv R dimension blocks samples <$>
      ($ᵗ Matrix (Fin dimension) (Fin (blocks * samples)) R)) =
    evalDist (Fin.mOfFn blocks fun _ ↦
      $ᵗ Matrix (Fin dimension) (Fin samples) R) := by
  have hMapped :
      evalDist (challengeEquiv R dimension blocks samples <$>
        ($ᵗ Matrix (Fin dimension) (Fin (blocks * samples)) R)) =
      evalDist ($ᵗ (Challenge R dimension blocks samples)) :=
    evalDist_map_bijective_uniform_cross
      (α := Matrix (Fin dimension) (Fin (blocks * samples)) R)
      (β := Challenge R dimension blocks samples)
      (challengeEquiv R dimension blocks samples)
      (challengeEquiv R dimension blocks samples).bijective
  have hParallel :
      evalDist (Fin.mOfFn blocks fun _ ↦
        $ᵗ Matrix (Fin dimension) (Fin samples) R) =
      evalDist ($ᵗ (Challenge R dimension blocks samples)) := by
    simpa [ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := Matrix (Fin dimension) (Fin samples) R) blocks)
  exact hMapped.trans hParallel.symm

/-- The parallel uniform-output sampler is the image of one combined uniform output. -/
theorem outputEquiv_uniform_evalDist {R : Type} [Fintype R] [SampleableType R]
    (blocks samples : ℕ) :
    evalDist (outputEquiv R blocks samples <$>
      ($ᵗ (Fin (blocks * samples) → R))) =
    evalDist (Fin.mOfFn blocks fun _ ↦ $ᵗ (Fin samples → R)) := by
  have hMapped :
      evalDist (outputEquiv R blocks samples <$>
        ($ᵗ (Fin (blocks * samples) → R))) =
      evalDist ($ᵗ (Output R blocks samples)) :=
    evalDist_map_bijective_uniform_cross
      (α := Fin (blocks * samples) → R)
      (β := Output R blocks samples)
      (outputEquiv R blocks samples) (outputEquiv R blocks samples).bijective
  have hParallel :
      evalDist (Fin.mOfFn blocks fun _ ↦ $ᵗ (Fin samples → R)) =
      evalDist ($ᵗ (Output R blocks samples)) := by
    simpa [ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := Fin samples → R) blocks)
  exact hMapped.trans hParallel.symm

/-- Deterministically assemble a real parallel transcript. -/
def realTranscript {R Secret : Type} [Semiring R]
    {dimension blocks samples : ℕ}
    (embed : Secret → Fin dimension → R)
    (challenge : Challenge R dimension blocks samples)
    (secret : Secret) (error : Output R blocks samples) :
    Transcript R dimension blocks samples :=
  (challenge, fun block ↦ vecMul (embed secret) (challenge block) + error block)

/-- Transcript splitting commutes with noiseless matrix multiplication and pointwise error
addition. -/
theorem transcriptEquiv_real {R Secret : Type} [Semiring R]
    {dimension blocks samples : ℕ}
    (embed : Secret → Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin (blocks * samples)) R)
    (secret : Secret) (error : Fin (blocks * samples) → R) :
    transcriptEquiv R dimension blocks samples
        (challenge, vecMul (embed secret) challenge + error) =
      realTranscript embed (challengeEquiv R dimension blocks samples challenge) secret
        (outputEquiv R blocks samples error) := by
  apply Prod.ext
  · rfl
  · funext block sample
    rfl

/-- Splitting maps the conventional real batch distribution exactly to the parallel real
distribution. -/
theorem real_evalDist {R Secret : Type}
    [Semiring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension blocks samples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R) :
    evalDist (LearningWithErrors.distr
          (embeddedBatchProblem dimension (blocks * samples)
            secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (transcriptEquiv R dimension blocks samples transcript)) =
      evalDist (LearningWithErrors.distr
        (problem dimension blocks samples secretSampler embed errorSampler)) := by
  let combinedChallenge :
      ProbComp (Matrix (Fin dimension) (Fin (blocks * samples)) R) :=
    $ᵗ Matrix (Fin dimension) (Fin (blocks * samples)) R
  let mappedChallenge : ProbComp (Challenge R dimension blocks samples) :=
    challengeEquiv R dimension blocks samples <$> combinedChallenge
  let targetChallenge : ProbComp (Challenge R dimension blocks samples) :=
    Fin.mOfFn blocks fun _ ↦ $ᵗ Matrix (Fin dimension) (Fin samples) R
  let combinedError : ProbComp (Fin (blocks * samples) → R) :=
    ProbComp.sampleIID (blocks * samples) errorSampler
  let mappedError : ProbComp (Output R blocks samples) :=
    outputEquiv R blocks samples <$> combinedError
  let targetError : ProbComp (Output R blocks samples) :=
    Fin.mOfFn blocks fun _ ↦ ProbComp.sampleIID samples errorSampler
  have hChallenge : evalDist mappedChallenge = evalDist targetChallenge := by
    simpa [mappedChallenge, combinedChallenge, targetChallenge] using
      (challengeEquiv_uniform_evalDist (R := R) dimension blocks samples)
  have hError : evalDist mappedError = evalDist targetError := by
    simpa [mappedError, combinedError, targetError] using
      (outputEquiv_sampleIID_evalDist (R := R) blocks samples errorSampler)
  have left_eq :
      (LearningWithErrors.distr
          (embeddedBatchProblem dimension (blocks * samples)
            secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (transcriptEquiv R dimension blocks samples transcript)) =
      (mappedChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        mappedError >>= fun error ↦
        pure (realTranscript embed challenge secret error)) := by
    simp [LearningWithErrors.distr, embeddedBatchProblem, mappedChallenge,
      combinedChallenge, mappedError, combinedError, transcriptEquiv_real,
      bind_assoc, monad_norm]
  have right_eq :
      LearningWithErrors.distr
          (problem dimension blocks samples secretSampler embed errorSampler) =
      (targetChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        targetError >>= fun error ↦
        pure (realTranscript embed challenge secret error)) := by
    simp [LearningWithErrors.distr, problem, targetChallenge, targetError,
      realTranscript, pointwiseAdd_eq_add, monad_norm]
  rw [left_eq, right_eq]
  calc
    _ = evalDist (targetChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        mappedError >>= fun error ↦
        pure (realTranscript embed challenge secret error)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hChallenge _
    _ = _ := by
      refine evalDist_bind_congr' targetChallenge fun challenge ↦ ?_
      refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hError _

/-- The parallel uniform distribution is uniform on its complete transcript space. -/
theorem uniformDistr_evalDist_eq_uniformSample {R Secret : Type}
    [Semiring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension blocks samples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R) :
    evalDist (LearningWithErrors.uniformDistr
      (problem dimension blocks samples secretSampler embed errorSampler)) =
    evalDist ($ᵗ (Transcript R dimension blocks samples)) := by
  let challengeSampler : ProbComp (Challenge R dimension blocks samples) :=
    Fin.mOfFn blocks fun _ ↦ $ᵗ Matrix (Fin dimension) (Fin samples) R
  let outputSampler : ProbComp (Output R blocks samples) :=
    Fin.mOfFn blocks fun _ ↦ $ᵗ (Fin samples → R)
  have hChallenge : evalDist challengeSampler =
      evalDist ($ᵗ (Challenge R dimension blocks samples)) := by
    simpa [challengeSampler, ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := Matrix (Fin dimension) (Fin samples) R) blocks)
  have hOutput : evalDist outputSampler =
      evalDist ($ᵗ (Output R blocks samples)) := by
    simpa [outputSampler, ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := Fin samples → R) blocks)
  have uniformProduct :
      ($ᵗ (Transcript R dimension blocks samples) :
        ProbComp (Transcript R dimension blocks samples)) =
      Prod.mk <$> ($ᵗ (Challenge R dimension blocks samples)) <*>
        ($ᵗ (Output R blocks samples)) := by
    rfl
  change evalDist (challengeSampler >>= fun challenge ↦
      outputSampler >>= fun output ↦ pure (challenge, output)) = _
  calc
    _ = evalDist (($ᵗ (Challenge R dimension blocks samples)) >>= fun challenge ↦
        outputSampler >>= fun output ↦ pure (challenge, output)) := by
      rw [evalDist_bind, evalDist_bind, hChallenge]
    _ = evalDist (($ᵗ (Challenge R dimension blocks samples)) >>= fun challenge ↦
        ($ᵗ (Output R blocks samples)) >>= fun output ↦
        pure (challenge, output)) := by
      refine evalDist_bind_congr' ($ᵗ (Challenge R dimension blocks samples)) fun _ ↦ ?_
      rw [evalDist_bind, evalDist_bind, hOutput]
    _ = evalDist ($ᵗ (Transcript R dimension blocks samples)) := by
      rw [uniformProduct]
      simp [monad_norm]

/-- Splitting maps the conventional uniform batch distribution exactly to the parallel uniform
distribution. -/
theorem uniform_evalDist {R Secret : Type}
    [Semiring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension blocks samples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R) :
    evalDist (LearningWithErrors.uniformDistr
          (embeddedBatchProblem dimension (blocks * samples)
            secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (transcriptEquiv R dimension blocks samples transcript)) =
      evalDist (LearningWithErrors.uniformDistr
        (problem dimension blocks samples secretSampler embed errorSampler)) := by
  rw [FormalProof4FHE.LWE.TwoBlock.batchUniformDistr_eq_uniformSample,
    uniformDistr_evalDist_eq_uniformSample]
  rw [show (($ᵗ (BatchTranscript R dimension (blocks * samples))) >>= fun transcript ↦
      pure (transcriptEquiv R dimension blocks samples transcript)) =
      transcriptEquiv R dimension blocks samples <$>
        ($ᵗ (BatchTranscript R dimension (blocks * samples))) by
    simp [monad_norm]]
  exact evalDist_map_bijective_uniform_cross
    (α := BatchTranscript R dimension (blocks * samples))
    (β := Transcript R dimension blocks samples)
    (transcriptEquiv R dimension blocks samples)
    (transcriptEquiv R dimension blocks samples).bijective

/-- Exact real-game equality for parallel-batch preprocessing. -/
theorem game0_evalDist_eq {R Secret : Type}
    [Semiring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension blocks samples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem dimension blocks samples secretSampler embed errorSampler)) :
    evalDist (LearningWithErrors.game0
        (problem dimension blocks samples secretSampler embed errorSampler) adversary) =
      evalDist (LearningWithErrors.game0
        (embeddedBatchProblem dimension (blocks * samples)
          secretSampler embed errorSampler) (reduction adversary)) := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  simp only [reduction]
  rw [show (LearningWithErrors.distr
        (embeddedBatchProblem dimension (blocks * samples)
          secretSampler embed errorSampler) >>=
      fun transcript ↦ adversary (transcriptEquiv R dimension blocks samples transcript)) =
    ((LearningWithErrors.distr
        (embeddedBatchProblem dimension (blocks * samples)
          secretSampler embed errorSampler) >>=
      fun transcript ↦ pure (transcriptEquiv R dimension blocks samples transcript)) >>=
        adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    real_evalDist dimension blocks samples secretSampler embed errorSampler]

/-- Exact uniform-game equality for parallel-batch preprocessing. -/
theorem game1_evalDist_eq {R Secret : Type}
    [Semiring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension blocks samples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem dimension blocks samples secretSampler embed errorSampler)) :
    evalDist (LearningWithErrors.game1
        (problem dimension blocks samples secretSampler embed errorSampler) adversary) =
      evalDist (LearningWithErrors.game1
        (embeddedBatchProblem dimension (blocks * samples)
          secretSampler embed errorSampler) (reduction adversary)) := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [reduction]
  rw [show (LearningWithErrors.uniformDistr
        (embeddedBatchProblem dimension (blocks * samples)
          secretSampler embed errorSampler) >>=
      fun transcript ↦ adversary (transcriptEquiv R dimension blocks samples transcript)) =
    ((LearningWithErrors.uniformDistr
        (embeddedBatchProblem dimension (blocks * samples)
          secretSampler embed errorSampler) >>=
      fun transcript ↦ pure (transcriptEquiv R dimension blocks samples transcript)) >>=
        adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    uniform_evalDist dimension blocks samples secretSampler embed errorSampler]

/-- Parallel-batch distinguishing advantage is exactly conventional combined-batch advantage. -/
theorem advantage_eq_batch {R Secret : Type}
    [Semiring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension blocks samples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem dimension blocks samples secretSampler embed errorSampler)) :
    LearningWithErrors.advantage
        (problem dimension blocks samples secretSampler embed errorSampler) adversary =
      LearningWithErrors.advantage
        (embeddedBatchProblem dimension (blocks * samples)
          secretSampler embed errorSampler) (reduction adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (game0_evalDist_eq dimension blocks samples secretSampler embed errorSampler adversary) true,
    evalDist_ext_iff.mp
      (game1_evalDist_eq dimension blocks samples secretSampler embed errorSampler adversary) true]

end FormalProof4FHE.LWE.ParallelBatch
