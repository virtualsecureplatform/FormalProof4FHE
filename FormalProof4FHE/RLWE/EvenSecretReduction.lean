/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.OddSecretReduction

/-!
# Exact Reduction for Parity-Placed Even RLWE Secrets

For

`R = ZMod q[X] / (X^(2*n) + 1)` and `S = ZMod q[Y] / (Y^n + 1)`,

this file transports RLWE whose large-ring secret is `p(X²)` to two ordinary degree-`n`
RLWE blocks sharing `p`.  In contrast with odd-coordinate placement, both mask components are
untwisted:

`(a₀(X²) + X*a₁(X²)) * p(X²) = (a₀*p)(X²) + X*(a₁*p)(X²)`.

Splitting every challenge, output, and error into its even and odd coefficients is a bijection
of complete transcripts.  Hence the reduction has no statistical term or hybrid loss, and one
large-ring sample becomes exactly two ordinary small-ring samples.
-/

set_option autoImplicit false

open Matrix OracleComp

namespace FormalProof4FHE.RLWE.EvenSecretReduction

noncomputable section

open EvenOddDecomposition

/-- Embed the shared small-ring secret without changing it. -/
def smallSecretEmbed (q half : ℕ) :
    RLWE.Secret q half → Fin 1 → RLWE.Rq q half :=
  id

/-- Place a small-ring secret in the even coefficients of the large ring. -/
def evenSecretEmbed (q half : ℕ) :
    RLWE.Secret q half → Fin 1 → RLWE.Rq q (2 * half) :=
  fun secret row ↦ joinRq q half (secret row) 0

/-- One large-ring error made from independent even and odd small-ring errors. -/
noncomputable def pairedErrorSampler (q half : ℕ)
    (errorSampler : ProbComp (RLWE.Rq q half)) :
    ProbComp (RLWE.Rq q (2 * half)) :=
  RLWE.OddSecretReduction.pairedErrorSampler q half errorSampler

/-- Two degree-`half` batches that share one small-ring secret. -/
noncomputable def parallelProblem (q half samples : ℕ) [NeZero q]
    (secretSampler : ProbComp (RLWE.Secret q half))
    (errorSampler : ProbComp (RLWE.Rq q half)) :=
  LWE.ParallelBatch.problem 1 2 samples secretSampler
    (smallSecretEmbed q half) errorSampler

/-- Degree-`2 * half` RLWE with an even-coordinate embedded secret and paired coefficient
error. -/
noncomputable def evenProblem (q half samples : ℕ) [NeZero q]
    (secretSampler : ProbComp (RLWE.Secret q half))
    (errorSampler : ProbComp (RLWE.Rq q half)) :=
  LWE.embeddedBatchProblem 1 samples secretSampler
    (evenSecretEmbed q half) (pairedErrorSampler q half errorSampler)

/-- The two small public-mask blocks are exactly one large public-mask block. -/
def challengeEquiv (q half samples : ℕ) :
    LWE.ParallelBatch.Challenge (RLWE.Rq q half) 1 2 samples ≃
      RLWE.Sample q (2 * half) samples where
  toFun challenge row sample :=
    joinRq q half (challenge 0 row sample) (challenge 1 row sample)
  invFun challenge block row sample :=
    (finTwoArrowEquiv (RLWE.Rq q half)).symm
      (ringParityEquiv q half (challenge row sample)) block
  left_inv challenge := by
    funext block row sample
    fin_cases block <;> simp
  right_inv challenge := by
    funext row sample
    simp

/-- Join the even and odd output blocks coefficientwise. -/
def outputEquiv (q half samples : ℕ) :
    LWE.ParallelBatch.Output (RLWE.Rq q half) 2 samples ≃
      RLWE.Output q (2 * half) samples where
  toFun output sample := joinRq q half (output 0 sample) (output 1 sample)
  invFun output block sample :=
    (finTwoArrowEquiv (RLWE.Rq q half)).symm
      (ringParityEquiv q half (output sample)) block
  left_inv output := by
    funext block sample
    fin_cases block <;> simp
  right_inv output := by
    funext sample
    simp

@[simp]
theorem challengeEquiv_apply (q half samples : ℕ)
    (challenge : LWE.ParallelBatch.Challenge (RLWE.Rq q half) 1 2 samples)
    (row : Fin 1) (sample : Fin samples) :
    challengeEquiv q half samples challenge row sample =
      joinRq q half (challenge 0 row sample) (challenge 1 row sample) := by
  rfl

@[simp]
theorem outputEquiv_apply (q half samples : ℕ)
    (output : LWE.ParallelBatch.Output (RLWE.Rq q half) 2 samples)
    (sample : Fin samples) :
    outputEquiv q half samples output sample =
      joinRq q half (output 0 sample) (output 1 sample) := by
  rfl

/-- Bijection between complete parallel and even-secret public transcripts. -/
def transcriptEquiv (q half samples : ℕ) :
    LWE.ParallelBatch.Transcript (RLWE.Rq q half) 1 2 samples ≃
      (RLWE.Sample q (2 * half) samples × RLWE.Output q (2 * half) samples) :=
  (challengeEquiv q half samples).prodCongr (outputEquiv q half samples)

@[simp]
theorem outputEquiv_add (q half samples : ℕ)
    (left right : LWE.ParallelBatch.Output (RLWE.Rq q half) 2 samples) :
    outputEquiv q half samples (left + right) =
      outputEquiv q half samples left + outputEquiv q half samples right := by
  funext sample
  exact joinRq_add q half (left 0 sample) (left 1 sample)
    (right 0 sample) (right 1 sample)

/-- The noiseless two-block small-ring output maps to the noiseless even-secret large-ring
output. -/
theorem outputEquiv_vecMul (q half samples : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half) (secret : RLWE.Secret q half)
    (challenge : LWE.ParallelBatch.Challenge (RLWE.Rq q half) 1 2 samples) :
    outputEquiv q half samples
        (fun block ↦ vecMul (smallSecretEmbed q half secret) (challenge block)) =
      vecMul (evenSecretEmbed q half secret)
        (challengeEquiv q half samples challenge) := by
  funext sample
  simp only [outputEquiv_apply, challengeEquiv_apply, smallSecretEmbed,
    evenSecretEmbed, Matrix.vecMul, dotProduct, Fin.sum_univ_one, id_eq]
  rw [mul_comm
    (joinRq q half (secret 0) 0)
    (joinRq q half (challenge 0 0 sample) (challenge 1 0 sample))]
  rw [mul_comm (secret 0) (challenge 0 0 sample),
    mul_comm (secret 0) (challenge 1 0 sample)]
  exact (joinRq_commRing_mul_even q half hhalf
    (challenge 0 0 sample) (challenge 1 0 sample) (secret 0)).symm

/-- Complete deterministic real-transcript assembly commutes with the transcript bijection. -/
theorem transcriptEquiv_real (q half samples : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half)
    (challenge : LWE.ParallelBatch.Challenge (RLWE.Rq q half) 1 2 samples)
    (secret : RLWE.Secret q half)
    (error : LWE.ParallelBatch.Output (RLWE.Rq q half) 2 samples) :
    transcriptEquiv q half samples
        (challenge,
          fun block ↦
            vecMul (smallSecretEmbed q half secret) (challenge block) + error block) =
      (challengeEquiv q half samples challenge,
        vecMul (evenSecretEmbed q half secret)
            (challengeEquiv q half samples challenge) +
          outputEquiv q half samples error) := by
  apply Prod.ext
  · rfl
  · change outputEquiv q half samples
        ((fun block ↦ vecMul (smallSecretEmbed q half secret) (challenge block)) + error) = _
    rw [outputEquiv_add, outputEquiv_vecMul q half samples hhalf]

@[simp]
theorem transcriptEquiv_real_add (q half samples : ℕ) [Nontrivial (ZMod q)]
    (hhalf : 0 < half)
    (challenge : LWE.ParallelBatch.Challenge (RLWE.Rq q half) 1 2 samples)
    (secret : RLWE.Secret q half)
    (error : LWE.ParallelBatch.Output (RLWE.Rq q half) 2 samples) :
    transcriptEquiv q half samples
        (challenge,
          (fun block ↦ vecMul (smallSecretEmbed q half secret) (challenge block)) + error) =
      (challengeEquiv q half samples challenge,
        vecMul (evenSecretEmbed q half secret)
            (challengeEquiv q half samples challenge) +
          outputEquiv q half samples error) := by
  exact transcriptEquiv_real q half samples hhalf challenge secret error

/-! ## Exact sampler transport -/

/-- Probability mass of one paired large-ring error factors into its two small-ring halves. -/
theorem probOutput_pairedErrorSampler (q half : ℕ)
    (errorSampler : ProbComp (RLWE.Rq q half))
    (value : RLWE.Rq q (2 * half)) :
    Pr[= value | pairedErrorSampler q half errorSampler] =
      Pr[= (ringParityEquiv q half value).1 | errorSampler] *
        Pr[= (ringParityEquiv q half value).2 | errorSampler] := by
  exact RLWE.OddSecretReduction.probOutput_pairedErrorSampler
    q half errorSampler value

/-- Joining two independently sampled small-ring error vectors gives independent samples from
the paired large-ring error law. -/
theorem outputEquiv_error_evalDist (q half samples : ℕ)
    [NeZero q] (errorSampler : ProbComp (RLWE.Rq q half)) :
    evalDist (outputEquiv q half samples <$>
      (Fin.mOfFn 2 fun _ ↦ ProbComp.sampleIID samples errorSampler)) =
      evalDist (ProbComp.sampleIID samples
        (pairedErrorSampler q half errorSampler)) := by
  apply evalDist_ext
  intro values
  rw [probOutput_map_equiv]
  simp only [ProbComp.sampleIID,
    FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn,
    probOutput_pairedErrorSampler]
  rw [Fin.prod_univ_two]
  rw [Finset.prod_mul_distrib]
  simp [outputEquiv, finTwoArrowEquiv]

/-- The public-mask bijection sends the independently uniform two-block challenge sampler to the
uniform large-ring challenge sampler. -/
theorem challengeEquiv_evalDist (q half samples : ℕ) [NeZero q] :
    evalDist (challengeEquiv q half samples <$>
      (Fin.mOfFn 2 fun _ ↦
        ($ᵗ Matrix (Fin 1) (Fin samples) (RLWE.Rq q half)))) =
      evalDist ($ᵗ RLWE.Sample q (2 * half) samples) := by
  have hsource :
      evalDist (Fin.mOfFn 2 fun _ ↦
        ($ᵗ Matrix (Fin 1) (Fin samples) (RLWE.Rq q half))) =
      evalDist ($ᵗ (LWE.ParallelBatch.Challenge
        (RLWE.Rq q half) 1 2 samples)) := by
    simpa [ProbComp.sampleIID] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := Matrix (Fin 1) (Fin samples) (RLWE.Rq q half)) 2)
  calc
    _ = evalDist (challengeEquiv q half samples <$>
        ($ᵗ (LWE.ParallelBatch.Challenge
          (RLWE.Rq q half) 1 2 samples))) := by
      simpa [parallelProblem, evalDist_map] using congrArg
        (fun distribution ↦ challengeEquiv q half samples <$> distribution)
        hsource
    _ = _ := evalDist_map_bijective_uniform_cross
      (α := LWE.ParallelBatch.Challenge (RLWE.Rq q half) 1 2 samples)
      (β := RLWE.Sample q (2 * half) samples)
      (challengeEquiv q half samples)
      (challengeEquiv q half samples).bijective

/-! ## Exact game transport -/

/-- Mapping the parallel real transcript gives exactly the even-secret large-ring real
transcript. -/
theorem real_evalDist (q half samples : ℕ)
    [NeZero q] [Nontrivial (ZMod q)] (hhalf : 0 < half)
    (secretSampler : ProbComp (RLWE.Secret q half))
    (errorSampler : ProbComp (RLWE.Rq q half)) :
    evalDist (LearningWithErrors.distr
          (parallelProblem q half samples secretSampler errorSampler) >>=
        fun transcript ↦ pure (transcriptEquiv q half samples transcript)) =
      evalDist (LearningWithErrors.distr
        (evenProblem q half samples secretSampler errorSampler)) := by
  let sourceChallenge : ProbComp
      (LWE.ParallelBatch.Challenge (RLWE.Rq q half) 1 2 samples) :=
    Fin.mOfFn 2 fun _ ↦
      ($ᵗ Matrix (Fin 1) (Fin samples) (RLWE.Rq q half))
  let mappedChallenge :=
    challengeEquiv q half samples <$> sourceChallenge
  let targetChallenge : ProbComp (RLWE.Sample q (2 * half) samples) :=
    $ᵗ RLWE.Sample q (2 * half) samples
  let sourceError : ProbComp
      (LWE.ParallelBatch.Output (RLWE.Rq q half) 2 samples) :=
    Fin.mOfFn 2 fun _ ↦ ProbComp.sampleIID samples errorSampler
  let mappedError := outputEquiv q half samples <$> sourceError
  let targetError := ProbComp.sampleIID samples
    (pairedErrorSampler q half errorSampler)
  let finish : RLWE.Sample q (2 * half) samples → RLWE.Secret q half →
      RLWE.Output q (2 * half) samples →
      ProbComp (RLWE.Sample q (2 * half) samples ×
        RLWE.Output q (2 * half) samples) :=
    fun challenge secret error ↦
      pure (challenge, vecMul (evenSecretEmbed q half secret) challenge + error)
  have hChallenge : evalDist mappedChallenge = evalDist targetChallenge := by
    simpa [mappedChallenge, sourceChallenge, targetChallenge] using
      (challengeEquiv_evalDist q half samples)
  have hError : evalDist mappedError = evalDist targetError := by
    simpa [mappedError, sourceError, targetError] using
      (outputEquiv_error_evalDist q half samples errorSampler)
  have left_eq :
      (LearningWithErrors.distr
          (parallelProblem q half samples secretSampler errorSampler) >>=
        fun transcript ↦ pure (transcriptEquiv q half samples transcript)) =
      (mappedChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        mappedError >>= fun error ↦
        finish challenge secret error) := by
    simp [LearningWithErrors.distr, parallelProblem,
      LWE.ParallelBatch.problem, mappedChallenge, sourceChallenge,
      mappedError, sourceError, finish,
      bind_assoc, monad_norm,
      transcriptEquiv_real_add q half samples hhalf]
  have right_eq :
      LearningWithErrors.distr
          (evenProblem q half samples secretSampler errorSampler) =
      (targetChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        targetError >>= fun error ↦
        finish challenge secret error) := by
    simp [LearningWithErrors.distr, evenProblem, LWE.embeddedBatchProblem,
      targetChallenge, targetError, finish, monad_norm]
  rw [left_eq, right_eq]
  calc
    _ = evalDist (targetChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        mappedError >>= fun error ↦
        finish challenge secret error) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hChallenge _
    _ = _ := by
      refine evalDist_bind_congr' targetChallenge fun challenge ↦ ?_
      refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hError _

/-- The transcript bijection also transports the uniform branch exactly. -/
theorem uniform_evalDist (q half samples : ℕ)
    [NeZero q] [Nontrivial (ZMod q)]
    (secretSampler : ProbComp (RLWE.Secret q half))
    (errorSampler : ProbComp (RLWE.Rq q half)) :
    evalDist (LearningWithErrors.uniformDistr
          (parallelProblem q half samples secretSampler errorSampler) >>=
        fun transcript ↦ pure (transcriptEquiv q half samples transcript)) =
      evalDist (LearningWithErrors.uniformDistr
        (evenProblem q half samples secretSampler errorSampler)) := by
  have hsource := LWE.ParallelBatch.uniformDistr_evalDist_eq_uniformSample
    1 2 samples secretSampler (smallSecretEmbed q half) errorSampler
  change _ = evalDist (LearningWithErrors.uniformDistr
    (LWE.embeddedBatchProblem 1 samples secretSampler
      (evenSecretEmbed q half) (pairedErrorSampler q half errorSampler)))
  rw [LWE.TwoBlock.batchUniformDistr_eq_uniformSample]
  rw [show (LearningWithErrors.uniformDistr
          (parallelProblem q half samples secretSampler errorSampler) >>=
        fun transcript ↦ pure (transcriptEquiv q half samples transcript)) =
      transcriptEquiv q half samples <$>
        LearningWithErrors.uniformDistr
          (parallelProblem q half samples secretSampler errorSampler) by
    simp [monad_norm]]
  calc
    _ = evalDist (transcriptEquiv q half samples <$>
        ($ᵗ (LWE.ParallelBatch.Transcript
          (RLWE.Rq q half) 1 2 samples))) := by
      simpa [parallelProblem, evalDist_map] using congrArg
        (fun distribution ↦ transcriptEquiv q half samples <$> distribution)
        hsource
    _ = _ := evalDist_map_bijective_uniform_cross
      (α := LWE.ParallelBatch.Transcript (RLWE.Rq q half) 1 2 samples)
      (β := RLWE.Sample q (2 * half) samples ×
        RLWE.Output q (2 * half) samples)
      (transcriptEquiv q half samples)
      (transcriptEquiv q half samples).bijective

/-- Preprocess an even-secret large-ring adversary with exact transcript splitting. -/
def parallelAdversary {q half samples : ℕ}
    [NeZero q] [Nontrivial (ZMod q)]
    {secretSampler : ProbComp (RLWE.Secret q half)}
    {errorSampler : ProbComp (RLWE.Rq q half)}
    (adversary : LearningWithErrors.Adversary
      (evenProblem q half samples secretSampler errorSampler)) :
    LearningWithErrors.Adversary
      (parallelProblem q half samples secretSampler errorSampler) :=
  fun transcript ↦ adversary (transcriptEquiv q half samples transcript)

/-- Exact equality of real-game output distributions under transcript preprocessing. -/
theorem game0_evalDist_eq (q half samples : ℕ)
    [NeZero q] [Nontrivial (ZMod q)] (hhalf : 0 < half)
    (secretSampler : ProbComp (RLWE.Secret q half))
    (errorSampler : ProbComp (RLWE.Rq q half))
    (adversary : LearningWithErrors.Adversary
      (evenProblem q half samples secretSampler errorSampler)) :
    evalDist (LearningWithErrors.game0
        (evenProblem q half samples secretSampler errorSampler) adversary) =
      evalDist (LearningWithErrors.game0
        (parallelProblem q half samples secretSampler errorSampler)
        (parallelAdversary adversary)) := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  change evalDist (LearningWithErrors.distr
      (evenProblem q half samples secretSampler errorSampler) >>= adversary) =
    evalDist (LearningWithErrors.distr
      (parallelProblem q half samples secretSampler errorSampler) >>=
        fun transcript ↦ adversary (transcriptEquiv q half samples transcript))
  rw [show (LearningWithErrors.distr
      (parallelProblem q half samples secretSampler errorSampler) >>=
        fun transcript ↦ adversary (transcriptEquiv q half samples transcript)) =
    ((LearningWithErrors.distr
        (parallelProblem q half samples secretSampler errorSampler) >>=
      fun transcript ↦ pure (transcriptEquiv q half samples transcript)) >>=
        adversary) by simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    real_evalDist q half samples hhalf secretSampler errorSampler]

/-- Exact equality of uniform-game output distributions under transcript preprocessing. -/
theorem game1_evalDist_eq (q half samples : ℕ)
    [NeZero q] [Nontrivial (ZMod q)]
    (secretSampler : ProbComp (RLWE.Secret q half))
    (errorSampler : ProbComp (RLWE.Rq q half))
    (adversary : LearningWithErrors.Adversary
      (evenProblem q half samples secretSampler errorSampler)) :
    evalDist (LearningWithErrors.game1
        (evenProblem q half samples secretSampler errorSampler) adversary) =
      evalDist (LearningWithErrors.game1
        (parallelProblem q half samples secretSampler errorSampler)
        (parallelAdversary adversary)) := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  change evalDist (LearningWithErrors.uniformDistr
      (evenProblem q half samples secretSampler errorSampler) >>= adversary) =
    evalDist (LearningWithErrors.uniformDistr
      (parallelProblem q half samples secretSampler errorSampler) >>=
        fun transcript ↦ adversary (transcriptEquiv q half samples transcript))
  rw [show (LearningWithErrors.uniformDistr
      (parallelProblem q half samples secretSampler errorSampler) >>=
        fun transcript ↦ adversary (transcriptEquiv q half samples transcript)) =
    ((LearningWithErrors.uniformDistr
        (parallelProblem q half samples secretSampler errorSampler) >>=
      fun transcript ↦ pure (transcriptEquiv q half samples transcript)) >>=
        adversary) by simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    uniform_evalDist q half samples secretSampler errorSampler]

/-- The even-secret large-ring advantage is exactly the two-block small-ring advantage. -/
theorem advantage_eq_parallel (q half samples : ℕ)
    [NeZero q] [Nontrivial (ZMod q)] (hhalf : 0 < half)
    (secretSampler : ProbComp (RLWE.Secret q half))
    (errorSampler : ProbComp (RLWE.Rq q half))
    (adversary : LearningWithErrors.Adversary
      (evenProblem q half samples secretSampler errorSampler)) :
    LearningWithErrors.advantage
        (evenProblem q half samples secretSampler errorSampler) adversary =
      LearningWithErrors.advantage
        (parallelProblem q half samples secretSampler errorSampler)
        (parallelAdversary adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (game0_evalDist_eq q half samples hhalf secretSampler errorSampler adversary) true,
    evalDist_ext_iff.mp
      (game1_evalDist_eq q half samples secretSampler errorSampler adversary) true]

/-- With the identity rank-one embedding, the conventional small-ring batch problem is exactly
the repository's explicit-secret RLWE problem. -/
theorem smallEmbeddedProblem_eq_rlwe (q half sampleCount : ℕ) [NeZero q]
    (secretSampler : ProbComp (RLWE.Secret q half))
    (errorSampler : ProbComp (RLWE.Rq q half)) :
    LWE.embeddedBatchProblem 1 sampleCount secretSampler
        (smallSecretEmbed q half) errorSampler =
      RLWE.problem q half sampleCount secretSampler errorSampler := by
  rfl

/-- Combined reduction from degree-`2 * half` even-secret RLWE to ordinary degree-`half` RLWE
with twice the sample count. -/
def reduction {q half samples : ℕ}
    [NeZero q] [Nontrivial (ZMod q)]
    {secretSampler : ProbComp (RLWE.Secret q half)}
    {errorSampler : ProbComp (RLWE.Rq q half)}
    (adversary : LearningWithErrors.Adversary
      (evenProblem q half samples secretSampler errorSampler)) :
    LearningWithErrors.Adversary
      (RLWE.problem q half (2 * samples) secretSampler errorSampler) := by
  rw [← smallEmbeddedProblem_eq_rlwe]
  exact LWE.ParallelBatch.reduction (parallelAdversary adversary)

/-- Exact main theorem: parity-placed even-secret degree-`2 * half` RLWE is ordinary
degree-`half` RLWE with `2 * samples` samples. -/
theorem advantage_eq_smallRLWE (q half samples : ℕ)
    [NeZero q] [Nontrivial (ZMod q)] (hhalf : 0 < half)
    (secretSampler : ProbComp (RLWE.Secret q half))
    (errorSampler : ProbComp (RLWE.Rq q half))
    (adversary : LearningWithErrors.Adversary
      (evenProblem q half samples secretSampler errorSampler)) :
    LearningWithErrors.advantage
        (evenProblem q half samples secretSampler errorSampler) adversary =
      LearningWithErrors.advantage
        (RLWE.problem q half (2 * samples) secretSampler errorSampler)
        (reduction adversary) := by
  cases half with
  | zero => omega
  | succ half =>
      rw [advantage_eq_parallel q (half + 1) samples hhalf]
      change LearningWithErrors.advantage
          (LWE.ParallelBatch.problem 1 2 samples secretSampler
            (smallSecretEmbed q (half + 1)) errorSampler)
          (parallelAdversary adversary) = _
      rw [← smallEmbeddedProblem_eq_rlwe]
      exact LWE.ParallelBatch.advantage_eq_batch
        1 2 samples secretSampler (smallSecretEmbed q (half + 1)) errorSampler
        (parallelAdversary adversary)

/-- Any concrete security bound for the ordinary smaller-ring problem transfers without loss. -/
theorem advantage_le_of_smallRLWE (q half samples : ℕ)
    [NeZero q] [Nontrivial (ZMod q)] (hhalf : 0 < half)
    (secretSampler : ProbComp (RLWE.Secret q half))
    (errorSampler : ProbComp (RLWE.Rq q half))
    (bound : ℝ)
    (hsmall : ∀ smallAdversary : LearningWithErrors.Adversary
        (RLWE.problem q half (2 * samples) secretSampler errorSampler),
      LearningWithErrors.advantage
        (RLWE.problem q half (2 * samples) secretSampler errorSampler)
        smallAdversary ≤ bound)
    (adversary : LearningWithErrors.Adversary
      (evenProblem q half samples secretSampler errorSampler)) :
    LearningWithErrors.advantage
        (evenProblem q half samples secretSampler errorSampler) adversary ≤ bound := by
  rw [advantage_eq_smallRLWE q half samples hhalf]
  exact hsmall _

end

end FormalProof4FHE.RLWE.EvenSecretReduction
