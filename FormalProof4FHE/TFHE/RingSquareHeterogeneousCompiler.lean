/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.TwoBlockConvolution
import FormalProof4FHE.TFHE.RingSquareCompilerFailure

/-!
# Heterogeneous-Noise Compiler Security for `RGSW_S(-S)`

The hidden source rows used to synthesize the square term need not have the same error law as the
emitted RGSW rows.  This file proves the exact two-block compiler normal form with narrow source
noise and independently wider target noise.  If target noise is the convolution of source noise
and a total widening sampler, the heterogeneous LWE term reduces exactly to ordinary batch-LWE
with the narrow source law.

The final finite-parameter theorem charges selector failure, translation distance under only the
widening component, and ordinary batch-RLWE.  This avoids the quantitative self-reference of a
same-width Gaussian simultaneously generating and hiding the compiler residual.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.Heterogeneous

noncomputable section

/-- Exact scalar convolution sampler used for the wider emitted RGSW error. -/
def convolutionSampler {R : Type} [Add R]
    (sourceErrorSampler extraErrorSampler : ProbComp R) : ProbComp R := do
  let sourceError ← sourceErrorSampler
  let extraError ← extraErrorSampler
  return sourceError + extraError

/-- The explicit convolution sampler satisfies the reduction premise definitionally. -/
theorem scalarErrorConvolution_convolutionSampler
    {R : Type} [Add R]
    (sourceErrorSampler extraErrorSampler : ProbComp R) :
    FormalProof4FHE.SharedRandomness.ScalarErrorConvolution
      (convolutionSampler sourceErrorSampler extraErrorSampler)
      sourceErrorSampler extraErrorSampler := by
  rfl

/-- Adding independent source noise cannot increase the translation distance of the wider
component. -/
theorem addShiftDistance_convolutionSampler_le_right
    {R : Type} [AddCommGroup R] [Finite R]
    (sourceErrorSampler extraErrorSampler : ProbComp R) (shift : R) :
    FormalProof4FHE.FiniteProduct.addShiftDistance
        (convolutionSampler sourceErrorSampler extraErrorSampler) shift ≤
      FormalProof4FHE.FiniteProduct.addShiftDistance extraErrorSampler shift := by
  unfold FormalProof4FHE.FiniteProduct.addShiftDistance convolutionSampler
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply tvDist_bind_left_le_const'
  intro sourceError
  have hdata := tvDist_map_le (m := ProbComp) (fun value : R ↦ sourceError + value)
    ((fun value ↦ shift + value) <$> extraErrorSampler) extraErrorSampler
  simpa only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def, add_assoc, add_left_comm, add_comm] using hdata

/-- Compiler output when hidden source rows and emitted target rows use distinct error laws. -/
def compiledBatchSampler {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount) :
    ProbComp (Full.TargetBatch R levels) := do
  let transcript ← LearningWithErrors.distr
    (LWE.TwoBlock.heterogeneousProblem 1 (levels * sourceCount)
      (TGSW.rowCount 1 levels) secretSampler embed sourceErrorSampler targetErrorSampler)
  return Full.compileTranscript selectors transcript

/-- The heterogeneous real experiment is exactly the hidden-source contextual compiler sampler. -/
theorem compiledBatchSampler_evalDist_eq_contextual
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount) :
    evalDist
        (compiledBatchSampler levels sourceCount secretSampler embed
          sourceErrorSampler targetErrorSampler selectors) =
      evalDist
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
            sourceErrorSampler >>=
          CompilerNormalForm.compileFromContext embed targetErrorSampler selectors) := by
  let SourceChallenges : ProbComp
      (Matrix (Fin 1) (Fin (levels * sourceCount)) R) :=
    $ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R
  let TargetChallenges : ProbComp
      (Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :=
    $ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R
  let SourceErrors : ProbComp (Fin (levels * sourceCount) → R) :=
    ProbComp.sampleIID (levels * sourceCount) sourceErrorSampler
  let TargetErrors : ProbComp (Fin (TGSW.rowCount 1 levels) → R) :=
    ProbComp.sampleIID (TGSW.rowCount 1 levels) targetErrorSampler
  let finish := fun
      (sourceChallenge : Matrix (Fin 1) (Fin (levels * sourceCount)) R)
      (targetChallenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
      (secretValue : Secret)
      (sourceError : Fin (levels * sourceCount) → R)
      (targetError : Fin (TGSW.rowCount 1 levels) → R) ↦
    (pure (Full.compileTargets selectors
      (TLWE.batchAssemble (embed secretValue) sourceChallenge 0 sourceError)
      (TLWE.batchAssemble (embed secretValue) targetChallenge 0 targetError)) :
        ProbComp (Full.TargetBatch R levels))
  have uniformChallenge :
      ($ᵗ (LWE.TwoBlock.Challenge R 1 (levels * sourceCount)
          (TGSW.rowCount 1 levels)) :
        ProbComp (LWE.TwoBlock.Challenge R 1 (levels * sourceCount)
          (TGSW.rowCount 1 levels))) =
        Prod.mk <$> SourceChallenges <*> TargetChallenges := by
    rfl
  have hCompiled :
      compiledBatchSampler levels sourceCount secretSampler embed
          sourceErrorSampler targetErrorSampler selectors =
        (SourceChallenges >>= fun sourceChallenge ↦
          TargetChallenges >>= fun targetChallenge ↦
            secretSampler >>= fun secretValue ↦
              SourceErrors >>= fun sourceError ↦
                TargetErrors >>= fun targetError ↦
                  finish sourceChallenge targetChallenge secretValue sourceError targetError) := by
    rw [show
      compiledBatchSampler levels sourceCount secretSampler embed
          sourceErrorSampler targetErrorSampler selectors =
        (LearningWithErrors.distr
          (LWE.TwoBlock.heterogeneousProblem 1 (levels * sourceCount)
            (TGSW.rowCount 1 levels) secretSampler embed
            sourceErrorSampler targetErrorSampler) >>=
          fun transcript ↦ pure (Full.compileTranscript selectors transcript)) by rfl]
    unfold LearningWithErrors.distr LWE.TwoBlock.heterogeneousProblem
    rw [uniformChallenge]
    simp [Full.compileTranscript, Full.transcriptPairEquiv,
      LWE.TwoBlock.toTranscriptPair, SourceChallenges, TargetChallenges,
      SourceErrors, TargetErrors, finish, TLWE.batchAssemble, monad_norm]
  have hContext :
      CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler >>=
          CompilerNormalForm.compileFromContext embed targetErrorSampler selectors =
        (SourceChallenges >>= fun sourceChallenge ↦
          secretSampler >>= fun secretValue ↦
            SourceErrors >>= fun sourceError ↦
              TargetChallenges >>= fun targetChallenge ↦
                TargetErrors >>= fun targetError ↦
                  finish sourceChallenge targetChallenge secretValue sourceError targetError) := by
    simp [CompilerNormalForm.contextSampler, CompilerNormalForm.compileFromContext,
      SourceChallenges, TargetChallenges, SourceErrors, TargetErrors,
      finish, TLWE.batchAssemble, monad_norm]
  rw [hCompiled, hContext]
  apply evalDist_bind_congr' SourceChallenges
  intro sourceChallenge
  calc
    evalDist (TargetChallenges >>= fun targetChallenge ↦
        secretSampler >>= fun secretValue ↦
          SourceErrors >>= fun sourceError ↦
            TargetErrors >>= fun targetError ↦
              finish sourceChallenge targetChallenge secretValue sourceError targetError) =
      evalDist (secretSampler >>= fun secretValue ↦
        TargetChallenges >>= fun targetChallenge ↦
          SourceErrors >>= fun sourceError ↦
            TargetErrors >>= fun targetError ↦
              finish sourceChallenge targetChallenge secretValue sourceError targetError) := by
        exact evalDist_bind_bind_swap TargetChallenges secretSampler _
    _ = evalDist (secretSampler >>= fun secretValue ↦
        SourceErrors >>= fun sourceError ↦
          TargetChallenges >>= fun targetChallenge ↦
            TargetErrors >>= fun targetError ↦
              finish sourceChallenge targetChallenge secretValue sourceError targetError) := by
      apply evalDist_bind_congr' secretSampler
      intro secretValue
      exact evalDist_bind_bind_swap TargetChallenges SourceErrors _

/-- Hidden source rows may use any error law: since they are discarded by the native branch,
sampling them does not alter a target-noise native square batch. -/
theorem nativeSquareBatchSampler_evalDist_eq_contextual
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (gadget : Fin levels → R) :
    evalDist
        (Full.nativeSquareBatchSampler levels secretSampler embed targetErrorSampler gadget) =
      evalDist
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
            sourceErrorSampler >>=
          fun context ↦
            BatchResidualSmudging.fixedSecretSquareBatchSampler levels
              (embed context.secretValue) targetErrorSampler gadget) := by
  let SourceChallenges : ProbComp
      (Matrix (Fin 1) (Fin (levels * sourceCount)) R) :=
    $ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R
  let SourceErrors : ProbComp (Fin (levels * sourceCount) → R) :=
    ProbComp.sampleIID (levels * sourceCount) sourceErrorSampler
  let Native := fun secretValue ↦
    BatchResidualSmudging.fixedSecretSquareBatchSampler levels
      (embed secretValue) targetErrorSampler gadget
  have hNative :
      Full.nativeSquareBatchSampler levels secretSampler embed targetErrorSampler gadget =
        (secretSampler >>= Native) := by
    rfl
  have hContext :
      CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler >>=
          (fun context ↦ Native context.secretValue) =
        (SourceChallenges >>= fun _sourceChallenge ↦
          secretSampler >>= fun secretValue ↦
            SourceErrors >>= fun _sourceError ↦ Native secretValue) := by
    simp [CompilerNormalForm.contextSampler, SourceChallenges, SourceErrors,
      Native, monad_norm]
  rw [hNative, hContext]
  have hDrop (secretValue : Secret) :
      evalDist
          (SourceChallenges >>= fun _sourceChallenge ↦
            SourceErrors >>= fun _sourceError ↦ Native secretValue) =
        evalDist (Native secretValue) := by
    calc
      _ = evalDist (SourceChallenges >>= fun _sourceChallenge ↦ Native secretValue) := by
        apply evalDist_bind_congr' SourceChallenges
        intro _sourceChallenge
        exact
          FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
            SourceErrors (by simp [SourceErrors]) (Native secretValue)
      _ = evalDist (Native secretValue) :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          SourceChallenges (by simp [SourceChallenges]) (Native secretValue)
  calc
    evalDist (secretSampler >>= Native) =
        evalDist (secretSampler >>= fun secretValue ↦
          SourceChallenges >>= fun _sourceChallenge ↦
            SourceErrors >>= fun _sourceError ↦ Native secretValue) := by
      symm
      exact evalDist_bind_congr' secretSampler hDrop
    _ = evalDist (SourceChallenges >>= fun _sourceChallenge ↦
          secretSampler >>= fun secretValue ↦
            SourceErrors >>= fun _sourceError ↦ Native secretValue) := by
      exact (evalDist_bind_bind_swap SourceChallenges secretSampler
        (fun _sourceChallenge secretValue ↦
          SourceErrors >>= fun _sourceError ↦ Native secretValue)).symm

/-- Failure-aware heterogeneous smudging: only the target error law pays translation distance,
while the induced shift is generated by the independent source error law. -/
theorem tvDist_contextualCompiler_native_le_failure_add_bound
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount) (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hShift : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance targetErrorSampler
          (CompilerNormalForm.contextShift (embed context.secretValue) selectors
            context.sourceBatch level)) ≤ bound) :
    tvDist
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
            sourceErrorSampler >>=
          CompilerNormalForm.compileFromContext embed targetErrorSampler selectors)
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
            sourceErrorSampler >>=
          fun context ↦
            BatchResidualSmudging.fixedSecretSquareBatchSampler levels
              (embed context.secretValue) targetErrorSampler gadget) ≤
      Pr[fun context ↦
          ¬ CompilerNormalForm.SelectorsSucceed gadget selectors context |
        CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler].toReal + bound := by
  classical
  let ContextSampler :=
    CompilerNormalForm.contextSampler levels sourceCount secretSampler embed sourceErrorSampler
  let Native := fun context : CompilerNormalForm.Context R Secret levels sourceCount ↦
    BatchResidualSmudging.fixedSecretSquareBatchSampler levels
      (embed context.secretValue) targetErrorSampler gadget
  let Shifted := fun context : CompilerNormalForm.Context R Secret levels sourceCount ↦
    BatchResidualSmudging.fixedSecretShiftedSquareBatchSampler levels
      (embed context.secretValue) targetErrorSampler gadget
      (CompilerNormalForm.contextShift (embed context.secretValue) selectors
        context.sourceBatch)
  let Hybrid := fun context : CompilerNormalForm.Context R Secret levels sourceCount ↦
    if CompilerNormalForm.SelectorsSucceed gadget selectors context
    then Shifted context else Native context
  have hFailure :
      tvDist
          (ContextSampler >>=
            CompilerNormalForm.compileFromContext embed targetErrorSampler selectors)
          (ContextSampler >>= Hybrid) ≤
        Pr[fun context ↦
          ¬ CompilerNormalForm.SelectorsSucceed gadget selectors context |
          ContextSampler].toReal := by
    apply tvDist_bind_left_event_le ContextSampler
      (CompilerNormalForm.compileFromContext embed targetErrorSampler selectors) Hybrid
      (fun context ↦ ¬ CompilerNormalForm.SelectorsSucceed gadget selectors context)
    intro context hNotBad
    have hSuccess : CompilerNormalForm.SelectorsSucceed gadget selectors context :=
      not_not.mp hNotBad
    simp only [Hybrid, hSuccess, if_true]
    exact CompilerNormalForm.compileFromContext_evalDist_eq_shifted embed
      targetErrorSampler gadget selectors context hSuccess
  have hSmudging :
      tvDist (ContextSampler >>= Hybrid) (ContextSampler >>= Native) ≤ bound := by
    apply tvDist_bind_left_le_const ContextSampler Hybrid Native bound
    intro context hcontext
    by_cases hSuccess : CompilerNormalForm.SelectorsSucceed gadget selectors context
    · simp only [Hybrid, hSuccess, if_true]
      exact
        (BatchResidualSmudging.tvDist_fixedSecretShiftedSquareBatchSampler_le_sum
          levels (embed context.secretValue) targetErrorSampler gadget
          (CompilerNormalForm.contextShift (embed context.secretValue) selectors
            context.sourceBatch)).trans
          (hShift context hcontext hSuccess)
    · simp only [Hybrid, hSuccess, if_false]
      simpa only [tvDist_self] using hBoundNonneg
  calc
    _ ≤ tvDist
          (ContextSampler >>=
            CompilerNormalForm.compileFromContext embed targetErrorSampler selectors)
          (ContextSampler >>= Hybrid) +
        tvDist (ContextSampler >>= Hybrid) (ContextSampler >>= Native) := by
      simpa only [ContextSampler, Native] using
        tvDist_triangle
          (ContextSampler >>=
            CompilerNormalForm.compileFromContext embed targetErrorSampler selectors)
          (ContextSampler >>= Hybrid) (ContextSampler >>= Native)
    _ ≤ Pr[fun context ↦
          ¬ CompilerNormalForm.SelectorsSucceed gadget selectors context |
          ContextSampler].toReal + bound := add_le_add hFailure hSmudging
    _ = _ := by rfl

/-- Genuine stripped-square distance from the heterogeneous hidden compiler. -/
noncomputable def actualDistributionGap {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount) : ℝ :=
  tvDist
    (Full.actualSquareBatchSampler levels secretSampler embed targetErrorSampler gadget)
    (compiledBatchSampler levels sourceCount secretSampler embed
      sourceErrorSampler targetErrorSampler selectors)

/-- The heterogeneous genuine gap is controlled by selector failure and target-noise smudging. -/
theorem actualDistributionGap_le_failure_add_selectorResidual
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount) (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hShift : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance targetErrorSampler
          (CompilerNormalForm.contextShift (embed context.secretValue) selectors
            context.sourceBatch level)) ≤ bound) :
    actualDistributionGap levels sourceCount secretSampler embed
        sourceErrorSampler targetErrorSampler gadget selectors ≤
      Pr[fun context ↦
          ¬ CompilerNormalForm.SelectorsSucceed gadget selectors context |
        CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler].toReal + bound := by
  have hContext := tvDist_contextualCompiler_native_le_failure_add_bound
    levels sourceCount secretSampler embed sourceErrorSampler targetErrorSampler
    gadget selectors bound hBoundNonneg hShift
  unfold actualDistributionGap tvDist at hContext ⊢
  rw [ActualNormalForm.actualSquareBatchSampler_evalDist_eq_nativeSquareBatchSampler,
    nativeSquareBatchSampler_evalDist_eq_contextual,
    compiledBatchSampler_evalDist_eq_contextual]
  simpa only [SPMF.tvDist_comm] using hContext

/-- Deterministic compiler reduction against heterogeneous unequal two-block LWE. -/
def reduction {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    {levels sourceCount : ℕ} {secretSampler : ProbComp Secret}
    {embed : Secret → Fin 1 → R}
    {sourceErrorSampler targetErrorSampler : ProbComp R}
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) :
    LearningWithErrors.Adversary
      (LWE.TwoBlock.heterogeneousProblem 1 (levels * sourceCount)
        (TGSW.rowCount 1 levels) secretSampler embed
        sourceErrorSampler targetErrorSampler) :=
  fun transcript ↦ distinguisher (Full.compileTranscript selectors transcript)

/-- Real heterogeneous compiler game. -/
def realGame {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) : ProbComp Bool :=
  LearningWithErrors.game0
    (LWE.TwoBlock.heterogeneousProblem 1 (levels * sourceCount)
      (TGSW.rowCount 1 levels) secretSampler embed
      sourceErrorSampler targetErrorSampler)
    (reduction selectors distinguisher)

/-- Heterogeneous compiler real-versus-uniform advantage. -/
noncomputable def advantage {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) : ℝ :=
  (realGame levels sourceCount secretSampler embed sourceErrorSampler
      targetErrorSampler selectors distinguisher).boolDistAdvantage
    (Full.uniformGame distinguisher)

theorem realGame_eq_compiledBatchSampler_bind
    {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) :
    realGame levels sourceCount secretSampler embed sourceErrorSampler
        targetErrorSampler selectors distinguisher =
      compiledBatchSampler levels sourceCount secretSampler embed
        sourceErrorSampler targetErrorSampler selectors >>= distinguisher := by
  simp [realGame, compiledBatchSampler, LearningWithErrors.game0, reduction,
    bind_assoc, monad_norm]

/-- The heterogeneous compiler's uniform branch remains the canonical uniform RGSW carrier. -/
theorem reduction_game1_evalDist_eq_uniformGame
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) :
    evalDist
        (LearningWithErrors.game1
          (LWE.TwoBlock.heterogeneousProblem 1 (levels * sourceCount)
            (TGSW.rowCount 1 levels) secretSampler embed
            sourceErrorSampler targetErrorSampler)
          (reduction selectors distinguisher)) =
      evalDist (Full.uniformGame distinguisher) := by
  rw [LearningWithErrors.game1,
    LWE.TwoBlock.heterogeneousUniformDistr_eq_uniformSample]
  simp only [reduction, Full.uniformGame]
  rw [show
      (($ᵗ (Full.InputTranscript R levels sourceCount)) >>= fun transcript ↦
        distinguisher (Full.compileTranscript selectors transcript)) =
        ((Full.compileTranscript selectors <$>
          ($ᵗ (Full.InputTranscript R levels sourceCount))) >>= distinguisher) by
      simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, Full.compileTranscript_uniform_evalDist, ← evalDist_bind]

/-- Exact heterogeneous compiler reduction to unequal two-block LWE. -/
theorem advantage_eq_twoBlockLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) :
    advantage levels sourceCount secretSampler embed sourceErrorSampler
        targetErrorSampler selectors distinguisher =
      LearningWithErrors.advantage
        (LWE.TwoBlock.heterogeneousProblem 1 (levels * sourceCount)
          (TGSW.rowCount 1 levels) secretSampler embed
          sourceErrorSampler targetErrorSampler)
        (reduction selectors distinguisher) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold advantage ProbComp.boolDistAdvantage realGame
  rw [evalDist_ext_iff.mp
    (reduction_game1_evalDist_eq_uniformGame levels sourceCount secretSampler embed
      sourceErrorSampler targetErrorSampler selectors distinguisher) true]

/-- If target noise is source noise plus an independent widening law, the heterogeneous compiler
reduces exactly to ordinary batch-LWE with the narrow source noise. -/
theorem advantage_eq_batchLWE_of_convolution
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler extraErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels)
    (hConvolution : FormalProof4FHE.SharedRandomness.ScalarErrorConvolution
      targetErrorSampler sourceErrorSampler extraErrorSampler)
    (hExtra : Pr[⊥ | extraErrorSampler] = 0) :
    advantage levels sourceCount secretSampler embed sourceErrorSampler
        targetErrorSampler selectors distinguisher =
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.embeddedBatchProblem 1
          (levels * sourceCount + TGSW.rowCount 1 levels)
          secretSampler embed sourceErrorSampler)
        (LWE.TwoBlock.convolutionReduction
          (secondErrorSampler := targetErrorSampler)
          (extraErrorSampler := extraErrorSampler)
          (reduction (targetErrorSampler := targetErrorSampler)
            selectors distinguisher)) := by
  rw [advantage_eq_twoBlockLWE levels sourceCount secretSampler embed
    sourceErrorSampler targetErrorSampler selectors distinguisher]
  exact LWE.TwoBlock.heterogeneous_advantage_eq_batch_of_convolution
    1 (levels * sourceCount) (TGSW.rowCount 1 levels)
    secretSampler embed sourceErrorSampler targetErrorSampler extraErrorSampler
    hConvolution hExtra
      (reduction (targetErrorSampler := targetErrorSampler) selectors distinguisher)

/-- Genuine stripped-square security from the heterogeneous gap plus heterogeneous LWE. -/
theorem actualSquareAdvantage_le_actualDistributionGap_add_twoBlockLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) :
    Full.actualSquareAdvantage levels secretSampler embed targetErrorSampler gadget
        distinguisher ≤
      actualDistributionGap levels sourceCount secretSampler embed
          sourceErrorSampler targetErrorSampler gadget selectors +
        LearningWithErrors.advantage
          (LWE.TwoBlock.heterogeneousProblem 1 (levels * sourceCount)
            (TGSW.rowCount 1 levels) secretSampler embed
            sourceErrorSampler targetErrorSampler)
          (reduction selectors distinguisher) := by
  have hTriangle := ProbComp.boolDistAdvantage_triangle
    (Full.actualSquareGame levels secretSampler embed targetErrorSampler gadget distinguisher)
    (realGame levels sourceCount secretSampler embed sourceErrorSampler
      targetErrorSampler selectors distinguisher)
    (Full.uniformGame distinguisher)
  have hComparison :
      (Full.actualSquareGame levels secretSampler embed targetErrorSampler gadget
          distinguisher).boolDistAdvantage
          (realGame levels sourceCount secretSampler embed sourceErrorSampler
            targetErrorSampler selectors distinguisher) ≤
        actualDistributionGap levels sourceCount secretSampler embed
          sourceErrorSampler targetErrorSampler gadget selectors := by
    refine (abs_probOutput_toReal_sub_le_tvDist _ _).trans ?_
    rw [Full.actualSquareGame,
      realGame_eq_compiledBatchSampler_bind levels sourceCount secretSampler embed
        sourceErrorSampler targetErrorSampler selectors distinguisher]
    exact tvDist_bind_right_le distinguisher
      (Full.actualSquareBatchSampler levels secretSampler embed targetErrorSampler gadget)
      (compiledBatchSampler levels sourceCount secretSampler embed
        sourceErrorSampler targetErrorSampler selectors)
  have hCompiler := advantage_eq_twoBlockLWE levels sourceCount secretSampler embed
    sourceErrorSampler targetErrorSampler selectors distinguisher
  calc
    Full.actualSquareAdvantage levels secretSampler embed targetErrorSampler gadget
        distinguisher ≤
      (Full.actualSquareGame levels secretSampler embed targetErrorSampler gadget
        distinguisher).boolDistAdvantage
          (realGame levels sourceCount secretSampler embed sourceErrorSampler
            targetErrorSampler selectors distinguisher) +
        advantage levels sourceCount secretSampler embed sourceErrorSampler
          targetErrorSampler selectors distinguisher := by
      simpa only [Full.actualSquareAdvantage, advantage] using hTriangle
    _ ≤ actualDistributionGap levels sourceCount secretSampler embed
          sourceErrorSampler targetErrorSampler gadget selectors +
        advantage levels sourceCount secretSampler embed sourceErrorSampler
          targetErrorSampler selectors distinguisher := add_le_add hComparison le_rfl
    _ = _ := by rw [hCompiler]

/-- Genuine unstripped `RGSW_S(-S)` security under the heterogeneous two-block problem. -/
theorem rgswMinusSecretAdvantage_le_actualDistributionGap_add_twoBlockLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) :
    Full.rgswMinusSecretAdvantage levels secretSampler embed targetErrorSampler gadget
        distinguisher ≤
      actualDistributionGap levels sourceCount secretSampler embed
          sourceErrorSampler targetErrorSampler gadget selectors +
        LearningWithErrors.advantage
          (LWE.TwoBlock.heterogeneousProblem 1 (levels * sourceCount)
            (TGSW.rowCount 1 levels) secretSampler embed
            sourceErrorSampler targetErrorSampler)
          (reduction selectors (Full.restoreDistinguisher gadget distinguisher)) := by
  rw [Full.rgswMinusSecretAdvantage_eq_actualSquareAdvantage_restore]
  exact actualSquareAdvantage_le_actualDistributionGap_add_twoBlockLWE
    levels sourceCount secretSampler embed sourceErrorSampler targetErrorSampler
    gadget selectors (Full.restoreDistinguisher gadget distinguisher)

/-- Convolution turns the heterogeneous security term into ordinary batch-RLWE with the narrow
source error law. -/
theorem rgswMinusSecretAdvantage_le_actualDistributionGap_add_batchLWE_of_convolution
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler extraErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels)
    (hConvolution : FormalProof4FHE.SharedRandomness.ScalarErrorConvolution
      targetErrorSampler sourceErrorSampler extraErrorSampler)
    (hExtra : Pr[⊥ | extraErrorSampler] = 0) :
    Full.rgswMinusSecretAdvantage levels secretSampler embed targetErrorSampler gadget
        distinguisher ≤
      actualDistributionGap levels sourceCount secretSampler embed
          sourceErrorSampler targetErrorSampler gadget selectors +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed sourceErrorSampler)
          (LWE.TwoBlock.convolutionReduction
            (secondErrorSampler := targetErrorSampler)
            (extraErrorSampler := extraErrorSampler)
            (reduction (targetErrorSampler := targetErrorSampler)
              selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  have hCompiler := advantage_eq_batchLWE_of_convolution
    levels sourceCount secretSampler embed sourceErrorSampler targetErrorSampler
    extraErrorSampler selectors (Full.restoreDistinguisher gadget distinguisher)
    hConvolution hExtra
  have hTwoBlock := advantage_eq_twoBlockLWE
    levels sourceCount secretSampler embed sourceErrorSampler targetErrorSampler
    selectors (Full.restoreDistinguisher gadget distinguisher)
  calc
    _ ≤ actualDistributionGap levels sourceCount secretSampler embed
          sourceErrorSampler targetErrorSampler gadget selectors +
        LearningWithErrors.advantage
          (LWE.TwoBlock.heterogeneousProblem 1 (levels * sourceCount)
            (TGSW.rowCount 1 levels) secretSampler embed
            sourceErrorSampler targetErrorSampler)
          (reduction selectors (Full.restoreDistinguisher gadget distinguisher)) :=
      rgswMinusSecretAdvantage_le_actualDistributionGap_add_twoBlockLWE
        levels sourceCount secretSampler embed sourceErrorSampler targetErrorSampler
        gadget selectors distinguisher
    _ = _ := by rw [← hTwoBlock, hCompiler]

/-- Main finite-parameter heterogeneous theorem.  The three statistical/computational costs are
selector failure, residual translation under the wider target noise, and ordinary narrow-noise
batch-RLWE. -/
theorem rgswMinusSecretAdvantage_le_failure_add_residual_add_batchLWE_of_convolution
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler extraErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hShift : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance targetErrorSampler
          (CompilerNormalForm.contextShift (embed context.secretValue) selectors
            context.sourceBatch level)) ≤ bound)
    (hConvolution : FormalProof4FHE.SharedRandomness.ScalarErrorConvolution
      targetErrorSampler sourceErrorSampler extraErrorSampler)
    (hExtra : Pr[⊥ | extraErrorSampler] = 0) :
    Full.rgswMinusSecretAdvantage levels secretSampler embed targetErrorSampler gadget
        distinguisher ≤
      (Pr[fun context ↦
            ¬ CompilerNormalForm.SelectorsSucceed gadget selectors context |
          CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
            sourceErrorSampler].toReal + bound) +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed sourceErrorSampler)
          (LWE.TwoBlock.convolutionReduction
            (secondErrorSampler := targetErrorSampler)
            (extraErrorSampler := extraErrorSampler)
            (reduction (targetErrorSampler := targetErrorSampler)
              selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  exact
    (rgswMinusSecretAdvantage_le_actualDistributionGap_add_batchLWE_of_convolution
      levels sourceCount secretSampler embed sourceErrorSampler targetErrorSampler
      extraErrorSampler gadget selectors distinguisher hConvolution hExtra).trans
      (add_le_add
        (actualDistributionGap_le_failure_add_selectorResidual
          levels sourceCount secretSampler embed sourceErrorSampler targetErrorSampler
          gadget selectors bound hBoundNonneg hShift)
        le_rfl)

/-- Canonical widened-noise endpoint: emitted RGSW noise is exactly the convolution of source
noise and an independent wider component.  Its residual cost is bounded solely using the wider
component. -/
theorem rgswMinusSecretAdvantage_le_convolution_failure_add_residual_add_batchLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler extraErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hShift : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance extraErrorSampler
          (CompilerNormalForm.contextShift (embed context.secretValue) selectors
            context.sourceBatch level)) ≤ bound)
    (hExtra : Pr[⊥ | extraErrorSampler] = 0) :
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (convolutionSampler sourceErrorSampler extraErrorSampler) gadget distinguisher ≤
      (Pr[fun context ↦
            ¬ CompilerNormalForm.SelectorsSucceed gadget selectors context |
          CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
            sourceErrorSampler].toReal + bound) +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed sourceErrorSampler)
          (LWE.TwoBlock.convolutionReduction
            (secondErrorSampler := convolutionSampler sourceErrorSampler extraErrorSampler)
            (extraErrorSampler := extraErrorSampler)
            (reduction
              (targetErrorSampler :=
                convolutionSampler sourceErrorSampler extraErrorSampler)
              selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  apply rgswMinusSecretAdvantage_le_failure_add_residual_add_batchLWE_of_convolution
    levels sourceCount secretSampler embed sourceErrorSampler
      (convolutionSampler sourceErrorSampler extraErrorSampler) extraErrorSampler
      gadget selectors distinguisher bound hBoundNonneg
  · intro context hcontext hSuccess
    refine (Finset.sum_le_sum fun level _ ↦
      addShiftDistance_convolutionSampler_le_right sourceErrorSampler extraErrorSampler
        (CompilerNormalForm.contextShift (embed context.secretValue) selectors
          context.sourceBatch level)).trans ?_
    exact hShift context hcontext hSuccess
  · exact scalarErrorConvolution_convolutionSampler
      sourceErrorSampler extraErrorSampler
  · exact hExtra

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.Heterogeneous
