/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareCompilerNormalForm

/-!
# Failure-Aware Hidden Compiler Bound for `RGSW_S(-S)`

An efficient short-preimage procedure may fail on a small fraction of ordinary-RLWE source
contexts.  This file removes the support-wide selector-success premise: bad contexts are charged
by their exact probability, while successful contexts pay only their induced residual translation
cost.  The resulting standalone bound has precisely three terms: selector failure, residual
smudging, and ordinary batch-RLWE advantage.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.CompilerNormalForm

noncomputable section

/-- All level-wise inhomogeneous gadget-preimage equations hold in one hidden source context. -/
def SelectorsSucceed {R Secret : Type} [CommRing R]
    {levels sourceCount : ℕ} (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : Context R Secret levels sourceCount) : Prop :=
  ∀ level, Full.SelectorSucceedsAt gadget selectors context.sourceBatch level

/-- Rare selector failures add only their probability to the contextual residual-smudging bound. -/
theorem tvDist_contextualCompiler_native_le_failure_add_bound
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount) (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hShift : ∀ context,
      context ∈ support
        (contextSampler levels sourceCount secretSampler embed errorSampler) →
      SelectorsSucceed gadget selectors context →
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler
          (contextShift (embed context.secretValue) selectors context.sourceBatch level)) ≤
        bound) :
    tvDist
        (contextSampler levels sourceCount secretSampler embed errorSampler >>=
          compileFromContext embed errorSampler selectors)
        (contextSampler levels sourceCount secretSampler embed errorSampler >>=
          fun context ↦
            BatchResidualSmudging.fixedSecretSquareBatchSampler levels
              (embed context.secretValue) errorSampler gadget) ≤
      Pr[fun context ↦ ¬ SelectorsSucceed gadget selectors context |
        contextSampler levels sourceCount secretSampler embed errorSampler].toReal + bound := by
  classical
  let ContextSampler :=
    contextSampler levels sourceCount secretSampler embed errorSampler
  let Native := fun context : Context R Secret levels sourceCount ↦
    BatchResidualSmudging.fixedSecretSquareBatchSampler levels
      (embed context.secretValue) errorSampler gadget
  let Shifted := fun context : Context R Secret levels sourceCount ↦
    BatchResidualSmudging.fixedSecretShiftedSquareBatchSampler levels
      (embed context.secretValue) errorSampler gadget
      (contextShift (embed context.secretValue) selectors context.sourceBatch)
  let Hybrid := fun context : Context R Secret levels sourceCount ↦
    if SelectorsSucceed gadget selectors context then Shifted context else Native context
  have hFailure :
      tvDist
          (ContextSampler >>= compileFromContext embed errorSampler selectors)
          (ContextSampler >>= Hybrid) ≤
        Pr[fun context ↦ ¬ SelectorsSucceed gadget selectors context |
          ContextSampler].toReal := by
    apply tvDist_bind_left_event_le ContextSampler
      (compileFromContext embed errorSampler selectors) Hybrid
      (fun context ↦ ¬ SelectorsSucceed gadget selectors context)
    intro context hNotBad
    have hSuccess : SelectorsSucceed gadget selectors context := not_not.mp hNotBad
    simp only [Hybrid, hSuccess, if_true]
    exact compileFromContext_evalDist_eq_shifted embed errorSampler gadget selectors context
      hSuccess
  have hSmudging :
      tvDist (ContextSampler >>= Hybrid) (ContextSampler >>= Native) ≤ bound := by
    apply tvDist_bind_left_le_const ContextSampler Hybrid Native bound
    intro context hcontext
    by_cases hSuccess : SelectorsSucceed gadget selectors context
    · simp only [Hybrid, hSuccess, if_true]
      exact
        (BatchResidualSmudging.tvDist_fixedSecretShiftedSquareBatchSampler_le_sum
          levels (embed context.secretValue) errorSampler gadget
          (contextShift (embed context.secretValue) selectors context.sourceBatch)).trans
          (hShift context hcontext hSuccess)
    · simp only [Hybrid, hSuccess, if_false]
      simpa only [tvDist_self] using hBoundNonneg
  calc
    tvDist
        (contextSampler levels sourceCount secretSampler embed errorSampler >>=
          compileFromContext embed errorSampler selectors)
        (contextSampler levels sourceCount secretSampler embed errorSampler >>=
          fun context ↦
            BatchResidualSmudging.fixedSecretSquareBatchSampler levels
              (embed context.secretValue) errorSampler gadget) ≤
      tvDist
          (ContextSampler >>= compileFromContext embed errorSampler selectors)
          (ContextSampler >>= Hybrid) +
        tvDist (ContextSampler >>= Hybrid) (ContextSampler >>= Native) := by
      simpa only [ContextSampler, Native] using
        tvDist_triangle
          (ContextSampler >>= compileFromContext embed errorSampler selectors)
          (ContextSampler >>= Hybrid) (ContextSampler >>= Native)
    _ ≤ Pr[fun context ↦ ¬ SelectorsSucceed gadget selectors context |
          ContextSampler].toReal + bound := add_le_add hFailure hSmudging
    _ = Pr[fun context ↦ ¬ SelectorsSucceed gadget selectors context |
          contextSampler levels sourceCount secretSampler embed errorSampler].toReal +
        bound := by rfl

/-- The genuine stripped distribution gap allows rare selector failure, charged additively. -/
theorem actualDistributionGap_le_failure_add_selectorResidual
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount) (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hShift : ∀ context,
      context ∈ support
        (contextSampler levels sourceCount secretSampler embed errorSampler) →
      SelectorsSucceed gadget selectors context →
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler
          (contextShift (embed context.secretValue) selectors context.sourceBatch level)) ≤
        bound) :
    Full.actualDistributionGap levels sourceCount secretSampler embed errorSampler gadget
        selectors ≤
      Pr[fun context ↦ ¬ SelectorsSucceed gadget selectors context |
        contextSampler levels sourceCount secretSampler embed errorSampler].toReal + bound := by
  have hContext := tvDist_contextualCompiler_native_le_failure_add_bound
    levels sourceCount secretSampler embed errorSampler gadget selectors bound
    hBoundNonneg hShift
  rw [ActualNormalForm.actualDistributionGap_eq_nativeDistributionGap]
  unfold Full.nativeDistributionGap tvDist at hContext ⊢
  rw [nativeSquareBatchSampler_evalDist_eq_contextual,
    compiledBatchSampler_evalDist_eq_contextual]
  simpa only [SPMF.tvDist_comm] using hContext

/-- Failure-aware standalone security: rare selector failure, successful residual smudging, and
ordinary batch-RLWE are the only three terms. -/
theorem rgswMinusSecretAdvantage_le_failure_add_residual_add_batchLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hShift : ∀ context,
      context ∈ support
        (contextSampler levels sourceCount secretSampler embed errorSampler) →
      SelectorsSucceed gadget selectors context →
      (∑ level : Fin levels,
        FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler
          (contextShift (embed context.secretValue) selectors context.sourceBatch level)) ≤
        bound) :
    Full.rgswMinusSecretAdvantage levels secretSampler embed errorSampler gadget
        distinguisher ≤
      (Pr[fun context ↦ ¬ SelectorsSucceed gadget selectors context |
          contextSampler levels sourceCount secretSampler embed errorSampler].toReal + bound) +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Full.reduction selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  exact
    (Full.rgswMinusSecretAdvantage_le_actualDistributionGap_add_batchLWE
      levels sourceCount secretSampler embed errorSampler gadget selectors
        distinguisher).trans
      (add_le_add
        (actualDistributionGap_le_failure_add_selectorResidual
          levels sourceCount secretSampler embed errorSampler gadget selectors bound
          hBoundNonneg hShift)
        le_rfl)

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.CompilerNormalForm
