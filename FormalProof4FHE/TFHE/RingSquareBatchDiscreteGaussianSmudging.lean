/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareHeterogeneousCompiler

/-!
# Discrete-Gaussian Full-Batch Smudging for `RGSW_S(-S)`

This file instantiates the full-batch residual interface with the executable certified
coefficientwise discrete-Gaussian sampler.  If every induced upper-row shift has coefficient norm
at most `B`, the genuine stripped-RGSW compiler gap is bounded by

`levels * ringDegree * scalarLinearShiftBound(certificate, B)`.

No assertion is made here that this expression is negligible for a correctness-compatible TFHE
parameter family; that is the remaining quantitative research obligation.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.BatchResidualSmudging.Native

noncomputable section

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

theorem sum_addShiftDistance_discreteGaussian_le
    {q degree levels : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (shift : Fin levels → RLWE.Rq q (degree + 1)) (shiftBound : ℕ)
    (hShift : ∀ level,
      LatticeCrypto.cInfNorm (shift level) ≤ shiftBound) :
    (∑ level : Fin levels,
      FormalProof4FHE.FiniteProduct.addShiftDistance
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        (shift level)) ≤
      (levels : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound) := by
  calc
    (∑ level : Fin levels,
      FormalProof4FHE.FiniteProduct.addShiftDistance
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        (shift level)) ≤
      ∑ _level : Fin levels,
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound) := by
      apply Finset.sum_le_sum
      intro level _
      exact
        DiscreteGaussianSampler.addShiftDistance_ringSampler_le_degree_mul_scalarLinearShiftBound
          (degree + 1) certificate shiftBound (shift level) (hShift level)
    _ = (levels : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound) := by
      simp

theorem tvDist_fixedSecretShiftedSquareBatchSampler_discreteGaussian_le
    {q degree levels : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secret : Fin 1 → RLWE.Rq q (degree + 1))
    (gadget shift : Fin levels → RLWE.Rq q (degree + 1))
    (shiftBound : ℕ)
    (hShift : ∀ level,
      LatticeCrypto.cInfNorm (shift level) ≤ shiftBound) :
    tvDist
        (fixedSecretShiftedSquareBatchSampler levels secret
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          gadget shift)
        (fixedSecretSquareBatchSampler levels secret
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          gadget) ≤
      (levels : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound) := by
  refine (tvDist_fixedSecretShiftedSquareBatchSampler_le_sum levels secret
    (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
    gadget shift).trans ?_
  exact sum_addShiftDistance_discreteGaussian_le certificate shift shiftBound hShift

theorem tvDist_contextualShiftedSquareBatches_discreteGaussian_le
    {q degree levels : ℕ} [NeZero q] {Context : Type}
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (contextSampler : ProbComp Context)
    (secret : Context → Fin 1 → RLWE.Rq q (degree + 1))
    (shift : Context → Fin levels → RLWE.Rq q (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1)) (shiftBound : ℕ)
    (hShift : ∀ context, context ∈ support contextSampler → ∀ level,
      LatticeCrypto.cInfNorm (shift context level) ≤ shiftBound) :
    tvDist
        (contextSampler >>= fun context ↦
          fixedSecretShiftedSquareBatchSampler levels (secret context)
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
            gadget (shift context))
        (contextSampler >>= fun context ↦
          fixedSecretSquareBatchSampler levels (secret context)
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) gadget) ≤
      (levels : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound) := by
  apply tvDist_contextualShiftedSquareBatches_le
  intro context hcontext
  exact sum_addShiftDistance_discreteGaussian_le certificate (shift context)
    shiftBound (hShift context hcontext)

theorem actualDistributionGap_discreteGaussian_le_of_contextual_normalForms
    {q degree levels sourceCount : ℕ} [NeZero q] {Secret Context : Type}
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (selectors : Full.Selectors (RLWE.Rq q (degree + 1)) levels sourceCount)
    (contextSampler : ProbComp Context)
    (contextSecret : Context → Fin 1 → RLWE.Rq q (degree + 1))
    (contextShift : Context → Fin levels → RLWE.Rq q (degree + 1))
    (shiftBound : ℕ)
    (hNative :
      evalDist
          (Full.nativeSquareBatchSampler levels secretSampler embed
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) gadget) =
        evalDist
          (contextSampler >>= fun context ↦
            fixedSecretSquareBatchSampler levels (contextSecret context)
              (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) gadget))
    (hCompiled :
      evalDist
          (Full.compiledBatchSampler levels sourceCount secretSampler embed
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) selectors) =
        evalDist
          (contextSampler >>= fun context ↦
            fixedSecretShiftedSquareBatchSampler levels (contextSecret context)
              (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
              gadget (contextShift context)))
    (hShift : ∀ context, context ∈ support contextSampler → ∀ level,
      LatticeCrypto.cInfNorm (contextShift context level) ≤ shiftBound) :
    Full.actualDistributionGap levels sourceCount secretSampler embed
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) gadget selectors ≤
      (levels : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound) := by
  apply actualDistributionGap_le_of_contextual_normalForms
    levels sourceCount secretSampler embed
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      gadget selectors contextSampler contextSecret contextShift
      ((levels : ℝ) * (((degree + 1 : ℕ) : ℝ) *
        DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound))
      hNative hCompiled
  intro context hcontext
  exact sum_addShiftDistance_discreteGaussian_le certificate
    (contextShift context) shiftBound (hShift context hcontext)

/-- Certified discrete-Gaussian security of the genuine stripped `RGSW_S(-S)` distribution,
stated directly in terms of successful hidden selectors and their induced residual norm. -/
theorem actualDistributionGap_discreteGaussian_le_of_selectorSuccess
    {q degree levels sourceCount : ℕ} [NeZero q] {Secret : Type}
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (selectors : Full.Selectors (RLWE.Rq q (degree + 1)) levels sourceCount)
    (shiftBound : ℕ)
    (hSuccess : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)) →
      ∀ level, Full.SelectorSucceedsAt gadget selectors context.sourceBatch level)
    (hShift : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)) →
      ∀ level,
        LatticeCrypto.cInfNorm
          (@CompilerNormalForm.contextShift (RLWE.Rq q (degree + 1))
            (NoiseBounds.positiveRqCommRing (q := q) (degree := degree))
            levels sourceCount (embed context.secretValue) selectors
            context.sourceBatch level) ≤ shiftBound) :
    Full.actualDistributionGap levels sourceCount secretSampler embed
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) gadget selectors ≤
      (levels : ℝ) *
        (((degree + 1 : ℕ) : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound) := by
  apply CompilerNormalForm.actualDistributionGap_le_of_selectorSuccess
    levels sourceCount secretSampler embed
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      gadget selectors
      ((levels : ℝ) * (((degree + 1 : ℕ) : ℝ) *
        DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound))
      hSuccess
  intro context hcontext
  exact sum_addShiftDistance_discreteGaussian_le certificate
    (@CompilerNormalForm.contextShift (RLWE.Rq q (degree + 1))
      (NoiseBounds.positiveRqCommRing (q := q) (degree := degree))
      levels sourceCount (embed context.secretValue) selectors context.sourceBatch)
    shiftBound (hShift context hcontext)

/-- Standalone `RGSW_S(-S)` distinguishing advantage under the same concrete selector and
discrete-Gaussian residual conditions, reduced to ordinary batch-RLWE. -/
theorem rgswMinusSecretAdvantage_discreteGaussian_le_of_selectorSuccess
    {q degree levels sourceCount : ℕ} [NeZero q] {Secret : Type}
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (selectors : Full.Selectors (RLWE.Rq q (degree + 1)) levels sourceCount)
    (distinguisher : Full.Distinguisher (RLWE.Rq q (degree + 1)) levels)
    (shiftBound : ℕ)
    (hSuccess : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)) →
      ∀ level, Full.SelectorSucceedsAt gadget selectors context.sourceBatch level)
    (hShift : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)) →
      ∀ level,
        LatticeCrypto.cInfNorm
          (@CompilerNormalForm.contextShift (RLWE.Rq q (degree + 1))
            (NoiseBounds.positiveRqCommRing (q := q) (degree := degree))
            levels sourceCount (embed context.secretValue) selectors
            context.sourceBatch level) ≤ shiftBound) :
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) gadget
        distinguisher ≤
      (levels : ℝ) *
          (((degree + 1 : ℕ) : ℝ) *
            DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound) +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate))
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Full.reduction selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  apply CompilerNormalForm.rgswMinusSecretAdvantage_le_selectorResidual_add_batchLWE
    levels sourceCount secretSampler embed
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      gadget selectors distinguisher
      ((levels : ℝ) * (((degree + 1 : ℕ) : ℝ) *
        DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound))
      hSuccess
  intro context hcontext
  exact sum_addShiftDistance_discreteGaussian_le certificate
    (@CompilerNormalForm.contextShift (RLWE.Rq q (degree + 1))
      (NoiseBounds.positiveRqCommRing (q := q) (degree := degree))
      levels sourceCount (embed context.secretValue) selectors context.sourceBatch)
    shiftBound (hShift context hcontext)

/-- Failure-aware certified distribution bound.  A selector may fail rarely; successful contexts
need only satisfy the induced-shift norm bound. -/
theorem actualDistributionGap_discreteGaussian_le_failure_add_shift
    {q degree levels sourceCount : ℕ} [NeZero q] {Secret : Type}
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (selectors : Full.Selectors (RLWE.Rq q (degree + 1)) levels sourceCount)
    (shiftBound : ℕ)
    (hShift : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      ∀ level,
        LatticeCrypto.cInfNorm
          (@CompilerNormalForm.contextShift (RLWE.Rq q (degree + 1))
            (NoiseBounds.positiveRqCommRing (q := q) (degree := degree))
            levels sourceCount (embed context.secretValue) selectors
            context.sourceBatch level) ≤ shiftBound) :
    Full.actualDistributionGap levels sourceCount secretSampler embed
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) gadget selectors ≤
      Pr[fun context ↦ ¬ CompilerNormalForm.SelectorsSucceed gadget selectors context |
          CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)].toReal +
        (levels : ℝ) *
          (((degree + 1 : ℕ) : ℝ) *
            DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound) := by
  apply CompilerNormalForm.actualDistributionGap_le_failure_add_selectorResidual
    levels sourceCount secretSampler embed
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      gadget selectors
      ((levels : ℝ) * (((degree + 1 : ℕ) : ℝ) *
        DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound))
  · exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _)
        (DiscreteGaussianSampler.scalarLinearShiftBound_nonneg certificate shiftBound))
  · intro context hcontext hSuccess
    exact sum_addShiftDistance_discreteGaussian_le certificate
      (@CompilerNormalForm.contextShift (RLWE.Rq q (degree + 1))
        (NoiseBounds.positiveRqCommRing (q := q) (degree := degree))
        levels sourceCount (embed context.secretValue) selectors context.sourceBatch)
      shiftBound (hShift context hcontext hSuccess)

/-- Final failure-aware standalone theorem for the genuine `RGSW_S(-S)` object. -/
theorem rgswMinusSecretAdvantage_discreteGaussian_le_failure_add_shift_add_batchLWE
    {q degree levels sourceCount : ℕ} [NeZero q] {Secret : Type}
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (selectors : Full.Selectors (RLWE.Rq q (degree + 1)) levels sourceCount)
    (distinguisher : Full.Distinguisher (RLWE.Rq q (degree + 1)) levels)
    (shiftBound : ℕ)
    (hShift : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      ∀ level,
        LatticeCrypto.cInfNorm
          (@CompilerNormalForm.contextShift (RLWE.Rq q (degree + 1))
            (NoiseBounds.positiveRqCommRing (q := q) (degree := degree))
            levels sourceCount (embed context.secretValue) selectors
            context.sourceBatch level) ≤ shiftBound) :
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) gadget
        distinguisher ≤
      (Pr[fun context ↦ ¬ CompilerNormalForm.SelectorsSucceed gadget selectors context |
            CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
              (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)].toReal +
          (levels : ℝ) *
            (((degree + 1 : ℕ) : ℝ) *
              DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound)) +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate))
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Full.reduction selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  apply CompilerNormalForm.rgswMinusSecretAdvantage_le_failure_add_residual_add_batchLWE
    levels sourceCount secretSampler embed
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      gadget selectors distinguisher
      ((levels : ℝ) * (((degree + 1 : ℕ) : ℝ) *
        DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound))
  · exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _)
        (DiscreteGaussianSampler.scalarLinearShiftBound_nonneg certificate shiftBound))
  · intro context hcontext hSuccess
    exact sum_addShiftDistance_discreteGaussian_le certificate
      (@CompilerNormalForm.contextShift (RLWE.Rq q (degree + 1))
        (NoiseBounds.positiveRqCommRing (q := q) (degree := degree))
        levels sourceCount (embed context.secretValue) selectors context.sourceBatch)
      shiftBound (hShift context hcontext hSuccess)

/-- Heterogeneous widened-noise endpoint.  Hidden source rows retain an arbitrary narrow error
law, while genuine RGSW rows use its exact convolution with the certified discrete Gaussian.
Only the widening Gaussian pays the residual translation cost, and the computational term is
ordinary batch-RLWE with the narrow source law. -/
theorem rgswMinusSecretAdvantage_widenedDiscreteGaussian_le_failure_add_shift_add_batchLWE
    {q degree levels sourceCount : ℕ} [NeZero q] {Secret : Type}
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (selectors : Full.Selectors (RLWE.Rq q (degree + 1)) levels sourceCount)
    (distinguisher : Full.Distinguisher (RLWE.Rq q (degree + 1)) levels)
    (shiftBound : ℕ)
    (hShift : ∀ context,
      context ∈ support
        (CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
          sourceErrorSampler) →
      CompilerNormalForm.SelectorsSucceed gadget selectors context →
      ∀ level,
        LatticeCrypto.cInfNorm
          (@CompilerNormalForm.contextShift (RLWE.Rq q (degree + 1))
            (NoiseBounds.positiveRqCommRing (q := q) (degree := degree))
            levels sourceCount (embed context.secretValue) selectors
            context.sourceBatch level) ≤ shiftBound) :
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (Heterogeneous.convolutionSampler sourceErrorSampler
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate))
        gadget distinguisher ≤
      (Pr[fun context ↦
            ¬ CompilerNormalForm.SelectorsSucceed gadget selectors context |
          CompilerNormalForm.contextSampler levels sourceCount secretSampler embed
            sourceErrorSampler].toReal +
          (levels : ℝ) *
            (((degree + 1 : ℕ) : ℝ) *
              DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound)) +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed sourceErrorSampler)
          (LWE.TwoBlock.convolutionReduction
            (secondErrorSampler := Heterogeneous.convolutionSampler sourceErrorSampler
              (DiscreteGaussianSampler.ringSampler (degree + 1) certificate))
            (extraErrorSampler :=
              DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
            (Heterogeneous.reduction
              (targetErrorSampler := Heterogeneous.convolutionSampler sourceErrorSampler
                (DiscreteGaussianSampler.ringSampler (degree + 1) certificate))
              selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  apply Heterogeneous.rgswMinusSecretAdvantage_le_convolution_failure_add_residual_add_batchLWE
    levels sourceCount secretSampler embed sourceErrorSampler
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      gadget selectors distinguisher
      ((levels : ℝ) * (((degree + 1 : ℕ) : ℝ) *
        DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound))
  · exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _)
        (DiscreteGaussianSampler.scalarLinearShiftBound_nonneg certificate shiftBound))
  · intro context hcontext hSuccess
    exact sum_addShiftDistance_discreteGaussian_le certificate
      (@CompilerNormalForm.contextShift (RLWE.Rq q (degree + 1))
        (NoiseBounds.positiveRqCommRing (q := q) (degree := degree))
        levels sourceCount (embed context.secretValue) selectors context.sourceBatch)
      shiftBound (hShift context hcontext hSuccess)
  · simp

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.BatchResidualSmudging.Native
