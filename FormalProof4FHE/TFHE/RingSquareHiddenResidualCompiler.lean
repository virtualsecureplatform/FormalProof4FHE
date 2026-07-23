/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareHeterogeneousCompiler
import FormalProof4FHE.Probability.ConditionalCollision

/-!
# Hidden-Residual Compiler Security for `RGSW_S(-S)`

The public short-preimage selector used by the ring-square compiler depends only on the source
masks.  The ordinary-RLWE source errors are sampled independently after those masks and are not
part of the published compiled ciphertext.  Consequently, conditioning on the complete source
batch is unnecessarily lossy: it reveals the compiler residual and turns a random convolution
problem into a worst-case fixed-translation problem.

This file factors the hidden compiler context into a mask/secret prefix and a subsequently sampled
source-error table.  On successful masks, the conditional compiler law is a fresh square batch
whose target errors are translated by the still-hidden random residual

`S * sum_i x_i e_i`.

The finite security theorem therefore charges the exact total-variation distance after mixing over
the source errors.  No pointwise norm bound or fixed-shift hybrid is used.  Analytically bounding
this hidden-residual distance for correctness-compatible noise is isolated as the remaining
small-noise problem.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.HiddenResidual

noncomputable section

/-! ## Generic hidden-shift convolution lemmas -/

/-- Sum two independent additive samples. -/
def independentSumSampler {G : Type} [Add G]
    (left right : ProbComp G) : ProbComp G := do
  let leftValue ← left
  let rightValue ← right
  return leftValue + rightValue

/-- Mix over a hidden random shift before adding independent noise. -/
def randomShiftSampler {G : Type} [Add G]
    (shiftSampler errorSampler : ProbComp G) : ProbComp G :=
  independentSumSampler shiftSampler errorSampler

/-- Adding the same independent random value to two distributions contracts total variation. -/
theorem tvDist_independentSumSampler_left_le
    {G : Type} [Add G]
    (common left right : ProbComp G) :
    tvDist
        (independentSumSampler common left)
        (independentSumSampler common right) ≤
      tvDist left right := by
  unfold independentSumSampler
  apply tvDist_bind_left_le_const'
  intro commonValue
  let addCommon := fun value : G ↦ commonValue + value
  calc
    tvDist
        (left >>= fun value ↦ pure (addCommon value))
        (right >>= fun value ↦ pure (addCommon value)) =
      tvDist (addCommon <$> left) (addCommon <$> right) := by
        simp [addCommon, monad_norm]
    _ ≤ tvDist left right := tvDist_map_le (m := ProbComp) addCommon left right

/-- Replacing the error sampler by a distributionally equal sampler preserves the complete
hidden-shift mixture. -/
theorem evalDist_randomShiftSampler_congr_right
    {G : Type} [Add G]
    (shiftSampler left right : ProbComp G)
    (hError : evalDist left = evalDist right) :
    evalDist (randomShiftSampler shiftSampler left) =
      evalDist (randomShiftSampler shiftSampler right) := by
  unfold randomShiftSampler independentSumSampler
  apply evalDist_bind_congr'
  intro shift
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    (evalDist_map_eq_of_evalDist_eq hError (fun error ↦ shift + error))

/-- A common independent convolution component can only help hide a random additive shift. -/
theorem tvDist_randomShiftSampler_independentSum_le_right
    {G : Type} [AddCommGroup G]
    (shiftSampler common wide : ProbComp G) :
    tvDist
        (randomShiftSampler shiftSampler
          (independentSumSampler common wide))
        (independentSumSampler common wide) ≤
      tvDist (randomShiftSampler shiftSampler wide) wide := by
  have hReorder :
      evalDist
          (randomShiftSampler shiftSampler
            (independentSumSampler common wide)) =
        evalDist
          (independentSumSampler common
            (randomShiftSampler shiftSampler wide)) := by
    unfold randomShiftSampler independentSumSampler
    simp only [bind_assoc, pure_bind]
    calc
      evalDist (shiftSampler >>= fun shift ↦
          common >>= fun commonValue ↦
            wide >>= fun wideValue ↦
              pure (shift + (commonValue + wideValue))) =
        evalDist (common >>= fun commonValue ↦
          shiftSampler >>= fun shift ↦
            wide >>= fun wideValue ↦
              pure (shift + (commonValue + wideValue))) :=
        evalDist_bind_bind_swap shiftSampler common _
      _ = evalDist (common >>= fun commonValue ↦
          shiftSampler >>= fun shift ↦
            wide >>= fun wideValue ↦
              pure (commonValue + (shift + wideValue))) := by
        apply evalDist_bind_congr'
        intro commonValue
        apply evalDist_bind_congr'
        intro shift
        apply evalDist_bind_congr'
        intro wideValue
        congr 2
        abel
  unfold tvDist
  rw [hReorder]
  exact tvDist_independentSumSampler_left_le common
    (randomShiftSampler shiftSampler wide) wide

/-- The part of the hidden compiler context fixed before source errors are sampled.  A selector
may inspect `sourceChallenge`, but neither it nor the eventual distinguisher receives the source
errors retained by the reduction. -/
structure MaskContext (R Secret : Type) (levels sourceCount : ℕ) where
  sourceChallenge : Matrix (Fin 1) (Fin (levels * sourceCount)) R
  secretValue : Secret

/-- Sample the uniform source masks and the shared secret, but not the ordinary-RLWE source
errors. -/
def maskContextSampler {R Secret : Type}
    [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret) :
    ProbComp (MaskContext R Secret levels sourceCount) := do
  let sourceChallenge ←
    $ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R
  let secretValue ← secretSampler
  return ⟨sourceChallenge, secretValue⟩

/-- The independent table of source errors sampled after a mask context has been fixed. -/
def sourceErrorTableSampler {R : Type} (levels sourceCount : ℕ)
    (sourceErrorSampler : ProbComp R) :
    ProbComp (Fin (levels * sourceCount) → R) :=
  ProbComp.sampleIID (levels * sourceCount) sourceErrorSampler

/-- Assemble the hidden ordinary-RLWE source batch from a mask context and an independent error
table. -/
def sourceBatchFrom {R Secret : Type} [Semiring R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (context : MaskContext R Secret levels sourceCount)
    (sourceError : Fin (levels * sourceCount) → R) :
    Full.SourceBatch R levels sourceCount :=
  TLWE.batchAssemble (embed context.secretValue) context.sourceChallenge 0 sourceError

/-- Reconstitute the older complete context after the independent source errors are sampled. -/
def compilerContextFrom {R Secret : Type} [Semiring R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (context : MaskContext R Secret levels sourceCount)
    (sourceError : Fin (levels * sourceCount) → R) :
    CompilerNormalForm.Context R Secret levels sourceCount :=
  ⟨context.secretValue, sourceBatchFrom embed context sourceError⟩

/-- Success of every level selector is a predicate of the public challenge alone.  The zero body
is merely a canonical way to package that challenge as a source batch. -/
def ChallengeSelectorsSucceed {R : Type} [CommRing R]
    {levels sourceCount : ℕ} (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (challenge : Matrix (Fin 1) (Fin (levels * sourceCount)) R) : Prop :=
  ∀ level,
    Full.SelectorSucceedsAt gadget selectors (challenge, 0) level

/-- Assembling arbitrary source errors does not change the selector-success predicate. -/
theorem selectorsSucceed_compilerContextFrom_iff
    {R Secret : Type} [CommRing R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount)
    (sourceError : Fin (levels * sourceCount) → R) :
    CompilerNormalForm.SelectorsSucceed gadget selectors
        (compilerContextFrom embed context sourceError) ↔
      ChallengeSelectorsSucceed gadget selectors context.sourceChallenge := by
  rfl

/-- The exact vector of compiler residuals generated from a fixed mask/secret prefix and a hidden
source-error table. -/
def residualShift {R Secret : Type} [CommRing R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount)
    (sourceError : Fin (levels * sourceCount) → R) : Fin levels → R :=
  CompilerNormalForm.contextShift (embed context.secretValue) selectors
    (sourceBatchFrom embed context sourceError)

/-- Algebraic form of the hidden residual: the selector weights are functions only of the public
masks, while the summands are the still-independent source errors. -/
theorem residualShift_eq_secret_mul_weightedSourceErrors
    {R Secret : Type} [CommRing R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount)
    (sourceError : Fin (levels * sourceCount) → R)
    (level : Fin levels) :
    residualShift embed selectors context sourceError level =
      embed context.secretValue 0 *
        ∑ source : Fin sourceCount,
          selectors level
              (fun index ↦ context.sourceChallenge 0 (finProdFinEquiv (level, index)))
              source *
            sourceError (finProdFinEquiv (level, source)) := by
  classical
  unfold residualShift CompilerNormalForm.contextShift
    ResidualSmudging.inducedShift
  rw [phase_preimageCombination_eq_weighted]
  rw [show
      sourceMasks
          (Full.sourceRowsAt
            (sourceBatchFrom embed context sourceError) level) =
        (fun index ↦
          context.sourceChallenge 0 (finProdFinEquiv (level, index))) by
    rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro source _hsource
  simp [sourceBatchFrom, Full.sourceRowsAt]

/-- The whole upper-row residual vector, sampled before any fresh target errors. -/
def residualVectorSampler {R Secret : Type} [CommRing R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) :
    ProbComp (Fin (TGSW.rowCount 1 levels) → R) :=
  (fun sourceError ↦
      BatchResidualSmudging.upperShiftVector
        (residualShift embed selectors context sourceError)) <$>
    sourceErrorTableSampler levels sourceCount sourceErrorSampler

/-- Sample hidden source errors, fresh target errors, and add the induced residual only to the
upper square row at every gadget level. -/
def hiddenShiftedBatchErrorSampler {R Secret : Type} [CommRing R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) :
    ProbComp (Fin (TGSW.rowCount 1 levels) → R) := do
  let sourceError ← sourceErrorTableSampler levels sourceCount sourceErrorSampler
  let targetError ← ProbComp.sampleIID (TGSW.rowCount 1 levels) targetErrorSampler
  return fun row ↦
    BatchResidualSmudging.upperShiftVector
        (residualShift embed selectors context sourceError) row + targetError row

/-- The hidden batch-error law is a random-shift mixture whose shift sampler is precisely the
residual vector generated by the independent source errors. -/
theorem hiddenShiftedBatchErrorSampler_evalDist_eq_randomShift
    {R Secret : Type} [CommRing R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) :
    evalDist
        (hiddenShiftedBatchErrorSampler embed sourceErrorSampler targetErrorSampler
          selectors context) =
      evalDist
        (randomShiftSampler
          (residualVectorSampler embed sourceErrorSampler selectors context)
          (ProbComp.sampleIID (TGSW.rowCount 1 levels) targetErrorSampler)) := by
  apply congrArg evalDist
  unfold hiddenShiftedBatchErrorSampler residualVectorSampler
    randomShiftSampler independentSumSampler sourceErrorTableSampler
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  apply bind_congr
  intro sourceError
  apply bind_congr
  intro targetError
  congr 2

/-- Coordinatewise scalar convolution is exactly vector convolution after independent product
sampling. -/
theorem sampleIID_convolutionSampler_evalDist
    {R : Type} [Finite R] [Add R]
    (count : ℕ) (left right : ProbComp R) :
    evalDist
        (ProbComp.sampleIID count
          (Heterogeneous.convolutionSampler left right)) =
      evalDist
        (independentSumSampler
          (ProbComp.sampleIID count left)
          (ProbComp.sampleIID count right)) := by
  calc
    _ = evalDist (do
        let leftValues ← ProbComp.sampleIID count left
        let rightValues ← ProbComp.sampleIID count right
        return fun index ↦ leftValues index + rightValues index) := by
      simpa only [Heterogeneous.convolutionSampler] using
        (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_add_convolution
          count left right)
    _ = _ := by
      apply congrArg evalDist
      unfold independentSumSampler
      apply bind_congr
      intro leftValues
      apply bind_congr
      intro rightValues
      congr 2

/-- The exact statistical cost after the source-error residual has been mixed, rather than
conditioned on and revealed. -/
noncomputable def hiddenResidualDistance {R Secret : Type} [CommRing R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) : ℝ :=
  tvDist
    (hiddenShiftedBatchErrorSampler embed sourceErrorSampler targetErrorSampler
      selectors context)
    (ProbComp.sampleIID (TGSW.rowCount 1 levels) targetErrorSampler)

/-- An unconditional finite `L²` upper-bound target for the hidden-residual distance.  This form
remains sound for executable Gaussian tables that assign probability zero to some residues. -/
noncomputable def hiddenResidualL2Loss {R Secret : Type} [CommRing R] [Fintype R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) : ℝ :=
  FormalProof4FHE.ConditionalCollision.l2Loss
    (hiddenShiftedBatchErrorSampler embed sourceErrorSampler targetErrorSampler
      selectors context)
    (ProbComp.sampleIID (TGSW.rowCount 1 levels) targetErrorSampler)

/-- The exact hidden-residual TV term is controlled by its explicit finite `L²` loss without an
absolute-continuity premise. -/
theorem hiddenResidualDistance_le_l2Loss
    {R Secret : Type} [CommRing R] [Fintype R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) :
    hiddenResidualDistance embed sourceErrorSampler targetErrorSampler selectors context ≤
      hiddenResidualL2Loss embed sourceErrorSampler targetErrorSampler selectors context := by
  exact FormalProof4FHE.ConditionalCollision.tvDist_le_l2Loss _ _

/-- Pearson chi-square form of the same random-convolution obligation.  It is sharper than the
unweighted `L²` loss when the widening sampler has full support. -/
noncomputable def hiddenResidualPearsonChiSquare
    {R Secret : Type} [CommRing R] [Fintype R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) : ℝ :=
  FormalProof4FHE.ConditionalCollision.pearsonChiSquare
    (hiddenShiftedBatchErrorSampler embed sourceErrorSampler targetErrorSampler
      selectors context)
    (ProbComp.sampleIID (TGSW.rowCount 1 levels) targetErrorSampler)

/-- Pearson chi-square controls the hidden-residual distance whenever the mixed residual law is
absolutely continuous with respect to the widening-error law. -/
theorem hiddenResidualDistance_le_sqrt_pearsonChiSquare_div_two
    {R Secret : Type} [CommRing R] [Fintype R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount)
    (hAbsolutelyContinuous : ∀ value : Fin (TGSW.rowCount 1 levels) → R,
      Pr[= value | ProbComp.sampleIID (TGSW.rowCount 1 levels) targetErrorSampler].toReal = 0 →
        Pr[= value |
          hiddenShiftedBatchErrorSampler embed sourceErrorSampler targetErrorSampler
            selectors context].toReal = 0) :
    hiddenResidualDistance embed sourceErrorSampler targetErrorSampler selectors context ≤
      Real.sqrt
          (hiddenResidualPearsonChiSquare embed sourceErrorSampler targetErrorSampler
            selectors context) /
        2 := by
  exact FormalProof4FHE.ConditionalCollision.tvDist_le_sqrt_pearsonChiSquare_div_two
    _ _ hAbsolutelyContinuous

/-- Any independent component already present in the target-error convolution can only decrease
the exact hidden-residual distance.  Thus the analytic obligation may be discharged using only
the widening component. -/
theorem hiddenResidualDistance_convolutionSampler_le_right
    {R Secret : Type}
    [CommRing R] [Fintype R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler commonErrorSampler wideningSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) :
    hiddenResidualDistance embed sourceErrorSampler
        (Heterogeneous.convolutionSampler commonErrorSampler wideningSampler)
        selectors context ≤
      hiddenResidualDistance embed sourceErrorSampler wideningSampler
        selectors context := by
  let ShiftSampler :=
    residualVectorSampler embed sourceErrorSampler selectors context
  let CommonSampler :=
    ProbComp.sampleIID (TGSW.rowCount 1 levels) commonErrorSampler
  let WideSampler :=
    ProbComp.sampleIID (TGSW.rowCount 1 levels) wideningSampler
  let ConvolvedSampler :=
    ProbComp.sampleIID (TGSW.rowCount 1 levels)
      (Heterogeneous.convolutionSampler commonErrorSampler wideningSampler)
  have hTarget :
      evalDist ConvolvedSampler =
        evalDist (independentSumSampler CommonSampler WideSampler) := by
    exact sampleIID_convolutionSampler_evalDist
      (TGSW.rowCount 1 levels) commonErrorSampler wideningSampler
  have hShiftedConvolved :
      evalDist
          (hiddenShiftedBatchErrorSampler embed sourceErrorSampler
            (Heterogeneous.convolutionSampler commonErrorSampler wideningSampler)
            selectors context) =
        evalDist (randomShiftSampler ShiftSampler ConvolvedSampler) := by
    exact hiddenShiftedBatchErrorSampler_evalDist_eq_randomShift
      embed sourceErrorSampler
        (Heterogeneous.convolutionSampler commonErrorSampler wideningSampler)
      selectors context
  have hShiftedWide :
      evalDist
          (hiddenShiftedBatchErrorSampler embed sourceErrorSampler wideningSampler
            selectors context) =
        evalDist (randomShiftSampler ShiftSampler WideSampler) := by
    exact hiddenShiftedBatchErrorSampler_evalDist_eq_randomShift
      embed sourceErrorSampler wideningSampler selectors context
  have hShiftedTarget :
      evalDist (randomShiftSampler ShiftSampler ConvolvedSampler) =
        evalDist
          (randomShiftSampler ShiftSampler
            (independentSumSampler CommonSampler WideSampler)) :=
    evalDist_randomShiftSampler_congr_right
      ShiftSampler ConvolvedSampler
        (independentSumSampler CommonSampler WideSampler) hTarget
  unfold hiddenResidualDistance tvDist
  rw [hShiftedConvolved, hShiftedTarget, hTarget, hShiftedWide]
  simpa only [tvDist, ShiftSampler, CommonSampler, WideSampler] using
    (tvDist_randomShiftSampler_independentSum_le_right
      ShiftSampler CommonSampler WideSampler)

theorem hiddenResidualDistance_nonneg
    {R Secret : Type} [CommRing R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) :
    0 ≤ hiddenResidualDistance embed sourceErrorSampler targetErrorSampler
      selectors context :=
  SPMF.tvDist_nonneg _ _

theorem hiddenResidualDistance_le_one
    {R Secret : Type} [CommRing R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) :
    hiddenResidualDistance embed sourceErrorSampler targetErrorSampler
      selectors context ≤ 1 :=
  SPMF.tvDist_le_one _ _

/-- The square-batch normal form in which the residual-generating source errors remain internal to
the error sampler. -/
def hiddenShiftedSquareBatchSampler
    {R Secret : Type} [CommRing R] [SampleableType R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) :
    ProbComp (Full.TargetBatch R levels) := do
  let targetChallenge ←
    $ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R
  let outputError ←
    hiddenShiftedBatchErrorSampler embed sourceErrorSampler targetErrorSampler
      selectors context
  return TLWE.batchAssemble (embed context.secretValue) targetChallenge
    (Full.squareMessages (embed context.secretValue) gadget) outputError

/-- Fresh challenge sampling and deterministic ciphertext assembly cannot increase the exact
hidden-residual error distance. -/
theorem tvDist_hiddenShiftedSquareBatchSampler_le_hiddenResidualDistance
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) :
    tvDist
        (hiddenShiftedSquareBatchSampler embed sourceErrorSampler targetErrorSampler
          gadget selectors context)
        (BatchResidualSmudging.fixedSecretSquareBatchSampler levels
          (embed context.secretValue) targetErrorSampler gadget) ≤
      hiddenResidualDistance embed sourceErrorSampler targetErrorSampler
        selectors context := by
  unfold hiddenShiftedSquareBatchSampler
    BatchResidualSmudging.fixedSecretSquareBatchSampler TLWE.batchEncrypt
  apply tvDist_bind_left_le_const'
  intro targetChallenge
  let assemble := fun error ↦
    TLWE.batchAssemble (embed context.secretValue) targetChallenge
      (Full.squareMessages (embed context.secretValue) gadget) error
  calc
    tvDist
        (hiddenShiftedBatchErrorSampler embed sourceErrorSampler targetErrorSampler
            selectors context >>=
          pure ∘ assemble)
        (ProbComp.sampleIID (TGSW.rowCount 1 levels) targetErrorSampler >>=
          pure ∘ assemble) =
      tvDist
        (assemble <$>
          hiddenShiftedBatchErrorSampler embed sourceErrorSampler targetErrorSampler
            selectors context)
        (assemble <$>
          ProbComp.sampleIID (TGSW.rowCount 1 levels) targetErrorSampler) := by
      simp [assemble, monad_norm]
    _ ≤ tvDist
        (hiddenShiftedBatchErrorSampler embed sourceErrorSampler targetErrorSampler
          selectors context)
        (ProbComp.sampleIID (TGSW.rowCount 1 levels) targetErrorSampler) :=
      tvDist_map_le (m := ProbComp) assemble _ _
    _ = hiddenResidualDistance embed sourceErrorSampler targetErrorSampler
        selectors context := rfl

/-- Sample the source errors hidden behind one fixed mask/secret context and run the ordinary
compiler conditional on the resulting complete source batch. -/
def compileFromMaskContext
    {R Secret : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) :
    ProbComp (Full.TargetBatch R levels) := do
  let sourceError ← sourceErrorTableSampler levels sourceCount sourceErrorSampler
  CompilerNormalForm.compileFromContext embed targetErrorSampler selectors
    (compilerContextFrom embed context sourceError)

/-- Moving the independent source-error draw across the fresh target challenge gives exactly the
hidden-residual square-batch sampler. -/
theorem sourceErrors_bind_shifted_evalDist_eq_hiddenShifted
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount) :
    evalDist
        (sourceErrorTableSampler levels sourceCount sourceErrorSampler >>= fun sourceError ↦
          BatchResidualSmudging.fixedSecretShiftedSquareBatchSampler levels
            (embed context.secretValue) targetErrorSampler gadget
            (residualShift embed selectors context sourceError)) =
      evalDist
        (hiddenShiftedSquareBatchSampler embed sourceErrorSampler targetErrorSampler
          gadget selectors context) := by
  let SourceErrors := sourceErrorTableSampler levels sourceCount sourceErrorSampler
  let TargetChallenges : ProbComp
      (Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R) :=
    $ᵗ Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R
  let TargetErrors := ProbComp.sampleIID (TGSW.rowCount 1 levels) targetErrorSampler
  let finish := fun
      (sourceError : Fin (levels * sourceCount) → R)
      (targetChallenge : Matrix (Fin 1) (Fin (TGSW.rowCount 1 levels)) R)
      (targetError : Fin (TGSW.rowCount 1 levels) → R) ↦
    (pure (TLWE.batchAssemble (embed context.secretValue) targetChallenge
        (Full.squareMessages (embed context.secretValue) gadget)
        (fun row ↦
          BatchResidualSmudging.upperShiftVector
              (residualShift embed selectors context sourceError) row + targetError row)) :
      ProbComp (Full.TargetBatch R levels))
  have hLeft :
      (sourceErrorTableSampler levels sourceCount sourceErrorSampler >>= fun sourceError ↦
          BatchResidualSmudging.fixedSecretShiftedSquareBatchSampler levels
            (embed context.secretValue) targetErrorSampler gadget
            (residualShift embed selectors context sourceError)) =
        (SourceErrors >>= fun sourceError ↦
          TargetChallenges >>= fun targetChallenge ↦
            TargetErrors >>= fun targetError ↦
              finish sourceError targetChallenge targetError) := by
    simp [SourceErrors, TargetChallenges, TargetErrors, finish,
      BatchResidualSmudging.fixedSecretShiftedSquareBatchSampler,
      BatchResidualSmudging.shiftedBatchErrorSampler, monad_norm]
  have hRight :
      hiddenShiftedSquareBatchSampler embed sourceErrorSampler targetErrorSampler
          gadget selectors context =
        (TargetChallenges >>= fun targetChallenge ↦
          SourceErrors >>= fun sourceError ↦
            TargetErrors >>= fun targetError ↦
              finish sourceError targetChallenge targetError) := by
    simp [hiddenShiftedSquareBatchSampler, hiddenShiftedBatchErrorSampler,
      sourceErrorTableSampler, SourceErrors, TargetChallenges, TargetErrors,
      finish, monad_norm]
  rw [hLeft, hRight]
  exact evalDist_bind_bind_swap SourceErrors TargetChallenges
    (fun sourceError targetChallenge ↦
      TargetErrors >>= fun targetError ↦
        finish sourceError targetChallenge targetError)

/-- On successful public masks, the compiler with hidden source errors has exactly the mixed
hidden-residual square-batch law. -/
theorem compileFromMaskContext_evalDist_eq_hiddenShifted
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount)
    (hSuccess : ChallengeSelectorsSucceed gadget selectors context.sourceChallenge) :
    evalDist
        (compileFromMaskContext embed sourceErrorSampler targetErrorSampler
          selectors context) =
      evalDist
        (hiddenShiftedSquareBatchSampler embed sourceErrorSampler targetErrorSampler
          gadget selectors context) := by
  unfold compileFromMaskContext
  calc
    evalDist
        (sourceErrorTableSampler levels sourceCount sourceErrorSampler >>= fun sourceError ↦
          CompilerNormalForm.compileFromContext embed targetErrorSampler selectors
            (compilerContextFrom embed context sourceError)) =
      evalDist
        (sourceErrorTableSampler levels sourceCount sourceErrorSampler >>= fun sourceError ↦
          BatchResidualSmudging.fixedSecretShiftedSquareBatchSampler levels
            (embed context.secretValue) targetErrorSampler gadget
            (residualShift embed selectors context sourceError)) := by
      apply evalDist_bind_congr'
      intro sourceError
      apply CompilerNormalForm.compileFromContext_evalDist_eq_shifted
      exact (selectorsSucceed_compilerContextFrom_iff
        embed gadget selectors context sourceError).mpr hSuccess
    _ = _ := sourceErrors_bind_shifted_evalDist_eq_hiddenShifted
      embed sourceErrorSampler targetErrorSampler gadget selectors context

/-! ## Complete hidden-context normal forms -/

/-- The heterogeneous ordinary-RLWE compiler factors exactly through the mask/secret prefix and
the later hidden source-error draw. -/
theorem compiledBatchSampler_evalDist_eq_maskContextual
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount) :
    evalDist
        (Heterogeneous.compiledBatchSampler levels sourceCount secretSampler embed
          sourceErrorSampler targetErrorSampler selectors) =
      evalDist
        (maskContextSampler (R := R) levels sourceCount secretSampler >>= fun context ↦
          compileFromMaskContext embed sourceErrorSampler targetErrorSampler
            selectors context) := by
  rw [Heterogeneous.compiledBatchSampler_evalDist_eq_contextual]
  apply congrArg evalDist
  simp [CompilerNormalForm.contextSampler, maskContextSampler,
    compileFromMaskContext, sourceErrorTableSampler, compilerContextFrom,
    sourceBatchFrom, monad_norm]

/-- Sampling unused source masks around the native square batch does not alter its distribution.
Unlike the old complete context, this normal form introduces no source-error draw. -/
theorem nativeSquareBatchSampler_evalDist_eq_maskContextual
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R) (targetErrorSampler : ProbComp R)
    (gadget : Fin levels → R) :
    evalDist
        (Full.nativeSquareBatchSampler levels secretSampler embed
          targetErrorSampler gadget) =
      evalDist
        (maskContextSampler (R := R) levels sourceCount secretSampler >>= fun context ↦
          BatchResidualSmudging.fixedSecretSquareBatchSampler levels
            (embed context.secretValue) targetErrorSampler gadget) := by
  let SourceChallenges : ProbComp
      (Matrix (Fin 1) (Fin (levels * sourceCount)) R) :=
    $ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R
  let Native := fun secretValue ↦
    BatchResidualSmudging.fixedSecretSquareBatchSampler levels
      (embed secretValue) targetErrorSampler gadget
  have hNative :
      Full.nativeSquareBatchSampler levels secretSampler embed
          targetErrorSampler gadget =
        (secretSampler >>= Native) := by
    rfl
  have hMask :
      (maskContextSampler (R := R) levels sourceCount secretSampler >>= fun context ↦
          BatchResidualSmudging.fixedSecretSquareBatchSampler levels
            (embed context.secretValue) targetErrorSampler gadget) =
        (SourceChallenges >>= fun _sourceChallenge ↦
          secretSampler >>= Native) := by
    simp [maskContextSampler, SourceChallenges, Native, monad_norm]
  rw [hNative, hMask]
  exact
    (FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      SourceChallenges (by simp [SourceChallenges]) (secretSampler >>= Native)).symm

/-- Extending a public challenge by a possibly failing secret sampler cannot increase the
probability of a selector failure that depends only on that challenge. -/
theorem maskContextSelectors_failure_le_challenge
    {R Secret : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount) :
    Pr[(fun context ↦
        ¬ ChallengeSelectorsSucceed gadget selectors context.sourceChallenge) |
      maskContextSampler (R := R) levels sourceCount secretSampler] ≤
      Pr[(fun challenge : Matrix (Fin 1) (Fin (levels * sourceCount)) R ↦
          ¬ ChallengeSelectorsSucceed gadget selectors challenge) |
        ($ᵗ Matrix (Fin 1) (Fin (levels * sourceCount)) R)] := by
  let Challenge := Matrix (Fin 1) (Fin (levels * sourceCount)) R
  let challengeSampler : ProbComp Challenge := $ᵗ Challenge
  let continuation : Challenge → ProbComp (MaskContext R Secret levels sourceCount) :=
    fun challenge ↦ do
      let secretValue ← secretSampler
      return ⟨challenge, secretValue⟩
  have hMaskSampler :
      maskContextSampler (R := R) levels sourceCount secretSampler =
        challengeSampler >>= continuation := by
    rfl
  rw [hMaskSampler]
  apply probEvent_bind_le_probEvent
  intro challenge _hChallenge hgood
  rw [probEvent_eq_zero_iff]
  intro context hcontext hfailure
  unfold continuation at hcontext
  rw [mem_support_bind_iff] at hcontext
  obtain ⟨secretValue, _hSecret, hcontext⟩ := hcontext
  simp only [support_pure, Set.mem_singleton_iff] at hcontext
  subst context
  exact hfailure (not_not.mp hgood)

/-- Rare public-mask failures plus the exact hidden-residual convolution distance control the
full contextual compiler gap.  In particular, no source error is exposed to `hResidual`. -/
theorem tvDist_maskContextualCompiler_native_le_failure_add_hiddenResidual
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount) (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hResidual : ∀ context,
      context ∈ support (maskContextSampler (R := R) levels sourceCount secretSampler) →
      ChallengeSelectorsSucceed gadget selectors context.sourceChallenge →
      hiddenResidualDistance embed sourceErrorSampler targetErrorSampler
        selectors context ≤ bound) :
    tvDist
        (maskContextSampler (R := R) levels sourceCount secretSampler >>= fun context ↦
          compileFromMaskContext embed sourceErrorSampler targetErrorSampler
            selectors context)
        (maskContextSampler (R := R) levels sourceCount secretSampler >>= fun context ↦
          BatchResidualSmudging.fixedSecretSquareBatchSampler levels
            (embed context.secretValue) targetErrorSampler gadget) ≤
      Pr[fun context ↦
          ¬ ChallengeSelectorsSucceed gadget selectors context.sourceChallenge |
        maskContextSampler (R := R) levels sourceCount secretSampler].toReal + bound := by
  classical
  let ContextSampler := maskContextSampler (R := R) levels sourceCount secretSampler
  let Native := fun context : MaskContext R Secret levels sourceCount ↦
    BatchResidualSmudging.fixedSecretSquareBatchSampler levels
      (embed context.secretValue) targetErrorSampler gadget
  let HiddenShifted := fun context : MaskContext R Secret levels sourceCount ↦
    hiddenShiftedSquareBatchSampler embed sourceErrorSampler targetErrorSampler
      gadget selectors context
  let Success := fun context : MaskContext R Secret levels sourceCount ↦
    ChallengeSelectorsSucceed gadget selectors context.sourceChallenge
  let Hybrid := fun context : MaskContext R Secret levels sourceCount ↦
    if Success context then HiddenShifted context else Native context
  have hFailure :
      tvDist
          (ContextSampler >>= fun context ↦
            compileFromMaskContext embed sourceErrorSampler targetErrorSampler
              selectors context)
          (ContextSampler >>= Hybrid) ≤
        Pr[fun context ↦ ¬ Success context | ContextSampler].toReal := by
    apply tvDist_bind_left_event_le ContextSampler
      (fun context ↦
        compileFromMaskContext embed sourceErrorSampler targetErrorSampler
          selectors context)
      Hybrid (fun context ↦ ¬ Success context)
    intro context hNotBad
    have hSuccess : Success context := not_not.mp hNotBad
    simp only [Hybrid, hSuccess, if_true]
    exact compileFromMaskContext_evalDist_eq_hiddenShifted
      embed sourceErrorSampler targetErrorSampler gadget selectors context hSuccess
  have hSmudging :
      tvDist (ContextSampler >>= Hybrid) (ContextSampler >>= Native) ≤ bound := by
    apply tvDist_bind_left_le_const ContextSampler Hybrid Native bound
    intro context hcontext
    by_cases hSuccess : Success context
    · simp only [Hybrid, hSuccess, if_true]
      exact
        (tvDist_hiddenShiftedSquareBatchSampler_le_hiddenResidualDistance
          embed sourceErrorSampler targetErrorSampler gadget selectors context).trans
          (hResidual context hcontext hSuccess)
    · simp only [Hybrid, hSuccess, if_false]
      simpa only [tvDist_self] using hBoundNonneg
  calc
    _ ≤ tvDist
          (ContextSampler >>= fun context ↦
            compileFromMaskContext embed sourceErrorSampler targetErrorSampler
              selectors context)
          (ContextSampler >>= Hybrid) +
        tvDist (ContextSampler >>= Hybrid) (ContextSampler >>= Native) := by
      simpa only [ContextSampler, Native] using
        tvDist_triangle
          (ContextSampler >>= fun context ↦
            compileFromMaskContext embed sourceErrorSampler targetErrorSampler
              selectors context)
          (ContextSampler >>= Hybrid) (ContextSampler >>= Native)
    _ ≤ Pr[fun context ↦ ¬ Success context | ContextSampler].toReal + bound :=
      add_le_add hFailure hSmudging
    _ = _ := by rfl

/-- The genuine stripped-square distribution gap now retains the random source residual under
the mixture. -/
theorem actualDistributionGap_le_failure_add_hiddenResidual
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount) (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hResidual : ∀ context,
      context ∈ support (maskContextSampler (R := R) levels sourceCount secretSampler) →
      ChallengeSelectorsSucceed gadget selectors context.sourceChallenge →
      hiddenResidualDistance embed sourceErrorSampler targetErrorSampler
        selectors context ≤ bound) :
    Heterogeneous.actualDistributionGap levels sourceCount secretSampler embed
        sourceErrorSampler targetErrorSampler gadget selectors ≤
      Pr[fun context ↦
          ¬ ChallengeSelectorsSucceed gadget selectors context.sourceChallenge |
        maskContextSampler (R := R) levels sourceCount secretSampler].toReal + bound := by
  have hContext :=
    tvDist_maskContextualCompiler_native_le_failure_add_hiddenResidual
      levels sourceCount secretSampler embed sourceErrorSampler targetErrorSampler
      gadget selectors bound hBoundNonneg hResidual
  unfold Heterogeneous.actualDistributionGap tvDist at hContext ⊢
  rw [ActualNormalForm.actualSquareBatchSampler_evalDist_eq_nativeSquareBatchSampler,
    nativeSquareBatchSampler_evalDist_eq_maskContextual,
    compiledBatchSampler_evalDist_eq_maskContextual]
  simpa only [SPMF.tvDist_comm] using hContext

/-- Finite genuine `RGSW_S(-S)` security with the statistical term stated as the exact hidden
random-residual distance and the computational term reduced to ordinary batch-RLWE. -/
theorem rgswMinusSecretAdvantage_le_failure_add_hiddenResidual_add_batchLWE_of_convolution
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler extraErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hResidual : ∀ context,
      context ∈ support (maskContextSampler (R := R) levels sourceCount secretSampler) →
      ChallengeSelectorsSucceed gadget selectors context.sourceChallenge →
      hiddenResidualDistance embed sourceErrorSampler targetErrorSampler
        selectors context ≤ bound)
    (hConvolution : FormalProof4FHE.SharedRandomness.ScalarErrorConvolution
      targetErrorSampler sourceErrorSampler extraErrorSampler)
    (hExtra : Pr[⊥ | extraErrorSampler] = 0) :
    Full.rgswMinusSecretAdvantage levels secretSampler embed targetErrorSampler
        gadget distinguisher ≤
      (Pr[fun context ↦
            ¬ ChallengeSelectorsSucceed gadget selectors context.sourceChallenge |
          maskContextSampler (R := R) levels sourceCount secretSampler].toReal + bound) +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed sourceErrorSampler)
          (LWE.TwoBlock.convolutionReduction
            (secondErrorSampler := targetErrorSampler)
            (extraErrorSampler := extraErrorSampler)
            (Heterogeneous.reduction (targetErrorSampler := targetErrorSampler)
              selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  exact
    (Heterogeneous.rgswMinusSecretAdvantage_le_actualDistributionGap_add_batchLWE_of_convolution
      levels sourceCount secretSampler embed sourceErrorSampler targetErrorSampler
      extraErrorSampler gadget selectors distinguisher hConvolution hExtra).trans
      (add_le_add
        (actualDistributionGap_le_failure_add_hiddenResidual
          levels sourceCount secretSampler embed sourceErrorSampler targetErrorSampler
          gadget selectors bound hBoundNonneg hResidual)
        le_rfl)

/-- Canonical endpoint when the emitted RGSW error is the source law convolved with an
independent widening law.  The hidden-residual premise is evaluated after this convolution; it
does not reveal the sampled residual. -/
theorem rgswMinusSecretAdvantage_le_convolution_failure_add_hiddenResidual_add_batchLWE
    {R Secret : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (levels sourceCount : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → R)
    (sourceErrorSampler extraErrorSampler : ProbComp R)
    (gadget : Fin levels → R)
    (selectors : Full.Selectors R levels sourceCount)
    (distinguisher : Full.Distinguisher R levels) (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hResidual : ∀ context,
      context ∈ support
        (maskContextSampler (R := R) levels sourceCount secretSampler) →
      ChallengeSelectorsSucceed gadget selectors context.sourceChallenge →
      hiddenResidualDistance embed sourceErrorSampler
        (Heterogeneous.convolutionSampler sourceErrorSampler extraErrorSampler)
        selectors context ≤ bound)
    (hExtra : Pr[⊥ | extraErrorSampler] = 0) :
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (Heterogeneous.convolutionSampler sourceErrorSampler extraErrorSampler)
        gadget distinguisher ≤
      (Pr[fun context ↦
            ¬ ChallengeSelectorsSucceed gadget selectors context.sourceChallenge |
          maskContextSampler (R := R) levels sourceCount secretSampler].toReal + bound) +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.embeddedBatchProblem 1
            (levels * sourceCount + TGSW.rowCount 1 levels)
            secretSampler embed sourceErrorSampler)
          (LWE.TwoBlock.convolutionReduction
            (secondErrorSampler :=
              Heterogeneous.convolutionSampler sourceErrorSampler extraErrorSampler)
            (extraErrorSampler := extraErrorSampler)
            (Heterogeneous.reduction
              (targetErrorSampler :=
                Heterogeneous.convolutionSampler sourceErrorSampler extraErrorSampler)
              selectors (Full.restoreDistinguisher gadget distinguisher))) := by
  apply rgswMinusSecretAdvantage_le_failure_add_hiddenResidual_add_batchLWE_of_convolution
    levels sourceCount secretSampler embed sourceErrorSampler
      (Heterogeneous.convolutionSampler sourceErrorSampler extraErrorSampler)
      extraErrorSampler gadget selectors distinguisher bound hBoundNonneg hResidual
  · exact Heterogeneous.scalarErrorConvolution_convolutionSampler
      sourceErrorSampler extraErrorSampler
  · exact hExtra

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.HiddenResidual
