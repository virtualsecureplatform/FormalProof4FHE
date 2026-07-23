/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareBinarySelectorSecurity
import FormalProof4FHE.TFHE.RingSquareHiddenResidualMomentObstruction
import FormalProof4FHE.LWE.ParallelBatch

/-!
# The Anchored Error in the Binary `RGSW_S(-S)` Compiler

The binary short-preimage selector reserves source row zero and assigns it coefficient one.
Consequently the hidden residual in every upper RGSW row has the exact form

`S * (e₀ + sum_i b_i e_{i+1})`.

This fact is independent of selector success and of the public masks.  In particular, increasing
the source pool does not make all source-error coefficients small: one fresh source error is
always retained with unit weight.  The final theorem substitutes this normal form into the
bounded-moment lower bound for the complete hidden-residual statistical hop.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler

noncomputable section

open BinaryPreimageExistence
open BinarySelectorSecurity
open FormalProof4FHE.BoundedMoment

/-! ## Exact anchored normal form -/

/-- The reserved coordinate of every anchored binary weight is exactly one. -/
@[simp]
theorem anchoredBinaryWeight_zero
    {R : Type} [CommRing R] {extraCount : ℕ}
    (bits : Fin extraCount → Bool) :
    anchoredBinaryWeight (R := R) bits (0 : Fin (extraCount + 1)) = 1 := by
  simp [anchoredBinaryWeight]

/-- Hence the first weight returned by every binary selector is exactly one, independently of
the public masks inspected by the selector. -/
@[simp]
theorem binarySelectorWeights_zero
    {R : Type} [CommRing R] {extraCount : ℕ}
    (selector : BitSelector R extraCount)
    (masks : MultiSourceCounting.Vectors R (extraCount + 1)) :
    binarySelectorWeights selector masks (0 : Fin (extraCount + 1)) = 1 := by
  simp [binarySelectorWeights]

/-- Split a binary-selector weighted error sum into its unit-weight anchor and its binary tail. -/
theorem sum_binarySelectorWeights_mul_eq_anchor_add_tail
    {R : Type} [CommRing R] {extraCount : ℕ}
    (selector : BitSelector R extraCount)
    (masks : MultiSourceCounting.Vectors R (extraCount + 1))
    (errors : Fin (extraCount + 1) → R) :
    (∑ source : Fin (extraCount + 1),
        binarySelectorWeights selector masks source * errors source) =
      errors 0 +
        ∑ source : Fin extraCount,
          (if selector masks source then 1 else 0) * errors source.succ := by
  classical
  rw [Fin.sum_univ_succ]
  simp [binarySelectorWeights, anchoredBinaryWeight]

/-- The hidden upper-row residual produced by binary selectors contains an unavoidable
unit-weight source error.  This is a pointwise identity, not merely a distributional statement. -/
theorem HiddenResidual.residualShift_binarySelectors_eq_anchor_add_tail
    {R Secret : Type} [CommRing R]
    {levels extraCount : ℕ} (embed : Secret → Fin 1 → R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (context : HiddenResidual.MaskContext R Secret levels (extraCount + 1))
    (sourceError : Fin (levels * (extraCount + 1)) → R)
    (level : Fin levels) :
    HiddenResidual.residualShift embed (binarySelectors bitSelectors)
        context sourceError level =
      embed context.secretValue 0 *
        (sourceError (finProdFinEquiv (level, (0 : Fin (extraCount + 1)))) +
          ∑ source : Fin extraCount,
            (if bitSelectors level
                (fun index ↦
                  context.sourceChallenge 0
                    (finProdFinEquiv (level, index))) source then 1 else 0) *
              sourceError (finProdFinEquiv (level, source.succ))) := by
  rw [HiddenResidual.residualShift_eq_secret_mul_weightedSourceErrors]
  congr 1
  exact sum_binarySelectorWeights_mul_eq_anchor_add_tail
    (bitSelectors level)
    (fun index ↦
      context.sourceChallenge 0 (finProdFinEquiv (level, index)))
    (fun source ↦ sourceError (finProdFinEquiv (level, source)))

/-- Sampler-level form of the same identity.  The complete source-error table stays hidden, but
the residual observable displays the mandatory anchor explicitly. -/
theorem HiddenResidual.upperResidualCoordinateSampler_binarySelectors_eq_anchored
    {R Secret : Type} [CommRing R]
    {levels extraCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler : ProbComp R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (context : HiddenResidual.MaskContext R Secret levels (extraCount + 1))
    (level : Fin levels) :
    HiddenResidual.upperResidualCoordinateSampler embed sourceErrorSampler
        (binarySelectors bitSelectors) context level =
      (fun sourceError ↦
        embed context.secretValue 0 *
          (sourceError (finProdFinEquiv
              (level, (0 : Fin (extraCount + 1)))) +
            ∑ source : Fin extraCount,
              (if bitSelectors level
                  (fun index ↦
                    context.sourceChallenge 0
                      (finProdFinEquiv (level, index))) source then 1 else 0) *
                sourceError (finProdFinEquiv (level, source.succ)))) <$>
        HiddenResidual.sourceErrorTableSampler
          levels (extraCount + 1) sourceErrorSampler := by
  rw [HiddenResidual.upperResidualCoordinateSampler_eq_weightedSourceErrors]
  apply congrArg (fun transform ↦
    transform <$> HiddenResidual.sourceErrorTableSampler
      levels (extraCount + 1) sourceErrorSampler)
  funext sourceError
  congr 1
  exact sum_binarySelectorWeights_mul_eq_anchor_add_tail
    (bitSelectors level)
    (fun index ↦
      context.sourceChallenge 0 (finProdFinEquiv (level, index)))
    (fun source ↦ sourceError (finProdFinEquiv (level, source)))

/-! ## Independent anchor/tail decomposition -/

/-- Restrict the flat hidden error table to the source rows belonging to one gadget level. -/
def HiddenResidual.levelSourceErrorSampler
    {R : Type} {levels sourceCount : ℕ}
    (sourceErrorSampler : ProbComp R) (level : Fin levels) :
    ProbComp (Fin sourceCount → R) :=
  (fun sourceError source ↦
    sourceError (finProdFinEquiv (level, source))) <$>
    HiddenResidual.sourceErrorTableSampler
      levels sourceCount sourceErrorSampler

/-- A level slice of the flat IID source-error table is itself an IID source-error vector. -/
theorem HiddenResidual.levelSourceErrorSampler_evalDist
    {R : Type} [Finite R] {levels sourceCount : ℕ}
    (sourceErrorSampler : ProbComp R) (level : Fin levels) :
    evalDist
        (HiddenResidual.levelSourceErrorSampler
          (levels := levels) (sourceCount := sourceCount)
          sourceErrorSampler level) =
      evalDist (ProbComp.sampleIID sourceCount sourceErrorSampler) := by
  letI : Fintype R := Fintype.ofFinite R
  letI : DecidableEq R := Classical.decEq R
  let split := FormalProof4FHE.LWE.ParallelBatch.outputEquiv
    R levels sourceCount
  let flat := HiddenResidual.sourceErrorTableSampler
    levels sourceCount sourceErrorSampler
  let nested := Fin.mOfFn levels
    (fun _ ↦ ProbComp.sampleIID sourceCount sourceErrorSampler)
  have hSplit : evalDist (split <$> flat) = evalDist nested := by
    simpa [split, flat, nested, HiddenResidual.sourceErrorTableSampler] using
      (FormalProof4FHE.LWE.ParallelBatch.outputEquiv_sampleIID_evalDist
        (R := R) levels sourceCount sourceErrorSampler)
  have hProject := evalDist_map_eq_of_evalDist_eq hSplit
    (fun table ↦ table level)
  calc
    evalDist
        (HiddenResidual.levelSourceErrorSampler
          (levels := levels) (sourceCount := sourceCount)
          sourceErrorSampler level) =
      evalDist ((fun table ↦ table level) <$> (split <$> flat)) := by
        simp only [Functor.map_map]
        rfl
    _ = evalDist ((fun table ↦ table level) <$> nested) := hProject
    _ = evalDist (ProbComp.sampleIID sourceCount sourceErrorSampler) := by
      simpa only [id_eq, id_map] using
        (FormalProof4FHE.FiniteProduct.evalDist_map_fin_mOfFn_apply
          levels
          (fun _ ↦ ProbComp.sampleIID sourceCount sourceErrorSampler)
          level id)

/-- The unit-weight contribution of the reserved source row. -/
def HiddenResidual.binaryAnchorResidualSampler
    {R Secret : Type} [CommRing R]
    (embed : Secret → Fin 1 → R) (sourceErrorSampler : ProbComp R)
    (secretValue : Secret) : ProbComp R :=
  (fun error ↦ embed secretValue 0 * error) <$> sourceErrorSampler

/-- The contribution of all non-anchor rows selected by the public binary selector. -/
def HiddenResidual.binaryTailResidualSampler
    {R Secret : Type} [CommRing R] {levels extraCount : ℕ}
    (embed : Secret → Fin 1 → R) (sourceErrorSampler : ProbComp R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (context : HiddenResidual.MaskContext R Secret levels (extraCount + 1))
    (level : Fin levels) : ProbComp R :=
  (fun errors ↦
    embed context.secretValue 0 *
      ∑ source : Fin extraCount,
        (if bitSelectors level
            (fun index ↦
              context.sourceChallenge 0
                (finProdFinEquiv (level, index))) source then 1 else 0) *
          errors source) <$>
    ProbComp.sampleIID extraCount sourceErrorSampler

/-- The same anchored residual sampled directly from the IID error vector at one level. -/
def HiddenResidual.binaryLevelResidualSampler
    {R Secret : Type} [CommRing R] {levels extraCount : ℕ}
    (embed : Secret → Fin 1 → R) (sourceErrorSampler : ProbComp R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (context : HiddenResidual.MaskContext R Secret levels (extraCount + 1))
    (level : Fin levels) : ProbComp R :=
  (fun errors ↦
    embed context.secretValue 0 *
      (errors 0 +
        ∑ source : Fin extraCount,
          (if bitSelectors level
              (fun index ↦
                context.sourceChallenge 0
                  (finProdFinEquiv (level, index))) source then 1 else 0) *
            errors source.succ)) <$>
    ProbComp.sampleIID (extraCount + 1) sourceErrorSampler

/-- Replacing the flat table by its IID level slice preserves the complete residual law. -/
theorem HiddenResidual.upperResidualCoordinateSampler_binarySelectors_evalDist_eq_level
    {R Secret : Type} [CommRing R] [Finite R]
    {levels extraCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler : ProbComp R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (context : HiddenResidual.MaskContext R Secret levels (extraCount + 1))
    (level : Fin levels) :
    evalDist
        (HiddenResidual.upperResidualCoordinateSampler embed sourceErrorSampler
          (binarySelectors bitSelectors) context level) =
      evalDist
        (HiddenResidual.binaryLevelResidualSampler embed sourceErrorSampler
          bitSelectors context level) := by
  rw [HiddenResidual.upperResidualCoordinateSampler_binarySelectors_eq_anchored]
  let transform := fun errors : Fin (extraCount + 1) → R ↦
    embed context.secretValue 0 *
      (errors 0 +
        ∑ source : Fin extraCount,
          (if bitSelectors level
              (fun index ↦
                context.sourceChallenge 0
                  (finProdFinEquiv (level, index))) source then 1 else 0) *
            errors source.succ)
  have hSlice := HiddenResidual.levelSourceErrorSampler_evalDist
    (levels := levels) (sourceCount := extraCount + 1)
    sourceErrorSampler level
  have hMapped := evalDist_map_eq_of_evalDist_eq hSlice transform
  simpa [HiddenResidual.levelSourceErrorSampler,
    HiddenResidual.binaryLevelResidualSampler, transform,
    Function.comp_def] using hMapped

/-- Sampling the first source error and the selected tail separately is definitionally the
anchored level residual.  In particular, the two contributions are independent. -/
theorem HiddenResidual.binaryLevelResidualSampler_eq_independentAdd
    {R Secret : Type} [CommRing R]
    {levels extraCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler : ProbComp R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (context : HiddenResidual.MaskContext R Secret levels (extraCount + 1))
    (level : Fin levels) :
    HiddenResidual.binaryLevelResidualSampler embed sourceErrorSampler
        bitSelectors context level =
      independentAdd
        (HiddenResidual.binaryAnchorResidualSampler
          embed sourceErrorSampler context.secretValue)
        (HiddenResidual.binaryTailResidualSampler
          embed sourceErrorSampler bitSelectors context level) := by
  classical
  unfold HiddenResidual.binaryLevelResidualSampler
    HiddenResidual.binaryAnchorResidualSampler
    HiddenResidual.binaryTailResidualSampler
    ProbComp.sampleIID independentAdd
  simp only [Fin.mOfFn, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  apply bind_congr
  intro anchorError
  apply bind_congr
  intro tailErrors
  congr 1
  rw [Fin.cons_zero]
  simp only [Fin.cons_succ]
  ring

/-- Exact independent-anchor normal form for the actual hidden compiler residual. -/
theorem HiddenResidual.upperResidualCoordinateSampler_binarySelectors_evalDist_eq_independentAdd
    {R Secret : Type} [CommRing R] [Finite R]
    {levels extraCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler : ProbComp R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (context : HiddenResidual.MaskContext R Secret levels (extraCount + 1))
    (level : Fin levels) :
    evalDist
        (HiddenResidual.upperResidualCoordinateSampler embed sourceErrorSampler
          (binarySelectors bitSelectors) context level) =
      evalDist
        (independentAdd
          (HiddenResidual.binaryAnchorResidualSampler
            embed sourceErrorSampler context.secretValue)
          (HiddenResidual.binaryTailResidualSampler
            embed sourceErrorSampler bitSelectors context level)) := by
  rw [
    HiddenResidual.upperResidualCoordinateSampler_binarySelectors_evalDist_eq_level,
    HiddenResidual.binaryLevelResidualSampler_eq_independentAdd]

/-- For centered, no-wrap anchor and tail contributions, adding the selector tail cannot decrease
the residual second moment. -/
theorem HiddenResidual.binaryAnchorSecondMoment_le_upperResidualSecondMoment
    {R Secret : Type} [CommRing R] [Fintype R]
    {levels extraCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler : ProbComp R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (context : HiddenResidual.MaskContext R Secret levels (extraCount + 1))
    (level : Fin levels) (lift : R → ℝ)
    (hAdd : ∀ anchorValue,
      anchorValue ∈ support
        (HiddenResidual.binaryAnchorResidualSampler
          embed sourceErrorSampler context.secretValue) →
      ∀ tailValue,
      tailValue ∈ support
        (HiddenResidual.binaryTailResidualSampler
          embed sourceErrorSampler bitSelectors context level) →
        lift (anchorValue + tailValue) =
          lift anchorValue + lift tailValue)
    (hAnchorCentered :
      mean
        (HiddenResidual.binaryAnchorResidualSampler
          embed sourceErrorSampler context.secretValue) lift = 0)
    (hTailCentered :
      mean
        (HiddenResidual.binaryTailResidualSampler
          embed sourceErrorSampler bitSelectors context level) lift = 0) :
    secondMoment
        (HiddenResidual.binaryAnchorResidualSampler
          embed sourceErrorSampler context.secretValue) lift ≤
      secondMoment
        (HiddenResidual.upperResidualCoordinateSampler embed sourceErrorSampler
          (binarySelectors bitSelectors) context level) lift := by
  have hMoment := secondMoment_independentAdd_eq_add
    (HiddenResidual.binaryAnchorResidualSampler
      embed sourceErrorSampler context.secretValue)
    (HiddenResidual.binaryTailResidualSampler
      embed sourceErrorSampler bitSelectors context level)
    lift hAdd hAnchorCentered hTailCentered
  have hDist :=
    HiddenResidual.upperResidualCoordinateSampler_binarySelectors_evalDist_eq_independentAdd
      embed sourceErrorSampler bitSelectors context level
  rw [secondMoment_congr_evalDist hDist lift, hMoment]
  exact le_add_of_nonneg_right
    (secondMoment_nonneg
      (HiddenResidual.binaryTailResidualSampler
        embed sourceErrorSampler bitSelectors context level) lift)

/-- Centering of the independent anchor and tail implies centering of the actual compiler
residual. -/
theorem HiddenResidual.mean_upperResidualCoordinateSampler_binarySelectors_eq_zero
    {R Secret : Type} [CommRing R] [Fintype R]
    {levels extraCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler : ProbComp R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (context : HiddenResidual.MaskContext R Secret levels (extraCount + 1))
    (level : Fin levels) (lift : R → ℝ)
    (hAdd : ∀ anchorValue,
      anchorValue ∈ support
        (HiddenResidual.binaryAnchorResidualSampler
          embed sourceErrorSampler context.secretValue) →
      ∀ tailValue,
      tailValue ∈ support
        (HiddenResidual.binaryTailResidualSampler
          embed sourceErrorSampler bitSelectors context level) →
        lift (anchorValue + tailValue) =
          lift anchorValue + lift tailValue)
    (hAnchorCentered :
      mean
        (HiddenResidual.binaryAnchorResidualSampler
          embed sourceErrorSampler context.secretValue) lift = 0)
    (hTailCentered :
      mean
        (HiddenResidual.binaryTailResidualSampler
          embed sourceErrorSampler bitSelectors context level) lift = 0) :
    mean
        (HiddenResidual.upperResidualCoordinateSampler embed sourceErrorSampler
          (binarySelectors bitSelectors) context level) lift = 0 := by
  have hDist :=
    HiddenResidual.upperResidualCoordinateSampler_binarySelectors_evalDist_eq_independentAdd
      embed sourceErrorSampler bitSelectors context level
  rw [mean_congr_evalDist hDist lift,
    mean_independentAdd_eq_add _ _ lift hAdd,
    hAnchorCentered, hTailCentered, add_zero]

/-- **Selector-independent native lower bound.**  In the no-wrap centered regime, the complete
hidden-residual hop is at least the moment of one fresh source error multiplied by the ring secret.
The bound contains neither the selector success probability nor the number of source rows. -/
theorem HiddenResidual.binaryAnchorSecondMoment_div_le_hiddenResidualDistance
    {R Secret : Type} [CommRing R] [Fintype R]
    {levels extraCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (context : HiddenResidual.MaskContext R Secret levels (extraCount + 1))
    (level : Fin levels) (bound : ℝ) (lift : R → ℝ)
    (hBoundPos : 0 < bound)
    (hAnchorTailAdd : ∀ anchorValue,
      anchorValue ∈ support
        (HiddenResidual.binaryAnchorResidualSampler
          embed sourceErrorSampler context.secretValue) →
      ∀ tailValue,
      tailValue ∈ support
        (HiddenResidual.binaryTailResidualSampler
          embed sourceErrorSampler bitSelectors context level) →
        lift (anchorValue + tailValue) =
          lift anchorValue + lift tailValue)
    (hAnchorCentered :
      mean
        (HiddenResidual.binaryAnchorResidualSampler
          embed sourceErrorSampler context.secretValue) lift = 0)
    (hTailCentered :
      mean
        (HiddenResidual.binaryTailResidualSampler
          embed sourceErrorSampler bitSelectors context level) lift = 0)
    (hResidualTargetAdd : ∀ residualValue,
      residualValue ∈ support
        (HiddenResidual.upperResidualCoordinateSampler embed sourceErrorSampler
          (binarySelectors bitSelectors) context level) →
      ∀ noiseValue,
      noiseValue ∈ support
        (HiddenResidual.upperTargetErrorCoordinateSampler
          levels targetErrorSampler level) →
        lift (residualValue + noiseValue) =
          lift residualValue + lift noiseValue)
    (hTargetCentered :
      mean
        (HiddenResidual.upperTargetErrorCoordinateSampler
          levels targetErrorSampler level) lift = 0)
    (hTargetSupport : ∀ value,
      value ∈ support
        (HiddenResidual.upperTargetErrorCoordinateSampler
          levels targetErrorSampler level) →
        |lift value| ≤ bound)
    (hShiftedSupport : ∀ value,
      value ∈ support
        (independentAdd
          (HiddenResidual.upperResidualCoordinateSampler embed sourceErrorSampler
            (binarySelectors bitSelectors) context level)
          (HiddenResidual.upperTargetErrorCoordinateSampler
            levels targetErrorSampler level)) →
        |lift value| ≤ bound) :
    secondMoment
          (HiddenResidual.binaryAnchorResidualSampler
            embed sourceErrorSampler context.secretValue) lift /
        (2 * bound ^ 2) ≤
      HiddenResidual.hiddenResidualDistance embed sourceErrorSampler
        targetErrorSampler (binarySelectors bitSelectors) context := by
  have hResidualCentered :=
    HiddenResidual.mean_upperResidualCoordinateSampler_binarySelectors_eq_zero
      embed sourceErrorSampler bitSelectors context level lift hAnchorTailAdd
        hAnchorCentered hTailCentered
  have hAnchorLe :=
    HiddenResidual.binaryAnchorSecondMoment_le_upperResidualSecondMoment
      embed sourceErrorSampler bitSelectors context level lift hAnchorTailAdd
        hAnchorCentered hTailCentered
  have hResidualDistance :=
    HiddenResidual.upperResidualSecondMoment_div_le_hiddenResidualDistance
      embed sourceErrorSampler targetErrorSampler (binarySelectors bitSelectors)
        context level bound lift hBoundPos hResidualTargetAdd hResidualCentered
        hTargetCentered hTargetSupport hShiftedSupport
  have hDenominatorPos : 0 < 2 * bound ^ 2 := by positivity
  exact (div_le_div_of_nonneg_right hAnchorLe hDenominatorPos.le).trans
    hResidualDistance

/-! ## Moment obstruction with the anchor exposed -/

/-- The exact second moment of the explicitly anchored residual. -/
def HiddenResidual.anchoredUpperResidualSecondMoment
    {R Secret : Type} [CommRing R] [Fintype R]
    {levels extraCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler : ProbComp R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (context : HiddenResidual.MaskContext R Secret levels (extraCount + 1))
    (level : Fin levels) (lift : R → ℝ) : ℝ :=
  secondMoment
    ((fun sourceError ↦
      embed context.secretValue 0 *
        (sourceError (finProdFinEquiv
            (level, (0 : Fin (extraCount + 1)))) +
          ∑ source : Fin extraCount,
            (if bitSelectors level
                (fun index ↦
                  context.sourceChallenge 0
                    (finProdFinEquiv (level, index))) source then 1 else 0) *
              sourceError (finProdFinEquiv (level, source.succ)))) <$>
      HiddenResidual.sourceErrorTableSampler
        levels (extraCount + 1) sourceErrorSampler)
    lift

/-- In the correctness-compatible no-wrap regime, the complete hidden-residual distance is at
least the second moment of `S * (e₀ + Σ bᵢeᵢ)` divided by `2 B²`.  This is the native
binary-selector obstruction with the always-present source error visible in the statement. -/
theorem HiddenResidual.anchoredUpperResidualSecondMoment_div_le_hiddenResidualDistance
    {R Secret : Type} [CommRing R] [Fintype R]
    {levels extraCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (context : HiddenResidual.MaskContext R Secret levels (extraCount + 1))
    (level : Fin levels) (bound : ℝ) (lift : R → ℝ)
    (hBoundPos : 0 < bound)
    (hAdd : ∀ residualValue,
      residualValue ∈ support
        (HiddenResidual.upperResidualCoordinateSampler embed sourceErrorSampler
          (binarySelectors bitSelectors) context level) →
      ∀ noiseValue,
      noiseValue ∈ support
        (HiddenResidual.upperTargetErrorCoordinateSampler
          levels targetErrorSampler level) →
        lift (residualValue + noiseValue) =
          lift residualValue + lift noiseValue)
    (hResidualCentered :
      mean
        (HiddenResidual.upperResidualCoordinateSampler embed sourceErrorSampler
          (binarySelectors bitSelectors) context level) lift = 0)
    (hTargetCentered :
      mean
        (HiddenResidual.upperTargetErrorCoordinateSampler
          levels targetErrorSampler level) lift = 0)
    (hTargetSupport : ∀ value,
      value ∈ support
        (HiddenResidual.upperTargetErrorCoordinateSampler
          levels targetErrorSampler level) →
        |lift value| ≤ bound)
    (hShiftedSupport : ∀ value,
      value ∈ support
        (independentAdd
          (HiddenResidual.upperResidualCoordinateSampler embed sourceErrorSampler
            (binarySelectors bitSelectors) context level)
          (HiddenResidual.upperTargetErrorCoordinateSampler
            levels targetErrorSampler level)) →
        |lift value| ≤ bound) :
    HiddenResidual.anchoredUpperResidualSecondMoment embed sourceErrorSampler
          bitSelectors context level lift /
        (2 * bound ^ 2) ≤
      HiddenResidual.hiddenResidualDistance embed sourceErrorSampler
        targetErrorSampler (binarySelectors bitSelectors) context := by
  rw [HiddenResidual.anchoredUpperResidualSecondMoment,
    ← HiddenResidual.upperResidualCoordinateSampler_binarySelectors_eq_anchored]
  exact HiddenResidual.upperResidualSecondMoment_div_le_hiddenResidualDistance
    embed sourceErrorSampler targetErrorSampler (binarySelectors bitSelectors)
      context level bound lift hBoundPos hAdd hResidualCentered hTargetCentered
      hTargetSupport hShiftedSupport

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler
