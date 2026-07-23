/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.BoundedMoment
import FormalProof4FHE.TFHE.RingSquareHiddenResidualCompiler

/-!
# A Bounded-Moment Obstruction for the Hidden `RGSW_S(-S)` Residual

The short-preimage compiler leaves the source errors hidden and therefore pays
the random-convolution distance

`TV(residualVector + targetErrorVector, targetErrorVector)`.

This file proves a converse in the correctness-compatible no-wrap regime.  At
any upper RGSW row, project the hidden residual and target error to a real
centered lift.  If both are centered, addition does not wrap on their supports,
and the target and shifted target stay in a common interval `[-B, B]`, then

`secondMoment(residual) / (2 B²) ≤ hiddenResidualDistance`.

Thus a non-negligible residual variance cannot be erased statistically by an
independent target error whose final support remains polynomially bounded.  A
successful native small-noise proof must make that residual moment negligible,
exploit modular wrap, or replace this statistical hop by a computational one.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.HiddenResidual

noncomputable section

open FormalProof4FHE.BoundedMoment

/-- One upper-row coordinate of the hidden compiler residual. -/
def upperResidualCoordinateSampler
    {R Secret : Type} [CommRing R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount)
    (level : Fin levels) : ProbComp R :=
  (fun residual ↦ residual (Full.upperRow level)) <$>
    residualVectorSampler embed sourceErrorSampler selectors context

/-- The projected residual sampler is exactly the hidden weighted source-error
sum from the compiler normal form. -/
theorem upperResidualCoordinateSampler_eq_weightedSourceErrors
    {R Secret : Type} [CommRing R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount)
    (level : Fin levels) :
    upperResidualCoordinateSampler embed sourceErrorSampler selectors
        context level =
      (fun sourceError ↦
        embed context.secretValue 0 *
          ∑ source : Fin sourceCount,
            selectors level
                (fun index ↦
                  context.sourceChallenge 0
                    (finProdFinEquiv (level, index))) source *
              sourceError (finProdFinEquiv (level, source))) <$>
        sourceErrorTableSampler levels sourceCount sourceErrorSampler := by
  classical
  unfold upperResidualCoordinateSampler residualVectorSampler
  simp only [Functor.map_map,
    BatchResidualSmudging.upperShiftVector_upper]
  apply congrArg (fun transform ↦
    transform <$> sourceErrorTableSampler levels sourceCount sourceErrorSampler)
  funext sourceError
  exact residualShift_eq_secret_mul_weightedSourceErrors
    embed selectors context sourceError level

/-- The matching upper-row coordinate of the independent target-error vector. -/
def upperTargetErrorCoordinateSampler
    {R : Type} [Finite R]
    (levels : ℕ) (targetErrorSampler : ProbComp R)
    (level : Fin levels) : ProbComp R :=
  (fun error ↦ error (Full.upperRow level)) <$>
    ProbComp.sampleIID (TGSW.rowCount 1 levels) targetErrorSampler

/-- Every coordinate of the IID target-error vector has exactly the original
scalar target-error law. -/
theorem upperTargetErrorCoordinateSampler_evalDist
    {R : Type} [Finite R]
    (levels : ℕ) (targetErrorSampler : ProbComp R)
    (level : Fin levels) :
    evalDist
        (upperTargetErrorCoordinateSampler levels targetErrorSampler level) =
      evalDist targetErrorSampler := by
  unfold upperTargetErrorCoordinateSampler ProbComp.sampleIID
  simpa only [id_eq, id_map] using
    (FormalProof4FHE.FiniteProduct.evalDist_map_fin_mOfFn_apply
      (TGSW.rowCount 1 levels) (fun _ ↦ targetErrorSampler)
      (Full.upperRow level) id)

/-- Projecting the hidden shifted batch to an upper row is exactly the sum of
the projected hidden residual and an independent projected target error. -/
theorem upperCoordinate_hiddenShifted_evalDist_eq_independentAdd
    {R Secret : Type} [CommRing R] [Finite R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount)
    (level : Fin levels) :
    evalDist
        ((fun error ↦ error (Full.upperRow level)) <$>
          hiddenShiftedBatchErrorSampler embed sourceErrorSampler
            targetErrorSampler selectors context) =
      evalDist
        (independentAdd
          (upperResidualCoordinateSampler embed sourceErrorSampler
            selectors context level)
          (upperTargetErrorCoordinateSampler levels targetErrorSampler level)) := by
  apply congrArg evalDist
  unfold hiddenShiftedBatchErrorSampler upperResidualCoordinateSampler
    upperTargetErrorCoordinateSampler residualVectorSampler independentAdd
    sourceErrorTableSampler
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]

/-- Data processing: one upper-row coordinate can only have smaller distance
than the complete hidden residual vector. -/
theorem tvDist_upperCoordinate_independentAdd_le_hiddenResidualDistance
    {R Secret : Type} [CommRing R] [Fintype R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount)
    (level : Fin levels) :
    tvDist
        (independentAdd
          (upperResidualCoordinateSampler embed sourceErrorSampler
            selectors context level)
          (upperTargetErrorCoordinateSampler levels targetErrorSampler level))
        (upperTargetErrorCoordinateSampler levels targetErrorSampler level) ≤
      hiddenResidualDistance embed sourceErrorSampler targetErrorSampler
        selectors context := by
  let project := fun error : Fin (TGSW.rowCount 1 levels) → R ↦
    error (Full.upperRow level)
  let shifted := hiddenShiftedBatchErrorSampler embed sourceErrorSampler
    targetErrorSampler selectors context
  let target := ProbComp.sampleIID (TGSW.rowCount 1 levels) targetErrorSampler
  have hShifted :
      evalDist (project <$> shifted) =
        evalDist
          (independentAdd
            (upperResidualCoordinateSampler embed sourceErrorSampler
              selectors context level)
            (upperTargetErrorCoordinateSampler levels targetErrorSampler level)) := by
    exact upperCoordinate_hiddenShifted_evalDist_eq_independentAdd
      embed sourceErrorSampler targetErrorSampler selectors context level
  have hProjected :
      tvDist
          (independentAdd
            (upperResidualCoordinateSampler embed sourceErrorSampler
              selectors context level)
            (upperTargetErrorCoordinateSampler levels targetErrorSampler level))
          (upperTargetErrorCoordinateSampler levels targetErrorSampler level) =
        tvDist (project <$> shifted) (project <$> target) := by
    unfold tvDist
    rw [hShifted]
    rfl
  rw [hProjected]
  exact tvDist_map_le project shifted target

/-- Quantified small-noise obstruction for one upper RGSW row.  Under centered,
no-wrap, common-support hypotheses, the complete hidden-residual distance is at
least the residual second moment divided by `2 B²`. -/
theorem upperResidualSecondMoment_div_le_hiddenResidualDistance
    {R Secret : Type} [CommRing R] [Fintype R]
    {levels sourceCount : ℕ} (embed : Secret → Fin 1 → R)
    (sourceErrorSampler targetErrorSampler : ProbComp R)
    (selectors : Full.Selectors R levels sourceCount)
    (context : MaskContext R Secret levels sourceCount)
    (level : Fin levels) (bound : ℝ) (lift : R → ℝ)
    (hBoundPos : 0 < bound)
    (hAdd : ∀ residualValue,
      residualValue ∈ support
        (upperResidualCoordinateSampler embed sourceErrorSampler
          selectors context level) →
      ∀ noiseValue,
      noiseValue ∈ support
        (upperTargetErrorCoordinateSampler levels targetErrorSampler level) →
        lift (residualValue + noiseValue) =
          lift residualValue + lift noiseValue)
    (hResidualCentered :
      mean
        (upperResidualCoordinateSampler embed sourceErrorSampler
          selectors context level) lift = 0)
    (hTargetCentered :
      mean
        (upperTargetErrorCoordinateSampler levels targetErrorSampler level)
        lift = 0)
    (hTargetSupport : ∀ value,
      value ∈ support
        (upperTargetErrorCoordinateSampler levels targetErrorSampler level) →
        |lift value| ≤ bound)
    (hShiftedSupport : ∀ value,
      value ∈ support
        (independentAdd
          (upperResidualCoordinateSampler embed sourceErrorSampler
            selectors context level)
          (upperTargetErrorCoordinateSampler levels targetErrorSampler level)) →
        |lift value| ≤ bound) :
    secondMoment
        (upperResidualCoordinateSampler embed sourceErrorSampler
          selectors context level) lift /
        (2 * bound ^ 2) ≤
      hiddenResidualDistance embed sourceErrorSampler targetErrorSampler
        selectors context := by
  exact
    (secondMoment_div_two_mul_sq_le_tvDist_independentAdd
      (upperResidualCoordinateSampler embed sourceErrorSampler
        selectors context level)
      (upperTargetErrorCoordinateSampler levels targetErrorSampler level)
      bound lift hBoundPos hAdd hResidualCentered hTargetCentered
      hTargetSupport hShiftedSupport).trans
      (tvDist_upperCoordinate_independentAdd_le_hiddenResidualDistance
        embed sourceErrorSampler targetErrorSampler selectors context level)

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.HiddenResidual
