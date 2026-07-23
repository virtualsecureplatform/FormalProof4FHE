/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.ConditionalCollision
import FormalProof4FHE.TFHE.NativeDiagonalResidualNormalForm

/-!
# Joint Collision Bound for the Native TFHE Diagonal

The fixed-difference analysis of the selected native TFHE diagonal conditions on the complete
digit matrix.  For exact-capacity even-base decompositions that route necessarily pays a
constant rank-failure loss.  The random difference is not public in the final experiment,
however, so the correct object is the joint distribution of

* the transformed source-error vector, retained as side information; and
* the transformed public challenge matrix, which should become fresh uniform.

This module instantiates the side-information collision inequality with the complete uniform
difference and challenge as one joint random input.  The resulting loss does not require the
fixed-difference row operator to be invertible.  It is therefore a sound replacement target for
the obstructed determinant certificate.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

variable {q degree ringRank : ℕ}

/-- Uniform randomness used jointly by the direct diagonal-mask extractor. -/
abbrev DiagonalJointRandomness (q degree ringRank levels : ℕ) :=
  RingGSWCiphertext q (degree + 1) ringRank levels ×
    DiagonalChallenge q degree ringRank levels

/-- Retained transformed error for a fixed source-error vector. -/
def fixedErrorDiagonalSide [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (randomness : DiagonalJointRandomness q degree ringRank params.levels) :
    DiagonalErrorVector q degree ringRank params.levels :=
  rowOperator candidate (differenceEntryDigits params randomness.1) sourceError

/-- Public challenge extracted from the same hidden difference randomness. -/
def fixedErrorDiagonalOutput [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (randomness : DiagonalJointRandomness q degree ringRank params.levels) :
    DiagonalChallenge q degree ringRank params.levels :=
  challengeOperator candidate (differenceEntryDigits params randomness.1) randomness.2

/-- Side-information collision cost for one fixed source-error vector.  Unlike the old
conditional loss, the complete difference ciphertext remains inside the extractor input. -/
noncomputable def fixedErrorDiagonalCollisionLoss [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  FormalProof4FHE.ConditionalCollision.conditionalFiberCollisionLoss
    (fixedErrorDiagonalSide params candidate sourceError)
    (fixedErrorDiagonalOutput params candidate)

/-- Pearson chi-square divergence for the same fixed-error joint extractor, expressed by
normalized joint- and side-fiber cardinalities. -/
noncomputable def fixedErrorDiagonalChiSquare [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  FormalProof4FHE.ConditionalCollision.conditionalFiberChiSquare
    (fixedErrorDiagonalSide params candidate sourceError)
    (fixedErrorDiagonalOutput params candidate)

/-- Total-variation budget obtained from the fixed-error Pearson chi-square divergence. -/
noncomputable def fixedErrorDiagonalChiSquareLoss [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  Real.sqrt (fixedErrorDiagonalChiSquare params candidate sourceError) / 2

/-- Pointwise pair-collision certificate for the native joint extractor.  Inside every retained
transformed-error fiber, its ordered output-collision count is at most `1 + ε` times the uniform
challenge baseline.  This is the interface intended for rectangular-rank or Fourier estimates
on two independently hidden difference/challenge inputs. -/
def fixedErrorDiagonalPairCollisionBound [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (ε : ℝ) : Prop :=
  ∀ transformedError : DiagonalErrorVector q degree ringRank params.levels,
    (Fintype.card (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
        FormalProof4FHE.ConditionalCollision.conditionalFiberCollisionPairCount
          (fixedErrorDiagonalSide params candidate sourceError)
          (fixedErrorDiagonalOutput params candidate) transformedError ≤
      (1 + ε) *
        (FormalProof4FHE.ConditionalCollision.sideFiberCard
          (fixedErrorDiagonalSide params candidate sourceError)
          transformedError : ℝ) ^ 2

/-- Exact source-error average of the direct joint collision cost. -/
noncomputable def averagedSourceErrorDiagonalCollisionLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) : ℝ :=
  ∑' sourceError : DiagonalErrorVector q degree ringRank params.levels,
    Pr[= sourceError |
      ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler].toReal *
      fixedErrorDiagonalCollisionLoss params candidate sourceError

/-- Exact source-error average of the explicit chi-square total-variation budget. -/
noncomputable def averagedSourceErrorDiagonalChiSquareLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) : ℝ :=
  ∑' sourceError : DiagonalErrorVector q degree ringRank params.levels,
    Pr[= sourceError |
      ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler].toReal *
      fixedErrorDiagonalChiSquareLoss params candidate sourceError

/-- Real pair experiment, with the transformed error retained as the first coordinate and the
transformed public challenge as the second. -/
noncomputable def jointDiagonalPairExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    ProbComp
      (DiagonalErrorVector q degree ringRank params.levels ×
        DiagonalChallenge q degree ringRank params.levels) := do
  let sourceError ←
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  FormalProof4FHE.ConditionalCollision.uniformJointImage
    (fixedErrorDiagonalSide params candidate sourceError)
    (fixedErrorDiagonalOutput params candidate)

/-- Mask-decoupled pair experiment.  It retains the exact transformed-error marginal while
replacing the public challenge by a fresh independent uniform matrix. -/
noncomputable def jointMaskReplacedPairExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    ProbComp
      (DiagonalErrorVector q degree ringRank params.levels ×
        DiagonalChallenge q degree ringRank params.levels) := do
  let sourceError ←
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  FormalProof4FHE.ConditionalCollision.uniformSideIndependentOutput
    (Output := DiagonalChallenge q degree ringRank params.levels)
    (fixedErrorDiagonalSide params candidate sourceError)

theorem fixedErrorDiagonalCollisionLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ fixedErrorDiagonalCollisionLoss params candidate sourceError :=
  FormalProof4FHE.ConditionalCollision.conditionalFiberCollisionLoss_nonneg _ _

/-- The original side-wise collision loss is exactly an explicit finite-cardinality
expression, with no residual probabilistic oracle terms. -/
theorem fixedErrorDiagonalCollisionLoss_eq_cardinalityLoss [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalCollisionLoss params candidate sourceError =
      FormalProof4FHE.ConditionalCollision.conditionalFiberCardinalityLoss
        (fixedErrorDiagonalSide params candidate sourceError)
        (fixedErrorDiagonalOutput params candidate) :=
  FormalProof4FHE.ConditionalCollision.conditionalFiberCollisionLoss_eq_cardinalityLoss _ _

theorem fixedErrorDiagonalChiSquare_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ fixedErrorDiagonalChiSquare params candidate sourceError :=
  FormalProof4FHE.ConditionalCollision.conditionalFiberChiSquare_nonneg _ _

theorem fixedErrorDiagonalChiSquareLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ fixedErrorDiagonalChiSquareLoss params candidate sourceError := by
  unfold fixedErrorDiagonalChiSquareLoss
  positivity

/-- The native fixed-error Pearson term is exactly the normalized conditional collision-pair
second moment. -/
theorem fixedErrorDiagonalChiSquare_eq_secondMoment [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalChiSquare params candidate sourceError =
      (Fintype.card (DiagonalChallenge q degree ringRank params.levels) : ℝ) /
          (Fintype.card
            (DiagonalJointRandomness q degree ringRank params.levels) : ℝ) *
        FormalProof4FHE.ConditionalCollision.conditionalFiberSecondMoment
          (fixedErrorDiagonalSide params candidate sourceError)
          (fixedErrorDiagonalOutput params candidate) - 1 := by
  unfold fixedErrorDiagonalChiSquare
  exact FormalProof4FHE.ConditionalCollision.conditionalFiberChiSquare_eq_secondMoment _ _

/-- A native pair-collision certificate bounds the fixed-error Pearson divergence. -/
theorem fixedErrorDiagonalChiSquare_le_of_pairCollisionBound [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (ε : ℝ)
    (hbound : fixedErrorDiagonalPairCollisionBound params candidate sourceError ε) :
    fixedErrorDiagonalChiSquare params candidate sourceError ≤ ε := by
  unfold fixedErrorDiagonalChiSquare
  apply FormalProof4FHE.ConditionalCollision.conditionalFiberChiSquare_le_of_secondMoment
  intro transformedError
  rw [FormalProof4FHE.ConditionalCollision.sum_jointFiberCard_sq_eq_collisionPairCount]
  exact hbound transformedError

/-- The pair-collision certificate gives the corresponding square-root statistical loss. -/
theorem fixedErrorDiagonalChiSquareLoss_le_of_pairCollisionBound [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (ε : ℝ)
    (hbound : fixedErrorDiagonalPairCollisionBound params candidate sourceError ε) :
    fixedErrorDiagonalChiSquareLoss params candidate sourceError ≤
      Real.sqrt ε / 2 := by
  unfold fixedErrorDiagonalChiSquareLoss
  gcongr
  exact fixedErrorDiagonalChiSquare_le_of_pairCollisionBound
    params candidate sourceError ε hbound

theorem averagedSourceErrorDiagonalCollisionLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    0 ≤ averagedSourceErrorDiagonalCollisionLoss (ringRank := ringRank)
      params sourceErrorSampler candidate := by
  unfold averagedSourceErrorDiagonalCollisionLoss
  exact tsum_nonneg fun sourceError =>
    mul_nonneg ENNReal.toReal_nonneg
      (fixedErrorDiagonalCollisionLoss_nonneg params candidate sourceError)

theorem averagedSourceErrorDiagonalChiSquareLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    0 ≤ averagedSourceErrorDiagonalChiSquareLoss (ringRank := ringRank)
      params sourceErrorSampler candidate := by
  unfold averagedSourceErrorDiagonalChiSquareLoss
  exact tsum_nonneg fun sourceError =>
    mul_nonneg ENNReal.toReal_nonneg
      (fixedErrorDiagonalChiSquareLoss_nonneg params candidate sourceError)

/-- A uniform pair-collision estimate on the support of the source-error vector bounds the
complete averaged direct mask-replacement budget. -/
theorem averagedSourceErrorDiagonalChiSquareLoss_le_of_pairCollisionBound [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) (ε : ℝ)
    (hbound : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      fixedErrorDiagonalPairCollisionBound params candidate sourceError ε) :
    averagedSourceErrorDiagonalChiSquareLoss (ringRank := ringRank)
        params sourceErrorSampler candidate ≤
      Real.sqrt ε / 2 := by
  let ErrorVector := DiagonalErrorVector q degree ringRank params.levels
  let Errors : ProbComp ErrorVector :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  letI : Fintype ErrorVector := Fintype.ofFinite ErrorVector
  have hmass : (∑ sourceError : ErrorVector,
      Pr[= sourceError | Errors].toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun _ _ => probOutput_ne_top),
      sum_probOutput_eq_one (by simp), ENNReal.toReal_one]
  unfold averagedSourceErrorDiagonalChiSquareLoss
  rw [tsum_fintype]
  calc
    ∑ sourceError : ErrorVector,
        Pr[= sourceError | Errors].toReal *
          fixedErrorDiagonalChiSquareLoss params candidate sourceError ≤
      ∑ sourceError : ErrorVector,
        Pr[= sourceError | Errors].toReal * (Real.sqrt ε / 2) := by
          apply Finset.sum_le_sum
          intro sourceError _
          by_cases hsource : sourceError ∈ support Errors
          · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
            apply fixedErrorDiagonalChiSquareLoss_le_of_pairCollisionBound
            exact hbound sourceError (by simpa [Errors, ErrorVector] using hsource)
          · have hzero : Pr[= sourceError | Errors] = 0 :=
              probOutput_eq_zero_of_not_mem_support hsource
            simp [hzero]
    _ = (∑ sourceError : ErrorVector,
        Pr[= sourceError | Errors].toReal) * (Real.sqrt ε / 2) := by
          rw [Finset.sum_mul]
    _ = Real.sqrt ε / 2 := by rw [hmass, one_mul]

/-- Fixed-error mask replacement bounded by its explicit Pearson chi-square quantity. -/
theorem tvDist_fixedErrorDiagonal_le_chiSquareLoss [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    tvDist
        (FormalProof4FHE.ConditionalCollision.uniformJointImage
          (fixedErrorDiagonalSide params candidate sourceError)
          (fixedErrorDiagonalOutput params candidate))
        (FormalProof4FHE.ConditionalCollision.uniformSideIndependentOutput
          (Output := DiagonalChallenge q degree ringRank params.levels)
          (fixedErrorDiagonalSide params candidate sourceError)) ≤
      fixedErrorDiagonalChiSquareLoss params candidate sourceError := by
  exact FormalProof4FHE.ConditionalCollision.tvDist_uniformJointImage_sideIndependent_le_chiSquare
    (fixedErrorDiagonalSide params candidate sourceError)
    (fixedErrorDiagonalOutput params candidate)

/-- A uniform product input may be exposed as independently sampled difference and challenge
without changing the fixed-error real pair law. -/
theorem fixedErrorUniformJointImage_evalDist_eq_sequential [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    evalDist
        (FormalProof4FHE.ConditionalCollision.uniformJointImage
          (fixedErrorDiagonalSide params candidate sourceError)
          (fixedErrorDiagonalOutput params candidate)) =
      evalDist (do
        let difference ←
          $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
        let challenge ← $ᵗ DiagonalChallenge q degree ringRank params.levels
        pure
          (rowOperator candidate (differenceEntryDigits params difference) sourceError,
            challengeOperator candidate (differenceEntryDigits params difference)
              challenge)) := by
  let Difference := RingGSWCiphertext q (degree + 1) ringRank params.levels
  let Challenge := DiagonalChallenge q degree ringRank params.levels
  let ProductSampler : ProbComp (Difference × Challenge) := do
    let difference ← $ᵗ Difference
    let challenge ← $ᵗ Challenge
    return (difference, challenge)
  let finish := fun randomness : Difference × Challenge =>
    (fixedErrorDiagonalSide params candidate sourceError randomness,
      fixedErrorDiagonalOutput params candidate randomness)
  have hProduct : evalDist ProductSampler = evalDist ($ᵗ (Difference × Challenge)) :=
    FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
  have hMapped := evalDist_map_eq_of_evalDist_eq hProduct finish
  simpa [FormalProof4FHE.ConditionalCollision.uniformJointImage,
    ProductSampler, finish, Difference, Challenge, fixedErrorDiagonalSide,
    fixedErrorDiagonalOutput, map_eq_bind_pure_comp, bind_assoc] using hMapped.symm

set_option maxRecDepth 2000 in
/-- In the fixed-error ideal pair law, the unused challenge component of the uniform product
input can be projected away. -/
theorem fixedErrorUniformSideIndependent_evalDist_eq_sequential [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    evalDist
        (FormalProof4FHE.ConditionalCollision.uniformSideIndependentOutput
          (Output := DiagonalChallenge q degree ringRank params.levels)
          (fixedErrorDiagonalSide params candidate sourceError)) =
      evalDist (do
        let difference ←
          $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
        let challenge ← $ᵗ DiagonalChallenge q degree ringRank params.levels
        pure
          (rowOperator candidate (differenceEntryDigits params difference) sourceError,
            challenge)) := by
  let Difference := RingGSWCiphertext q (degree + 1) ringRank params.levels
  let Challenge := DiagonalChallenge q degree ringRank params.levels
  let sideFromDifference := fun difference : Difference =>
    rowOperator candidate (differenceEntryDigits params difference) sourceError
  have hProjection :
      evalDist (Prod.fst <$> ($ᵗ (Difference × Challenge))) =
        evalDist ($ᵗ Difference) :=
    evalDist_map_fst_uniformSample_prod
  have hSide := evalDist_map_eq_of_evalDist_eq hProjection sideFromDifference
  have hBind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hSide (fun sideValue =>
      (fun challenge : Challenge => (sideValue, challenge)) <$> ($ᵗ Challenge))
  have hLeft :
      FormalProof4FHE.ConditionalCollision.uniformSideIndependentOutput
          (Output := Challenge)
          (fixedErrorDiagonalSide params candidate sourceError) =
        ((sideFromDifference <$> (Prod.fst <$> ($ᵗ (Difference × Challenge)))) >>=
          fun sideValue =>
            (fun challenge : Challenge => (sideValue, challenge)) <$> ($ᵗ Challenge)) := by
    simp only [FormalProof4FHE.ConditionalCollision.uniformSideIndependentOutput,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    rfl
  have hRight :
      ((sideFromDifference <$> ($ᵗ Difference)) >>= fun sideValue =>
          (fun challenge : Challenge => (sideValue, challenge)) <$> ($ᵗ Challenge)) =
        (do
          let difference ← $ᵗ Difference
          let challenge ← $ᵗ Challenge
          pure (sideFromDifference difference, challenge)) := by
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
    rfl
  rw [hLeft]
  calc
    _ = evalDist
        ((sideFromDifference <$> ($ᵗ Difference)) >>= fun sideValue =>
          (fun challenge : Challenge => (sideValue, challenge)) <$>
            ($ᵗ Challenge)) := hBind
    _ = evalDist (do
        let difference ← $ᵗ Difference
        let challenge ← $ᵗ Challenge
        pure (sideFromDifference difference, challenge)) := congrArg evalDist hRight
    _ = _ := by
      rfl

/-- The source-error-first joint pair definition is exactly the original
difference/challenge/error sampling order. -/
theorem jointDiagonalPairExperiment_evalDist_eq_differenceFirst [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    evalDist
        (jointDiagonalPairExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate) =
      evalDist (do
        let difference ←
          $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
        let challenge ← $ᵗ DiagonalChallenge q degree ringRank params.levels
        let sourceError ←
          ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
            sourceErrorSampler
        pure
          (rowOperator candidate (differenceEntryDigits params difference) sourceError,
            challengeOperator candidate (differenceEntryDigits params difference)
              challenge)) := by
  let Errors : ProbComp (DiagonalErrorVector q degree ringRank params.levels) :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  let Difference : ProbComp
      (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  let Challenge : ProbComp (DiagonalChallenge q degree ringRank params.levels) :=
    $ᵗ DiagonalChallenge q degree ringRank params.levels
  let finish := fun
      (sourceError : DiagonalErrorVector q degree ringRank params.levels)
      (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (challenge : DiagonalChallenge q degree ringRank params.levels) =>
    (pure
      (rowOperator candidate (differenceEntryDigits params difference) sourceError,
        challengeOperator candidate (differenceEntryDigits params difference) challenge) :
      ProbComp
        (DiagonalErrorVector q degree ringRank params.levels ×
          DiagonalChallenge q degree ringRank params.levels))
  calc
    _ = evalDist (Errors >>= fun sourceError =>
        Difference >>= fun difference => Challenge >>= finish sourceError difference) := by
      unfold jointDiagonalPairExperiment
      refine evalDist_bind_congr' Errors fun sourceError => ?_
      simpa only [Difference, Challenge, finish] using
        (fixedErrorUniformJointImage_evalDist_eq_sequential
          params candidate sourceError)
    _ = evalDist (Difference >>= fun difference =>
        Errors >>= fun sourceError => Challenge >>= finish sourceError difference) :=
      evalDist_bind_bind_swap Errors Difference
        (fun sourceError difference => Challenge >>= finish sourceError difference)
    _ = evalDist (Difference >>= fun difference =>
        Challenge >>= fun challenge => Errors >>= fun sourceError =>
          finish sourceError difference challenge) := by
      refine evalDist_bind_congr' Difference fun difference => ?_
      exact evalDist_bind_bind_swap Errors Challenge
        (fun sourceError challenge => finish sourceError difference challenge)
    _ = _ := by
      simp only [Errors, Difference, Challenge, finish]

/-- The side-independent pair law consists of the exact mixed transformed-error marginal and a
fresh independent uniform challenge. -/
theorem jointMaskReplacedPairExperiment_evalDist_eq_mixedErrorFirst [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    evalDist
        (jointMaskReplacedPairExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate) =
      evalDist (do
        let transformedError ←
          mixedDiagonalErrorSampler (ringRank := ringRank)
            params sourceErrorSampler candidate
        let challenge ← $ᵗ DiagonalChallenge q degree ringRank params.levels
        pure (transformedError, challenge)) := by
  let Errors : ProbComp (DiagonalErrorVector q degree ringRank params.levels) :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  let Difference : ProbComp
      (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  let Challenge : ProbComp (DiagonalChallenge q degree ringRank params.levels) :=
    $ᵗ DiagonalChallenge q degree ringRank params.levels
  let finish := fun
      (sourceError : DiagonalErrorVector q degree ringRank params.levels)
      (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (challenge : DiagonalChallenge q degree ringRank params.levels) =>
    (pure
      (rowOperator candidate (differenceEntryDigits params difference) sourceError,
        challenge) :
      ProbComp
        (DiagonalErrorVector q degree ringRank params.levels ×
          DiagonalChallenge q degree ringRank params.levels))
  calc
    _ = evalDist (Errors >>= fun sourceError =>
        Difference >>= fun difference => Challenge >>= finish sourceError difference) := by
      unfold jointMaskReplacedPairExperiment
      refine evalDist_bind_congr' Errors fun sourceError => ?_
      simpa only [Difference, Challenge, finish] using
        (fixedErrorUniformSideIndependent_evalDist_eq_sequential
          params candidate sourceError)
    _ = evalDist (Difference >>= fun difference =>
        Errors >>= fun sourceError => Challenge >>= finish sourceError difference) :=
      evalDist_bind_bind_swap Errors Difference
        (fun sourceError difference => Challenge >>= finish sourceError difference)
    _ = _ := by
      simp [mixedDiagonalErrorSampler, Errors, Difference, Challenge, finish,
        map_eq_bind_pure_comp, bind_assoc]

/-- Direct collision replacement of the transformed public challenge, retaining the complete
transformed-error side information. -/
theorem tvDist_jointDiagonalPair_jointMaskReplaced_le [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    tvDist
        (jointDiagonalPairExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate)
        (jointMaskReplacedPairExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate) ≤
      averagedSourceErrorDiagonalCollisionLoss (ringRank := ringRank)
        params sourceErrorSampler candidate := by
  let Errors : ProbComp (DiagonalErrorVector q degree ringRank params.levels) :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  let Real := fun sourceError : DiagonalErrorVector q degree ringRank params.levels =>
    FormalProof4FHE.ConditionalCollision.uniformJointImage
      (fixedErrorDiagonalSide params candidate sourceError)
      (fixedErrorDiagonalOutput params candidate)
  let Ideal := fun sourceError : DiagonalErrorVector q degree ringRank params.levels =>
    FormalProof4FHE.ConditionalCollision.uniformSideIndependentOutput
      (Output := DiagonalChallenge q degree ringRank params.levels)
      (fixedErrorDiagonalSide params candidate sourceError)
  have hMixture := FormalProof4FHE.FiniteProduct.tvDist_bind_left_le_expectation
    Errors Real Ideal
  have hAverage :
      (∑' sourceError,
          Pr[= sourceError | Errors].toReal * tvDist (Real sourceError) (Ideal sourceError)) ≤
        averagedSourceErrorDiagonalCollisionLoss (ringRank := ringRank)
          params sourceErrorSampler candidate := by
    unfold averagedSourceErrorDiagonalCollisionLoss
    apply Summable.tsum_le_tsum
    · intro sourceError
      exact mul_le_mul_of_nonneg_left
        (FormalProof4FHE.ConditionalCollision.tvDist_uniformJointImage_sideIndependent_le
          (fixedErrorDiagonalSide params candidate sourceError)
          (fixedErrorDiagonalOutput params candidate))
        ENNReal.toReal_nonneg
    · exact Summable.of_finite
    · exact Summable.of_finite
  simpa only [jointDiagonalPairExperiment, jointMaskReplacedPairExperiment,
    Errors, Real, Ideal] using hMixture.trans hAverage

/-- The same direct pair replacement through the normalized fiber chi-square interface.  This
form is convenient when a counting argument controls the full Pearson sum at once. -/
theorem tvDist_jointDiagonalPair_jointMaskReplaced_le_chiSquare [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    tvDist
        (jointDiagonalPairExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate)
        (jointMaskReplacedPairExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate) ≤
      averagedSourceErrorDiagonalChiSquareLoss (ringRank := ringRank)
        params sourceErrorSampler candidate := by
  let Errors : ProbComp (DiagonalErrorVector q degree ringRank params.levels) :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  let Real := fun sourceError : DiagonalErrorVector q degree ringRank params.levels =>
    FormalProof4FHE.ConditionalCollision.uniformJointImage
      (fixedErrorDiagonalSide params candidate sourceError)
      (fixedErrorDiagonalOutput params candidate)
  let Ideal := fun sourceError : DiagonalErrorVector q degree ringRank params.levels =>
    FormalProof4FHE.ConditionalCollision.uniformSideIndependentOutput
      (Output := DiagonalChallenge q degree ringRank params.levels)
      (fixedErrorDiagonalSide params candidate sourceError)
  have hMixture := FormalProof4FHE.FiniteProduct.tvDist_bind_left_le_expectation
    Errors Real Ideal
  have hAverage :
      (∑' sourceError,
          Pr[= sourceError | Errors].toReal * tvDist (Real sourceError) (Ideal sourceError)) ≤
        averagedSourceErrorDiagonalChiSquareLoss (ringRank := ringRank)
          params sourceErrorSampler candidate := by
    unfold averagedSourceErrorDiagonalChiSquareLoss
    apply Summable.tsum_le_tsum
    · intro sourceError
      exact mul_le_mul_of_nonneg_left
        (tvDist_fixedErrorDiagonal_le_chiSquareLoss
          params candidate sourceError)
        ENNReal.toReal_nonneg
    · exact Summable.of_finite
    · exact Summable.of_finite
  simpa only [jointDiagonalPairExperiment, jointMaskReplacedPairExperiment,
    Errors, Real, Ideal] using hMixture.trans hAverage

/-- Assemble a retained transformed-error/public-challenge pair into the selected TGSW entry. -/
def assembleDiagonalPair [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (pair :
      DiagonalErrorVector q degree ringRank params.levels ×
        DiagonalChallenge q degree ringRank params.levels) :
    RingGSWCiphertext q (degree + 1) ringRank params.levels :=
  TGSW.addGadget (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) candidate)
    (TLWE.batchAssemble (embedRingSecret q ringSecret) pair.2 0 pair.1)

/-- Ciphertext-level joint-collision presentation of the real selected diagonal. -/
noncomputable def jointCollisionDiagonalExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
  assembleDiagonalPair params candidate ringSecret <$>
    jointDiagonalPairExperiment (ringRank := ringRank)
      params sourceErrorSampler candidate

/-- Ciphertext-level joint-collision presentation after replacing the extracted public mask. -/
noncomputable def jointCollisionMaskReplacedDiagonalExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
  assembleDiagonalPair params candidate ringSecret <$>
    jointMaskReplacedPairExperiment (ringRank := ringRank)
      params sourceErrorSampler candidate

/-- The joint-collision presentation is exactly the existing difference-first diagonal operator
experiment. -/
theorem jointCollisionDiagonalExperiment_evalDist_eq_operator [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist
        (jointCollisionDiagonalExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate ringSecret) =
      evalDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret) := by
  let Difference : ProbComp
      (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  let Challenge : ProbComp (DiagonalChallenge q degree ringRank params.levels) :=
    $ᵗ DiagonalChallenge q degree ringRank params.levels
  let Errors : ProbComp (DiagonalErrorVector q degree ringRank params.levels) :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  let pairFinish := fun
      (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (challenge : DiagonalChallenge q degree ringRank params.levels)
      (sourceError : DiagonalErrorVector q degree ringRank params.levels) =>
    (rowOperator candidate (differenceEntryDigits params difference) sourceError,
      challengeOperator candidate (differenceEntryDigits params difference) challenge)
  let assemble := assembleDiagonalPair params candidate ringSecret
  have hPairs := jointDiagonalPairExperiment_evalDist_eq_differenceFirst
    (ringRank := ringRank) params sourceErrorSampler candidate
  have hMapped := evalDist_map_eq_of_evalDist_eq hPairs assemble
  calc
    _ = evalDist (do
        let difference ← Difference
        let challenge ← Challenge
        let sourceError ← Errors
        pure (assemble (pairFinish difference challenge sourceError))) := by
      simpa only [jointCollisionDiagonalExperiment, Difference, Challenge, Errors,
        pairFinish, assemble, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
        using hMapped
    _ = _ := by
      unfold operatorDiagonalExperiment
      simp only [TLWE.batchEncrypt, Difference, Challenge, Errors, bind_assoc, pure_bind]
      refine evalDist_bind_congr' Difference fun difference => ?_
      refine evalDist_bind_congr' Challenge fun challenge => ?_
      refine evalDist_bind_congr' Errors fun sourceError => ?_
      apply congrArg evalDist
      apply congrArg pure
      unfold assemble pairFinish assembleDiagonalPair
      rw [homogeneousTransform_batchAssemble_zero]

/-- The joint-collision mask-replaced presentation is exactly the existing experiment with an
independent uniform public challenge and the full mixed transformed-error marginal. -/
theorem jointCollisionMaskReplaced_evalDist_eq_maskReplaced [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist
        (jointCollisionMaskReplacedDiagonalExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate ringSecret) =
      evalDist
        (maskReplacedDiagonalExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate ringSecret) := by
  let MixedErrors : ProbComp (DiagonalErrorVector q degree ringRank params.levels) :=
    mixedDiagonalErrorSampler (ringRank := ringRank)
      params sourceErrorSampler candidate
  let Challenge : ProbComp (DiagonalChallenge q degree ringRank params.levels) :=
    $ᵗ DiagonalChallenge q degree ringRank params.levels
  let assemble := assembleDiagonalPair params candidate ringSecret
  have hPairs := jointMaskReplacedPairExperiment_evalDist_eq_mixedErrorFirst
    (ringRank := ringRank) params sourceErrorSampler candidate
  have hMapped := evalDist_map_eq_of_evalDist_eq hPairs assemble
  calc
    _ = evalDist (MixedErrors >>= fun transformedError =>
        Challenge >>= fun challenge => pure (assemble (transformedError, challenge))) := by
      simpa only [jointCollisionMaskReplacedDiagonalExperiment, MixedErrors, Challenge,
        assemble, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply] using hMapped
    _ = evalDist (Challenge >>= fun challenge =>
        MixedErrors >>= fun transformedError => pure (assemble (transformedError, challenge))) :=
      evalDist_bind_bind_swap MixedErrors Challenge
        (fun transformedError challenge => pure (assemble (transformedError, challenge)))
    _ = _ := by
      simp only [maskReplacedDiagonalExperiment, SamplerReplacement.independentPair,
        MixedErrors, Challenge, assemble, map_eq_bind_pure_comp]
      rfl

/-- Direct mask replacement for the actual selected-diagonal operator.  The bound retains the
error transformed by the same hidden difference, so it does not pay fixed-matrix rank failure. -/
theorem tvDist_operatorDiagonal_maskReplaced_le_jointCollision [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    tvDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
        (maskReplacedDiagonalExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate ringSecret) ≤
      averagedSourceErrorDiagonalCollisionLoss (ringRank := ringRank)
        params sourceErrorSampler candidate := by
  have hPair := tvDist_jointDiagonalPair_jointMaskReplaced_le
    (ringRank := ringRank) params sourceErrorSampler candidate
  have hMap := (tvDist_map_le (m := ProbComp)
    (assembleDiagonalPair params candidate ringSecret)
    (jointDiagonalPairExperiment (ringRank := ringRank)
      params sourceErrorSampler candidate)
    (jointMaskReplacedPairExperiment (ringRank := ringRank)
      params sourceErrorSampler candidate)).trans hPair
  change tvDist
      (jointCollisionDiagonalExperiment (ringRank := ringRank)
        params sourceErrorSampler candidate ringSecret)
      (jointCollisionMaskReplacedDiagonalExperiment (ringRank := ringRank)
        params sourceErrorSampler candidate ringSecret) ≤
    averagedSourceErrorDiagonalCollisionLoss (ringRank := ringRank)
      params sourceErrorSampler candidate at hMap
  unfold tvDist at hMap ⊢
  rw [jointCollisionDiagonalExperiment_evalDist_eq_operator
    params sourceErrorSampler candidate ringSecret] at hMap
  rw [jointCollisionMaskReplaced_evalDist_eq_maskReplaced
    params sourceErrorSampler candidate ringSecret] at hMap
  simpa only [jointCollisionDiagonalExperiment,
    jointCollisionMaskReplacedDiagonalExperiment] using hMap

/-- Ciphertext-level direct mask replacement through the explicit normalized fiber
chi-square budget. -/
theorem tvDist_operatorDiagonal_maskReplaced_le_jointChiSquare [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    tvDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
        (maskReplacedDiagonalExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate ringSecret) ≤
      averagedSourceErrorDiagonalChiSquareLoss (ringRank := ringRank)
        params sourceErrorSampler candidate := by
  have hPair := tvDist_jointDiagonalPair_jointMaskReplaced_le_chiSquare
    (ringRank := ringRank) params sourceErrorSampler candidate
  have hMap := (tvDist_map_le (m := ProbComp)
    (assembleDiagonalPair params candidate ringSecret)
    (jointDiagonalPairExperiment (ringRank := ringRank)
      params sourceErrorSampler candidate)
    (jointMaskReplacedPairExperiment (ringRank := ringRank)
      params sourceErrorSampler candidate)).trans hPair
  change tvDist
      (jointCollisionDiagonalExperiment (ringRank := ringRank)
        params sourceErrorSampler candidate ringSecret)
      (jointCollisionMaskReplacedDiagonalExperiment (ringRank := ringRank)
        params sourceErrorSampler candidate ringSecret) ≤
    averagedSourceErrorDiagonalChiSquareLoss (ringRank := ringRank)
      params sourceErrorSampler candidate at hMap
  unfold tvDist at hMap ⊢
  rw [jointCollisionDiagonalExperiment_evalDist_eq_operator
    params sourceErrorSampler candidate ringSecret] at hMap
  rw [jointCollisionMaskReplaced_evalDist_eq_maskReplaced
    params sourceErrorSampler candidate ringSecret] at hMap
  simpa only [jointCollisionDiagonalExperiment,
    jointCollisionMaskReplacedDiagonalExperiment] using hMap

/-- Direct selected-diagonal budget: side-information collision loss for the public mask plus
the existing distance from the complete mixed transformed-error marginal to target errors. -/
noncomputable def jointCollisionDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) : ℝ :=
  averagedSourceErrorDiagonalCollisionLoss (ringRank := ringRank)
      params sourceErrorSampler candidate +
    mixedDiagonalErrorDistance (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate

/-- Candidate-independent direct joint-collision budget. -/
noncomputable def worstCaseJointCollisionDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))) : ℝ :=
  max
    (jointCollisionDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler false)
    (jointCollisionDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler true)

/-- Selected-diagonal budget using the explicit normalized fiber chi-square estimate for the
public-mask hop and the exact mixed-error marginal distance for the error hop. -/
noncomputable def jointChiSquareDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) : ℝ :=
  averagedSourceErrorDiagonalChiSquareLoss (ringRank := ringRank)
      params sourceErrorSampler candidate +
    mixedDiagonalErrorDistance (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate

/-- Candidate-independent normalized fiber chi-square budget. -/
noncomputable def worstCaseJointChiSquareDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))) : ℝ :=
  max
    (jointChiSquareDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler false)
    (jointChiSquareDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler true)

theorem jointCollisionDiagonalOperatorLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    0 ≤ jointCollisionDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate :=
  add_nonneg
    (averagedSourceErrorDiagonalCollisionLoss_nonneg (ringRank := ringRank)
      params sourceErrorSampler candidate)
    (mixedDiagonalErrorDistance_nonneg (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate)

theorem worstCaseJointCollisionDiagonalOperatorLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))) :
    0 ≤ worstCaseJointCollisionDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler := by
  exact (jointCollisionDiagonalOperatorLoss_nonneg (ringRank := ringRank) params
    sourceErrorSampler targetErrorSampler false).trans (le_max_left _ _)

theorem jointChiSquareDiagonalOperatorLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    0 ≤ jointChiSquareDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate :=
  add_nonneg
    (averagedSourceErrorDiagonalChiSquareLoss_nonneg (ringRank := ringRank)
      params sourceErrorSampler candidate)
    (mixedDiagonalErrorDistance_nonneg (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate)

theorem worstCaseJointChiSquareDiagonalOperatorLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))) :
    0 ≤ worstCaseJointChiSquareDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler := by
  exact (jointChiSquareDiagonalOperatorLoss_nonneg (ringRank := ringRank) params
    sourceErrorSampler targetErrorSampler false).trans (le_max_left _ _)

/-- Selected-diagonal replacement theorem using the direct side-information collision route. -/
theorem tvDist_operatorDiagonalExperiment_target_le_jointCollision [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    tvDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
        (TGSW.encrypt ringRank params.levels targetErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate)) ≤
      jointCollisionDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate := by
  let Middle := maskReplacedDiagonalExperiment (ringRank := ringRank) params
    sourceErrorSampler candidate ringSecret
  let Target := TGSW.encrypt ringRank params.levels targetErrorSampler
    (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) candidate)
  calc
    _ ≤ tvDist
          (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
          Middle + tvDist Middle Target := tvDist_triangle _ _ _
    _ ≤ averagedSourceErrorDiagonalCollisionLoss (ringRank := ringRank)
          params sourceErrorSampler candidate +
        mixedDiagonalErrorDistance (ringRank := ringRank) params
          sourceErrorSampler targetErrorSampler candidate :=
      add_le_add
        (tvDist_operatorDiagonal_maskReplaced_le_jointCollision
          params sourceErrorSampler candidate ringSecret)
        (tvDist_maskReplacedDiagonal_target_le_mixedError
          params sourceErrorSampler targetErrorSampler candidate ringSecret)
    _ = _ := rfl

/-- Direct joint-collision reduction for the actual self-correlated diagonal entry. -/
theorem tvDist_diagonalExperiment_directEntry_le_jointCollision [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      jointCollisionDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler (hidden coordinate) := by
  have h := tvDist_operatorDiagonalExperiment_target_le_jointCollision
    params sourceErrorSampler targetErrorSampler (hidden coordinate) ringSecret
  unfold tvDist at h ⊢
  rw [diagonalExperiment_evalDist_eq_operator
    params sourceErrorSampler hidden ringSecret coordinate]
  unfold OffDiagonalNormalForm.directEntrySampler
  rw [← TGSW.encrypt_evalDist_eq_directEncrypt ringRank params.levels
    targetErrorSampler (embedRingSecret q ringSecret)
    (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) (hidden coordinate))]
  exact h

/-- Candidate-independent direct joint-collision bound for the whole-key diagonal certificate. -/
theorem tvDist_diagonalExperiment_directEntry_le_worstCaseJointCollision [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      worstCaseJointCollisionDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler := by
  have h := tvDist_diagonalExperiment_directEntry_le_jointCollision
    params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate
  cases hbit : hidden coordinate
  · exact h.trans (by
      simpa only [hbit, worstCaseJointCollisionDiagonalOperatorLoss] using
        (le_max_left
          (jointCollisionDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler false)
          (jointCollisionDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler true)))
  · exact h.trans (by
      simpa only [hbit, worstCaseJointCollisionDiagonalOperatorLoss] using
        (le_max_right
          (jointCollisionDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler false)
          (jointCollisionDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler true)))

/-- Selected-diagonal replacement theorem through the normalized finite-fiber chi-square
interface. -/
theorem tvDist_operatorDiagonalExperiment_target_le_jointChiSquare [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    tvDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
        (TGSW.encrypt ringRank params.levels targetErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate)) ≤
      jointChiSquareDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate := by
  let Middle := maskReplacedDiagonalExperiment (ringRank := ringRank) params
    sourceErrorSampler candidate ringSecret
  let Target := TGSW.encrypt ringRank params.levels targetErrorSampler
    (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) candidate)
  calc
    _ ≤ tvDist
          (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
          Middle + tvDist Middle Target := tvDist_triangle _ _ _
    _ ≤ averagedSourceErrorDiagonalChiSquareLoss (ringRank := ringRank)
          params sourceErrorSampler candidate +
        mixedDiagonalErrorDistance (ringRank := ringRank) params
          sourceErrorSampler targetErrorSampler candidate :=
      add_le_add
        (tvDist_operatorDiagonal_maskReplaced_le_jointChiSquare
          params sourceErrorSampler candidate ringSecret)
        (tvDist_maskReplacedDiagonal_target_le_mixedError
          params sourceErrorSampler targetErrorSampler candidate ringSecret)
    _ = _ := rfl

/-- Normalized finite-fiber chi-square reduction for the actual self-correlated diagonal
entry. -/
theorem tvDist_diagonalExperiment_directEntry_le_jointChiSquare [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      jointChiSquareDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler (hidden coordinate) := by
  have h := tvDist_operatorDiagonalExperiment_target_le_jointChiSquare
    params sourceErrorSampler targetErrorSampler (hidden coordinate) ringSecret
  unfold tvDist at h ⊢
  rw [diagonalExperiment_evalDist_eq_operator
    params sourceErrorSampler hidden ringSecret coordinate]
  unfold OffDiagonalNormalForm.directEntrySampler
  rw [← TGSW.encrypt_evalDist_eq_directEncrypt ringRank params.levels
    targetErrorSampler (embedRingSecret q ringSecret)
    (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) (hidden coordinate))]
  exact h

/-- Candidate-independent normalized finite-fiber chi-square bound for the whole-key diagonal
certificate. -/
theorem tvDist_diagonalExperiment_directEntry_le_worstCaseJointChiSquare [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      worstCaseJointChiSquareDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler := by
  have h := tvDist_diagonalExperiment_directEntry_le_jointChiSquare
    params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate
  cases hbit : hidden coordinate
  · exact h.trans (by
      simpa only [hbit, worstCaseJointChiSquareDiagonalOperatorLoss] using
        (le_max_left
          (jointChiSquareDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler false)
          (jointChiSquareDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler true)))
  · exact h.trans (by
      simpa only [hbit, worstCaseJointChiSquareDiagonalOperatorLoss] using
        (le_max_right
          (jointChiSquareDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler false)
          (jointChiSquareDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler true)))

/-- Construction-specific selected-diagonal bound from a support-wise collision-pair estimate
and an external estimate of the mixed transformed-error marginal. -/
theorem tvDist_operatorDiagonalExperiment_target_le_of_pairCollisionBound [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (ε mixedErrorBound : ℝ)
    (hpair : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      fixedErrorDiagonalPairCollisionBound params candidate sourceError ε)
    (hmixed : mixedDiagonalErrorDistance (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate ≤ mixedErrorBound) :
    tvDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
        (TGSW.encrypt ringRank params.levels targetErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate)) ≤
      Real.sqrt ε / 2 + mixedErrorBound := by
  exact (tvDist_operatorDiagonalExperiment_target_le_jointChiSquare
    params sourceErrorSampler targetErrorSampler candidate ringSecret).trans
      (add_le_add
        (averagedSourceErrorDiagonalChiSquareLoss_le_of_pairCollisionBound
          params sourceErrorSampler candidate ε hpair)
        hmixed)

/-- The pair-collision and mixed-error estimates bound the actual self-correlated selected
entry, uniformly over the hidden bit when supplied for both candidates. -/
theorem tvDist_diagonalExperiment_directEntry_le_of_pairCollisionBound [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (ε mixedErrorBound : ℝ)
    (hpair : ∀ candidate sourceError,
      sourceError ∈ support
        (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
          sourceErrorSampler) →
      fixedErrorDiagonalPairCollisionBound params candidate sourceError ε)
    (hmixed : ∀ candidate,
      mixedDiagonalErrorDistance (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate ≤ mixedErrorBound) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      Real.sqrt ε / 2 + mixedErrorBound := by
  have h := tvDist_operatorDiagonalExperiment_target_le_of_pairCollisionBound
    params sourceErrorSampler targetErrorSampler (hidden coordinate) ringSecret
    ε mixedErrorBound (fun sourceError hsource =>
      hpair (hidden coordinate) sourceError hsource) (hmixed (hidden coordinate))
  unfold tvDist at h ⊢
  rw [diagonalExperiment_evalDist_eq_operator
    params sourceErrorSampler hidden ringSecret coordinate]
  unfold OffDiagonalNormalForm.directEntrySampler
  rw [← TGSW.encrypt_evalDist_eq_directEncrypt ringRank params.levels
    targetErrorSampler (embedRingSecret q ringSecret)
    (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) (hidden coordinate))]
  exact h

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
