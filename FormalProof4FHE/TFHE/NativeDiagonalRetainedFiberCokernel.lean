/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDiagonalRetainedFiberSelfSlice

/-!
# Exact Cokernel Accounting in the Retained Native TFHE Fiber

The binary-rank envelope for the paired native row operator is sound but can be much too coarse:
one missing residue-field rank was previously charged by the cardinality of the complete native
coefficient ring.  The exact finite-group calculation depends instead on the cokernel cardinality
of the native operator.

For a paired row operator with row-space cardinality `N`, image cardinality `I`, and kernel
cardinality `K`, the homomorphism theorem gives `K * I = N^2`.  Thus

`K = N * (N / I)`.

After taking one independent row operator for every public ring-secret coordinate, the complete
challenge collision count is exactly the challenge-space cardinality times `(N / I)^ringRank`.
The challenge cardinality therefore cancels from the retained-fiber normalization.  What remains
to finish the statistical step is a distributional bound on the average native cokernel factor
inside each transformed-error fiber; no residue-rank relaxation is used in this file.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

variable {q degree ringRank : ℕ}

/-- Real-valued cardinality of the native paired-row cokernel.  The quotient is an integer by the
finite-group homomorphism theorem, but the real presentation is the one used by collision
accounting. -/
noncomputable def differencePairRowCokernelFactor [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ :=
  (Fintype.card
      (Fin (TGSW.rowCount ringRank params.levels) →
        RLWE.Rq q (degree + 1)) : ℝ) /
    differencePairRowImageCard params candidate leftDifference rightDifference

/-- The native paired-row image always contains zero, so its cardinality is positive. -/
theorem differencePairRowImageCard_pos [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    0 < differencePairRowImageCard params candidate
      leftDifference rightDifference := by
  unfold differencePairRowImageCard
  exact Fintype.card_pos

/-- The paired-row image is a subtype of the complete native row space. -/
theorem differencePairRowImageCard_le_rowCard [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    differencePairRowImageCard params candidate
        leftDifference rightDifference ≤
      Fintype.card
        (Fin (TGSW.rowCount ringRank params.levels) →
          RLWE.Rq q (degree + 1)) := by
  unfold differencePairRowImageCard
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

/-- A finite cokernel cardinality is at least one. -/
theorem one_le_differencePairRowCokernelFactor [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    1 ≤ differencePairRowCokernelFactor params candidate
      leftDifference rightDifference := by
  have himage : (0 : ℝ) < differencePairRowImageCard params candidate
      leftDifference rightDifference := by
    exact_mod_cast differencePairRowImageCard_pos params candidate
      leftDifference rightDifference
  unfold differencePairRowCokernelFactor
  apply (le_div_iff₀ himage).2
  simpa using (show
    (differencePairRowImageCard params candidate
        leftDifference rightDifference : ℝ) ≤
      Fintype.card
        (Fin (TGSW.rowCount ringRank params.levels) →
          RLWE.Rq q (degree + 1)) by
    exact_mod_cast differencePairRowImageCard_le_rowCard params candidate
      leftDifference rightDifference)

/-- The exact cokernel excess factor is nonnegative. -/
theorem differencePairRowCokernelFactor_pow_sub_one_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    0 ≤ (differencePairRowCokernelFactor params candidate
        leftDifference rightDifference) ^ ringRank - 1 := by
  have hpow : (1 : ℝ) ≤
      (differencePairRowCokernelFactor params candidate
        leftDifference rightDifference) ^ ringRank := by
    simpa using pow_le_pow_left₀ (by positivity)
      (one_le_differencePairRowCokernelFactor params candidate
        leftDifference rightDifference) ringRank
  linarith

/-- Exact row-level kernel/cokernel identity in the native coefficient ring. -/
theorem pairedRowZeroFiberCard_eq_rowCard_mul_differencePairRowCokernelFactor
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    (pairedRowZeroFiberCard candidate
        (differenceEntryDigits params leftDifference)
        (differenceEntryDigits params rightDifference) : ℝ) =
      (Fintype.card
          (Fin (TGSW.rowCount ringRank params.levels) →
            RLWE.Rq q (degree + 1)) : ℝ) *
        differencePairRowCokernelFactor params candidate
          leftDifference rightDifference := by
  let Row := Fin (TGSW.rowCount ringRank params.levels) →
    RLWE.Rq q (degree + 1)
  have hcardNat :
      pairedRowZeroFiberCard candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference) *
        differencePairRowImageCard params candidate
          leftDifference rightDifference =
      Fintype.card Row * Fintype.card Row := by
    calc
      pairedRowZeroFiberCard candidate
            (differenceEntryDigits params leftDifference)
            (differenceEntryDigits params rightDifference) *
          differencePairRowImageCard params candidate
            leftDifference rightDifference =
        Fintype.card (Row × Row) := by
          unfold differencePairRowImageCard
          exact pairedRowZeroFiberCard_mul_imageCard_eq_domainCard
            candidate
            (differenceEntryDigits params leftDifference)
            (differenceEntryDigits params rightDifference)
      _ = Fintype.card Row * Fintype.card Row := Fintype.card_prod Row Row
  have hcard :
      (pairedRowZeroFiberCard candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference) : ℝ) *
        (differencePairRowImageCard params candidate
          leftDifference rightDifference : ℝ) =
      (Fintype.card Row : ℝ) * (Fintype.card Row : ℝ) := by
    exact_mod_cast hcardNat
  have himage :
      (differencePairRowImageCard params candidate
        leftDifference rightDifference : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (differencePairRowImageCard_pos params candidate
        leftDifference rightDifference))
  unfold differencePairRowCokernelFactor
  change _ = (Fintype.card Row : ℝ) *
    ((Fintype.card Row : ℝ) /
      differencePairRowImageCard params candidate
        leftDifference rightDifference)
  calc
    (pairedRowZeroFiberCard candidate
        (differenceEntryDigits params leftDifference)
        (differenceEntryDigits params rightDifference) : ℝ) =
        ((Fintype.card Row : ℝ) * (Fintype.card Row : ℝ)) /
          differencePairRowImageCard params candidate
            leftDifference rightDifference :=
      (eq_div_iff himage).2 hcard
    _ = (Fintype.card Row : ℝ) *
        ((Fintype.card Row : ℝ) /
          differencePairRowImageCard params candidate
            leftDifference rightDifference) := by ring

/-- Exact complete-challenge collision count.  The only excess over the uniform challenge
baseline is the native row-cokernel factor, independently repeated `ringRank` times. -/
theorem differencePairChallengeCollisionCount_eq_challengeCard_mul_cokernelFactor_pow
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    differencePairChallengeCollisionCount params candidate
        leftDifference rightDifference =
      (Fintype.card
          (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
        (differencePairRowCokernelFactor params candidate
          leftDifference rightDifference) ^ ringRank := by
  let Row := Fin (TGSW.rowCount ringRank params.levels) →
    RLWE.Rq q (degree + 1)
  have hchallenge :
      Fintype.card (DiagonalChallenge q degree ringRank params.levels) =
        Fintype.card Row ^ ringRank := by
    change Fintype.card (Fin ringRank → Row) = Fintype.card Row ^ ringRank
    simp
  unfold differencePairChallengeCollisionCount
  rw [pairedChallengeCollisionCount_eq_rowZeroFiberCard_pow,
    pairedRowZeroFiberCard_eq_rowCard_mul_differencePairRowCokernelFactor]
  rw [mul_pow]
  norm_cast at hchallenge ⊢
  rw [hchallenge]

/-- Exact fixed-pair collision excess after factoring out the complete challenge space. -/
theorem differencePairChallengeCollisionExcess_eq_challengeCard_mul_cokernelExcess
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    differencePairChallengeCollisionExcess params candidate
        leftDifference rightDifference =
      (Fintype.card
          (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
        ((differencePairRowCokernelFactor params candidate
            leftDifference rightDifference) ^ ringRank - 1) := by
  unfold differencePairChallengeCollisionExcess
  rw [differencePairChallengeCollisionCount_eq_challengeCard_mul_cokernelFactor_pow]
  ring

/-- Full residue-field rank makes the native paired map surjective, so its exact cokernel factor
is one.  Consequently only rank-deficient pairs can contribute to the cokernel average. -/
theorem differencePairRowCokernelFactor_eq_one_of_binaryFullRank [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (fullRank :
      (differencePairBinaryTransposeMatrix params
        (leftDifference, rightDifference)).rank =
          TGSW.rowCount ringRank params.levels) :
    differencePairRowCokernelFactor params candidate
      leftDifference rightDifference = 1 := by
  have hsurjective : Function.Surjective
      (pairedRowDifferenceOperator candidate
        (differenceEntryDigits params leftDifference)
        (differenceEntryDigits params rightDifference)) :=
    pairedRowDifferenceOperator_surjective_of_differencePairBinaryFullRank
      params heven candidate leftDifference rightDifference localParity fullRank
  let transform := pairedRowDifferenceAddHom candidate
    (differenceEntryDigits params leftDifference)
    (differenceEntryDigits params rightDifference)
  let rangeEquiv : transform.range ≃
      (Fin (TGSW.rowCount ringRank params.levels) →
        RLWE.Rq q (degree + 1)) := {
    toFun := Subtype.val
    invFun := fun output => ⟨output, hsurjective output⟩
    left_inv := fun input => Subtype.ext rfl
    right_inv := fun _output => rfl
  }
  have hcard : Fintype.card transform.range =
      Fintype.card
        (Fin (TGSW.rowCount ringRank params.levels) →
          RLWE.Rq q (degree + 1)) :=
    Fintype.card_congr rangeEquiv
  unfold differencePairRowCokernelFactor differencePairRowImageCard
  change _ / (Fintype.card transform.range : ℝ) = 1
  rw [hcard]
  simp

/-- Sum of the exact native cokernel excess factors over distinct difference pairs retained in
one transformed-error fiber. -/
noncomputable def fixedErrorDiagonalDistinctPairCokernelExcess [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  ∑ leftDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels,
    ∑ rightDifference :
        RingGSWCiphertext q (degree + 1) ringRank params.levels,
      if fixedErrorDifferenceSide params candidate sourceError leftDifference =
            transformedError ∧
          fixedErrorDifferenceSide params candidate sourceError rightDifference =
            transformedError ∧
          leftDifference ≠ rightDifference then
        (differencePairRowCokernelFactor params candidate
            leftDifference rightDifference) ^ ringRank - 1
      else 0

/-- Every term in the exact retained distinct-pair cokernel sum is nonnegative. -/
theorem fixedErrorDiagonalDistinctPairCokernelExcess_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ fixedErrorDiagonalDistinctPairCokernelExcess
      params candidate sourceError transformedError := by
  unfold fixedErrorDiagonalDistinctPairCokernelExcess
  apply Finset.sum_nonneg
  intro leftDifference _
  apply Finset.sum_nonneg
  intro rightDifference _
  split_ifs
  · exact differencePairRowCokernelFactor_pow_sub_one_nonneg
      params candidate leftDifference rightDifference
  · exact le_rfl

/-- The exact retained distinct-pair collision excess is one challenge cardinality times the
matching sum of native cokernel excess factors. -/
theorem fixedErrorDiagonalDistinctPairCollisionExcess_eq_challengeCard_mul_cokernelExcess
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalDistinctPairCollisionExcess
        params candidate sourceError transformedError =
      (Fintype.card
          (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
        fixedErrorDiagonalDistinctPairCokernelExcess
          params candidate sourceError transformedError := by
  classical
  unfold fixedErrorDiagonalDistinctPairCollisionExcess
    fixedErrorDiagonalDistinctPairCokernelExcess
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro leftDifference _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rightDifference _
  by_cases hretained :
      fixedErrorDifferenceSide params candidate sourceError leftDifference =
            transformedError ∧
        fixedErrorDifferenceSide params candidate sourceError rightDifference =
            transformedError ∧
        leftDifference ≠ rightDifference
  · rcases hretained with ⟨hleft, hright, hne⟩
    simpa [hleft, hright, hne] using
      (differencePairChallengeCollisionExcess_eq_challengeCard_mul_cokernelExcess
        params candidate leftDifference rightDifference)
  · simp [hretained]

/-- The remaining quantitative statement for distinct pairs: conditioned on every retained
transformed-error fiber, the exact average native cokernel excess is bounded by
`collisionAverageBound`. -/
def fixedErrorDifferenceFiberDistinctCokernelAverageBound [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (collisionAverageBound : ℝ) : Prop :=
  ∀ transformedError : DiagonalErrorVector q degree ringRank params.levels,
    fixedErrorDiagonalDistinctPairCokernelExcess
        params candidate sourceError transformedError ≤
      (fixedErrorDifferenceFiberCard
          params candidate sourceError transformedError : ℝ) *
        collisionAverageBound

/-- An exact conditioned cokernel bound supplies the retained distinct-collision certificate
consumed by the native Pearson-loss security reduction. -/
theorem fixedErrorDifferenceFiberDistinctCollisionAverageBound_of_cokernel
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (collisionAverageBound : ℝ)
    (hCokernel : fixedErrorDifferenceFiberDistinctCokernelAverageBound
      params candidate sourceError collisionAverageBound) :
    fixedErrorDifferenceFiberDistinctCollisionAverageBound
      params candidate sourceError collisionAverageBound := by
  intro transformedError
  rw [fixedErrorDiagonalDistinctPairCollisionExcess_eq_challengeCard_mul_cokernelExcess]
  calc
    (Fintype.card
        (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
        fixedErrorDiagonalDistinctPairCokernelExcess
          params candidate sourceError transformedError ≤
      (Fintype.card
          (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
        ((fixedErrorDifferenceFiberCard
            params candidate sourceError transformedError : ℝ) *
          collisionAverageBound) := by
            exact mul_le_mul_of_nonneg_left
              (hCokernel transformedError) (by positivity)
    _ = (fixedErrorDifferenceFiberCard
          params candidate sourceError transformedError : ℝ) *
        (Fintype.card
          (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
        collisionAverageBound := by ring

/-! ## Distribution-weighted good/bad source-error split -/

/-- Challenge-normalized loss obtained from one retained self-kernel certificate and one exact
native distinct-pair cokernel certificate. -/
noncomputable def retainedCokernelGoodErrorLossBound [NeZero q]
    (params : Gadget.Base.Parameters q)
    (selfKernelAverageBound distinctCokernelAverageBound : ℝ) : ℝ :=
  Real.sqrt
        (selfKernelAverageBound /
          (Fintype.card
            (DiagonalChallenge q degree ringRank params.levels) : ℝ)) /
      2 +
    Real.sqrt
        (distinctCokernelAverageBound /
          (Fintype.card
            (DiagonalChallenge q degree ringRank params.levels) : ℝ)) /
      2

theorem retainedCokernelGoodErrorLossBound_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (selfKernelAverageBound distinctCokernelAverageBound : ℝ) :
    0 ≤ retainedCokernelGoodErrorLossBound (degree := degree) (ringRank := ringRank)
      params selfKernelAverageBound distinctCokernelAverageBound := by
  unfold retainedCokernelGoodErrorLossBound
  positivity

/-- On one good source-error vector, the retained self-kernel and exact native cokernel
certificates bound the actual fixed-error mask replacement. -/
theorem tvDist_fixedErrorDiagonal_le_retainedCokernelGoodErrorLossBound
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selfKernelAverageBound distinctCokernelAverageBound : ℝ)
    (hSelfNonneg : 0 ≤ selfKernelAverageBound)
    (hDistinctNonneg : 0 ≤ distinctCokernelAverageBound)
    (hSelf : fixedErrorDifferenceFiberKernelAverageBound
      params candidate sourceError selfKernelAverageBound)
    (hDistinct : fixedErrorDifferenceFiberDistinctCokernelAverageBound
      params candidate sourceError distinctCokernelAverageBound) :
    tvDist
        (FormalProof4FHE.ConditionalCollision.uniformJointImage
          (fixedErrorDiagonalSide params candidate sourceError)
          (fixedErrorDiagonalOutput params candidate))
        (FormalProof4FHE.ConditionalCollision.uniformSideIndependentOutput
          (Output := DiagonalChallenge q degree ringRank params.levels)
          (fixedErrorDiagonalSide params candidate sourceError)) ≤
      retainedCokernelGoodErrorLossBound (degree := degree) (ringRank := ringRank)
        params selfKernelAverageBound distinctCokernelAverageBound := by
  calc
    tvDist
        (FormalProof4FHE.ConditionalCollision.uniformJointImage
          (fixedErrorDiagonalSide params candidate sourceError)
          (fixedErrorDiagonalOutput params candidate))
        (FormalProof4FHE.ConditionalCollision.uniformSideIndependentOutput
          (Output := DiagonalChallenge q degree ringRank params.levels)
          (fixedErrorDiagonalSide params candidate sourceError)) ≤
      fixedErrorDiagonalChiSquareLoss params candidate sourceError :=
        tvDist_fixedErrorDiagonal_le_chiSquareLoss params candidate sourceError
    _ ≤ fixedErrorDiagonalSelfChiSquareLoss params candidate sourceError +
          fixedErrorDiagonalDistinctChiSquareLoss params candidate sourceError :=
      fixedErrorDiagonalChiSquareLoss_le_self_add_distinct
        params candidate sourceError
    _ ≤ retainedCokernelGoodErrorLossBound (degree := degree) (ringRank := ringRank)
          params selfKernelAverageBound distinctCokernelAverageBound := by
      unfold retainedCokernelGoodErrorLossBound
      apply add_le_add
      · exact fixedErrorDiagonalSelfChiSquareLoss_le_fiberAverage
          params candidate sourceError selfKernelAverageBound hSelfNonneg hSelf
      · exact fixedErrorDiagonalDistinctChiSquareLoss_le_fiberAverage
          params candidate sourceError distinctCokernelAverageBound hDistinctNonneg
            (fixedErrorDifferenceFiberDistinctCollisionAverageBound_of_cokernel
              params candidate sourceError distinctCokernelAverageBound hDistinct)

/-- Probability that a sampled native source-error vector fails a caller-supplied analytic
predicate.  This is the actual product error law used in the selected TFHE diagonal. -/
noncomputable def sourceErrorBadProbability [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (Good : DiagonalErrorVector q degree ringRank params.levels → Prop) : ℝ :=
  Pr[(fun sourceError ↦ ¬ Good sourceError) |
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
      sourceErrorSampler].toReal

theorem sourceErrorBadProbability_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (Good : DiagonalErrorVector q degree ringRank params.levels → Prop) :
    0 ≤ sourceErrorBadProbability params sourceErrorSampler Good :=
  ENNReal.toReal_nonneg

/-- Distribution-weighted retained-fiber theorem.  The exact self/cokernel estimates need hold
only on a good set of source errors.  Every exceptional vector is charged by its actual
probability, using only the universal `TV ≤ 1` bound.  In particular, this avoids the stronger
and unnecessary requirement that a cokernel estimate hold at every point in the sampler's
support. -/
theorem tvDist_jointDiagonalPair_jointMaskReplaced_le_goodBadRetainedCokernel
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (Good : DiagonalErrorVector q degree ringRank params.levels → Prop)
    (selfKernelAverageBound distinctCokernelAverageBound : ℝ)
    (hSelfNonneg : 0 ≤ selfKernelAverageBound)
    (hDistinctNonneg : 0 ≤ distinctCokernelAverageBound)
    (hSelf : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      Good sourceError →
        fixedErrorDifferenceFiberKernelAverageBound
          params candidate sourceError selfKernelAverageBound)
    (hDistinct : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      Good sourceError →
        fixedErrorDifferenceFiberDistinctCokernelAverageBound
          params candidate sourceError distinctCokernelAverageBound) :
    tvDist
        (jointDiagonalPairExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate)
        (jointMaskReplacedPairExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate) ≤
      retainedCokernelGoodErrorLossBound (degree := degree) (ringRank := ringRank)
          params selfKernelAverageBound distinctCokernelAverageBound +
        sourceErrorBadProbability params sourceErrorSampler Good := by
  classical
  let ErrorVector := DiagonalErrorVector q degree ringRank params.levels
  let Errors : ProbComp ErrorVector :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  let Real := fun sourceError : ErrorVector ↦
    FormalProof4FHE.ConditionalCollision.uniformJointImage
      (fixedErrorDiagonalSide params candidate sourceError)
      (fixedErrorDiagonalOutput params candidate)
  let Ideal := fun sourceError : ErrorVector ↦
    FormalProof4FHE.ConditionalCollision.uniformSideIndependentOutput
      (Output := DiagonalChallenge q degree ringRank params.levels)
      (fixedErrorDiagonalSide params candidate sourceError)
  let goodError := retainedCokernelGoodErrorLossBound (degree := degree) (ringRank := ringRank)
    params selfKernelAverageBound distinctCokernelAverageBound
  letI : Fintype ErrorVector := Fintype.ofFinite ErrorVector
  have hmass : (∑ sourceError : ErrorVector,
      Pr[= sourceError | Errors].toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun _ _ ↦ probOutput_ne_top),
      sum_probOutput_eq_one (by simp), ENNReal.toReal_one]
  have hbadMass :
      (∑ sourceError : ErrorVector,
          if ¬ Good sourceError then Pr[= sourceError | Errors].toReal else 0) =
        Pr[(fun sourceError ↦ ¬ Good sourceError) | Errors].toReal := by
    rw [probEvent_eq_sum_fintype_ite, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro sourceError _
      by_cases hsource : ¬ Good sourceError <;> simp [hsource]
    · intro sourceError _
      by_cases hsource : ¬ Good sourceError
      · simp [hsource, probOutput_ne_top]
      · simp [hsource]
  have hMixture := FormalProof4FHE.FiniteProduct.tvDist_bind_left_le_expectation
    Errors Real Ideal
  have hAverage :
      (∑' sourceError,
          Pr[= sourceError | Errors].toReal *
            tvDist (Real sourceError) (Ideal sourceError)) ≤
        goodError +
          Pr[(fun sourceError ↦ ¬ Good sourceError) | Errors].toReal := by
    rw [tsum_fintype]
    calc
      ∑ sourceError : ErrorVector,
          Pr[= sourceError | Errors].toReal *
            tvDist (Real sourceError) (Ideal sourceError) ≤
        ∑ sourceError : ErrorVector,
          Pr[= sourceError | Errors].toReal *
            (goodError + if ¬ Good sourceError then 1 else 0) := by
        apply Finset.sum_le_sum
        intro sourceError _
        by_cases hsupport : sourceError ∈ support Errors
        · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
          by_cases hgood : Good sourceError
          · have hpoint :=
              tvDist_fixedErrorDiagonal_le_retainedCokernelGoodErrorLossBound
                params candidate sourceError selfKernelAverageBound
                distinctCokernelAverageBound hSelfNonneg hDistinctNonneg
                (hSelf sourceError (by simpa [Errors, ErrorVector] using hsupport) hgood)
                (hDistinct sourceError (by simpa [Errors, ErrorVector] using hsupport) hgood)
            simpa [Real, Ideal, goodError, hgood] using hpoint
          · have hone : tvDist (Real sourceError) (Ideal sourceError) ≤ 1 :=
              tvDist_le_one _ _
            have hgoodError : 0 ≤ goodError := by
              exact retainedCokernelGoodErrorLossBound_nonneg (degree := degree)
                params selfKernelAverageBound distinctCokernelAverageBound
            simpa [hgood] using hone.trans (by linarith)
        · have hzero : Pr[= sourceError | Errors] = 0 :=
            probOutput_eq_zero_of_not_mem_support hsupport
          simp [hzero]
      _ = goodError +
          ∑ sourceError : ErrorVector,
            if ¬ Good sourceError then
              Pr[= sourceError | Errors].toReal else 0 := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        have hconstant :
            (∑ sourceError : ErrorVector,
              Pr[= sourceError | Errors].toReal * goodError) = goodError := by
          rw [← Finset.sum_mul, hmass, one_mul]
        rw [hconstant]
        congr 1
        apply Finset.sum_congr rfl
        intro sourceError _
        by_cases hsource : ¬ Good sourceError <;> simp [hsource]
      _ = goodError +
          Pr[(fun sourceError ↦ ¬ Good sourceError) | Errors].toReal := by
        rw [hbadMass]
  simpa only [jointDiagonalPairExperiment, jointMaskReplacedPairExperiment,
    sourceErrorBadProbability, Errors, Real, Ideal, goodError, ErrorVector] using
      hMixture.trans hAverage

/-- Ciphertext-level form of the distribution-weighted theorem.  It replaces the public mask
of the actual selected native diagonal while preserving its complete transformed-error
marginal. -/
theorem tvDist_operatorDiagonal_maskReplaced_le_goodBadRetainedCokernel
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (Good : DiagonalErrorVector q degree ringRank params.levels → Prop)
    (selfKernelAverageBound distinctCokernelAverageBound : ℝ)
    (hSelfNonneg : 0 ≤ selfKernelAverageBound)
    (hDistinctNonneg : 0 ≤ distinctCokernelAverageBound)
    (hSelf : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      Good sourceError →
        fixedErrorDifferenceFiberKernelAverageBound
          params candidate sourceError selfKernelAverageBound)
    (hDistinct : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      Good sourceError →
        fixedErrorDifferenceFiberDistinctCokernelAverageBound
          params candidate sourceError distinctCokernelAverageBound) :
    tvDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
        (maskReplacedDiagonalExperiment (ringRank := ringRank)
          params sourceErrorSampler candidate ringSecret) ≤
      retainedCokernelGoodErrorLossBound (degree := degree) (ringRank := ringRank)
          params selfKernelAverageBound distinctCokernelAverageBound +
        sourceErrorBadProbability params sourceErrorSampler Good := by
  have hPair :=
    tvDist_jointDiagonalPair_jointMaskReplaced_le_goodBadRetainedCokernel
      (ringRank := ringRank) params sourceErrorSampler candidate Good
      selfKernelAverageBound distinctCokernelAverageBound hSelfNonneg hDistinctNonneg
      hSelf hDistinct
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
        params sourceErrorSampler candidate ringSecret) ≤ _ at hMap
  unfold tvDist at hMap ⊢
  rw [jointCollisionDiagonalExperiment_evalDist_eq_operator
    params sourceErrorSampler candidate ringSecret] at hMap
  rw [jointCollisionMaskReplaced_evalDist_eq_maskReplaced
    params sourceErrorSampler candidate ringSecret] at hMap
  simpa only [jointCollisionDiagonalExperiment,
    jointCollisionMaskReplacedDiagonalExperiment] using hMap

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
