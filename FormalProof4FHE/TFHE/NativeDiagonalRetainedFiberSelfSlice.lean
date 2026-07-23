/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDiagonalGlobalBudgetObstruction
import FormalProof4FHE.TFHE.NativeDiagonalPairZeroFiber

/-!
# Equal-Difference Slice with the Retained Error Fiber Preserved

The source-independent global pair-collision relaxation is non-negligible because it retains the
equal-difference slice but discards the transformed-error fiber size.  This file keeps that fiber
normalization and isolates the same slice inside the exact conditional Pearson expression.

For one difference ciphertext, the self-pair challenge excess is exactly the challenge-space
cardinality times the nontrivial part of the row-operator kernel.  Consequently the challenge
cardinality cancels from the normalized retained-fiber expression.  The exact diagonal slice is
an average of kernel factors inside each transformed-error fiber, divided once by the complete
difference-space cardinality.  This explains formally why the constant lower bound for the
unconditional global relaxation does not lower-bound the exact retained-fiber loss.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

variable {q degree ringRank : ℕ}

/-- Cardinality of the kernel of the selected-diagonal row operator for one difference. -/
def differenceRowKernelCard [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℕ :=
  Fintype.card
    {value : Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1) //
      rowOperator candidate (differenceEntryDigits params difference) value = 0}

/-- Kernel contribution left after removing the uniform self-pair challenge baseline. -/
noncomputable def differenceSelfKernelFactor [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ :=
  (differenceRowKernelCard params candidate difference : ℝ) ^ ringRank - 1

theorem one_le_differenceRowKernelCard [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    1 ≤ differenceRowKernelCard params candidate difference := by
  let zeroValue :
      {value : Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1) //
        rowOperator candidate (differenceEntryDigits params difference) value = 0} :=
    ⟨0, (rowOperatorAddHom candidate
      (differenceEntryDigits params difference)).map_zero⟩
  exact Fintype.card_pos_iff.mpr ⟨zeroValue⟩

theorem differenceSelfKernelFactor_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    0 ≤ differenceSelfKernelFactor params candidate difference := by
  unfold differenceSelfKernelFactor
  have hcard : (1 : ℝ) ≤ differenceRowKernelCard params candidate difference := by
    exact_mod_cast one_le_differenceRowKernelCard params candidate difference
  have hpow : (1 : ℝ) ≤
      (differenceRowKernelCard params candidate difference : ℝ) ^ ringRank := by
    simpa using pow_le_pow_left₀ (by positivity) hcard ringRank
  linarith

/-- Exact self-pair collision excess.  The large challenge cardinality is a common factor; the
remaining factor is only the nontrivial row-kernel cardinality, raised to the number of public
challenge coordinates. -/
theorem differencePairChallengeCollisionExcess_self_eq_challengeCard_mul_kernelFactor
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    differencePairChallengeCollisionExcess params candidate difference difference =
      (Fintype.card (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
        differenceSelfKernelFactor params candidate difference := by
  let Row := Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)
  have hchallenge :
      Fintype.card (DiagonalChallenge q degree ringRank params.levels) =
        Fintype.card Row ^ ringRank := by
    change Fintype.card (Fin ringRank → Row) = Fintype.card Row ^ ringRank
    simp
  unfold differencePairChallengeCollisionExcess differencePairChallengeCollisionCount
    differenceSelfKernelFactor differenceRowKernelCard
  rw [pairedChallengeCollisionCount_eq_rowZeroFiberCard_pow,
    pairedRowZeroFiberCard_self_eq_card_mul_kernelCard, hchallenge]
  push_cast
  rw [mul_pow]
  ring

/-- Equal-difference contribution inside one retained transformed-error fiber. -/
noncomputable def fixedErrorDiagonalSelfPairCollisionExcess [NeZero q]
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
          leftDifference = rightDifference then
        differencePairChallengeCollisionExcess params candidate
          leftDifference rightDifference
      else 0

/-- Off-diagonal difference-pair contribution inside one retained transformed-error fiber. -/
noncomputable def fixedErrorDiagonalDistinctPairCollisionExcess [NeZero q]
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
        differencePairChallengeCollisionExcess params candidate
          leftDifference rightDifference
      else 0

/-- The exact retained-fiber excess splits into equal- and distinct-difference slices. -/
theorem fixedErrorDiagonalPairCollisionExcess_eq_self_add_distinct [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalPairCollisionExcess params candidate sourceError transformedError =
      fixedErrorDiagonalSelfPairCollisionExcess params candidate sourceError transformedError +
        fixedErrorDiagonalDistinctPairCollisionExcess params candidate sourceError
          transformedError := by
  classical
  unfold fixedErrorDiagonalPairCollisionExcess
    fixedErrorDiagonalSelfPairCollisionExcess
    fixedErrorDiagonalDistinctPairCollisionExcess
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro leftDifference _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rightDifference _
  by_cases hside :
      fixedErrorDifferenceSide params candidate sourceError leftDifference =
          transformedError ∧
        fixedErrorDifferenceSide params candidate sourceError rightDifference =
          transformedError
  · by_cases heq : leftDifference = rightDifference
    · simp [hside, heq]
    · simp [hside, heq]
  · have hself : ¬(
        fixedErrorDifferenceSide params candidate sourceError leftDifference =
            transformedError ∧
          fixedErrorDifferenceSide params candidate sourceError rightDifference =
            transformedError ∧
          leftDifference = rightDifference) := by
      intro h
      exact hside ⟨h.1, h.2.1⟩
    have hdistinct : ¬(
        fixedErrorDifferenceSide params candidate sourceError leftDifference =
            transformedError ∧
          fixedErrorDifferenceSide params candidate sourceError rightDifference =
            transformedError ∧
          leftDifference ≠ rightDifference) := by
      intro h
      exact hside ⟨h.1, h.2.1⟩
    simp [hside, hself, hdistinct]

/-- The equal-difference double sum reduces to one sum over retained differences. -/
theorem fixedErrorDiagonalSelfPairCollisionExcess_eq_sum [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalSelfPairCollisionExcess params candidate sourceError transformedError =
      ∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
        if fixedErrorDifferenceSide params candidate sourceError difference =
            transformedError then
          differencePairChallengeCollisionExcess params candidate difference difference
        else 0 := by
  classical
  unfold fixedErrorDiagonalSelfPairCollisionExcess
  apply Finset.sum_congr rfl
  intro leftDifference _
  rw [Finset.sum_eq_single leftDifference]
  · by_cases hside : fixedErrorDifferenceSide params candidate sourceError leftDifference =
        transformedError <;> simp [hside]
  · intro rightDifference _ hne
    have hne' : leftDifference ≠ rightDifference := fun heq => hne heq.symm
    simp [hne']
  · simp

/-- The equal-difference fiber excess is the challenge cardinality times the sum of kernel
factors in that retained transformed-error fiber. -/
theorem fixedErrorDiagonalSelfPairCollisionExcess_eq_challengeCard_mul_kernelSum
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalSelfPairCollisionExcess params candidate sourceError transformedError =
      (Fintype.card (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
        (∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
          if fixedErrorDifferenceSide params candidate sourceError difference =
              transformedError then
            differenceSelfKernelFactor params candidate difference
          else 0) := by
  rw [fixedErrorDiagonalSelfPairCollisionExcess_eq_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro difference _
  by_cases hside : fixedErrorDifferenceSide params candidate sourceError difference =
      transformedError
  · simp only [hside, if_true]
    exact differencePairChallengeCollisionExcess_self_eq_challengeCard_mul_kernelFactor
      params candidate difference
  · simp [hside]

/-- Normalized equal-difference contribution, with the exact retained-fiber denominator. -/
noncomputable def fixedErrorDiagonalNormalizedSelfPairCollisionExcess [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  ∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
    if fixedErrorDifferenceFiberCard params candidate sourceError transformedError = 0 then
      0
    else
      fixedErrorDiagonalSelfPairCollisionExcess params candidate sourceError transformedError /
        ((Fintype.card
              (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) *
          (Fintype.card
              (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
          (fixedErrorDifferenceFiberCard params candidate sourceError
            transformedError : ℝ))

/-- Normalized distinct-difference contribution, with the same exact retained-fiber
denominator. -/
noncomputable def fixedErrorDiagonalNormalizedDistinctPairCollisionExcess [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  ∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
    if fixedErrorDifferenceFiberCard params candidate sourceError transformedError = 0 then
      0
    else
      fixedErrorDiagonalDistinctPairCollisionExcess params candidate sourceError
          transformedError /
        ((Fintype.card
              (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) *
          (Fintype.card
              (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
          (fixedErrorDifferenceFiberCard params candidate sourceError
            transformedError : ℝ))

/-- Exact normalized Pearson excess is the sum of the retained equal- and distinct-difference
slices. -/
theorem fixedErrorDiagonalNormalizedPairCollisionExcess_eq_self_add_distinct [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalNormalizedPairCollisionExcess params candidate sourceError =
      fixedErrorDiagonalNormalizedSelfPairCollisionExcess params candidate sourceError +
        fixedErrorDiagonalNormalizedDistinctPairCollisionExcess params candidate sourceError := by
  unfold fixedErrorDiagonalNormalizedPairCollisionExcess
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess
    fixedErrorDiagonalNormalizedDistinctPairCollisionExcess
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro transformedError _
  by_cases hfiber :
      fixedErrorDifferenceFiberCard params candidate sourceError transformedError = 0
  · simp [hfiber]
  · simp only [hfiber, if_false]
    rw [fixedErrorDiagonalPairCollisionExcess_eq_self_add_distinct, add_div]

theorem fixedErrorDiagonalSelfPairCollisionExcess_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ fixedErrorDiagonalSelfPairCollisionExcess params candidate
      sourceError transformedError := by
  unfold fixedErrorDiagonalSelfPairCollisionExcess
  apply Finset.sum_nonneg
  intro leftDifference _
  apply Finset.sum_nonneg
  intro rightDifference _
  split_ifs
  · exact differencePairChallengeCollisionExcess_nonneg
      params candidate leftDifference rightDifference
  · exact le_rfl

theorem fixedErrorDiagonalDistinctPairCollisionExcess_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ fixedErrorDiagonalDistinctPairCollisionExcess params candidate
      sourceError transformedError := by
  unfold fixedErrorDiagonalDistinctPairCollisionExcess
  apply Finset.sum_nonneg
  intro leftDifference _
  apply Finset.sum_nonneg
  intro rightDifference _
  split_ifs
  · exact differencePairChallengeCollisionExcess_nonneg
      params candidate leftDifference rightDifference
  · exact le_rfl

theorem fixedErrorDiagonalNormalizedSelfPairCollisionExcess_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ fixedErrorDiagonalNormalizedSelfPairCollisionExcess
      params candidate sourceError := by
  unfold fixedErrorDiagonalNormalizedSelfPairCollisionExcess
  apply Finset.sum_nonneg
  intro transformedError _
  split_ifs
  · exact le_rfl
  · exact div_nonneg
      (fixedErrorDiagonalSelfPairCollisionExcess_nonneg
        params candidate sourceError transformedError) (by positivity)

theorem fixedErrorDiagonalNormalizedDistinctPairCollisionExcess_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ fixedErrorDiagonalNormalizedDistinctPairCollisionExcess
      params candidate sourceError := by
  unfold fixedErrorDiagonalNormalizedDistinctPairCollisionExcess
  apply Finset.sum_nonneg
  intro transformedError _
  split_ifs
  · exact le_rfl
  · exact div_nonneg
      (fixedErrorDiagonalDistinctPairCollisionExcess_nonneg
        params candidate sourceError transformedError) (by positivity)

/-- Square-root statistical loss carried by the retained equal-difference slice. -/
noncomputable def fixedErrorDiagonalSelfChiSquareLoss [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  Real.sqrt
      (fixedErrorDiagonalNormalizedSelfPairCollisionExcess
        params candidate sourceError) /
    2

/-- Square-root statistical loss carried by the retained distinct-difference slice. -/
noncomputable def fixedErrorDiagonalDistinctChiSquareLoss [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  Real.sqrt
      (fixedErrorDiagonalNormalizedDistinctPairCollisionExcess
        params candidate sourceError) /
    2

theorem fixedErrorDiagonalSelfChiSquareLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ fixedErrorDiagonalSelfChiSquareLoss params candidate sourceError := by
  unfold fixedErrorDiagonalSelfChiSquareLoss
  positivity

theorem fixedErrorDiagonalDistinctChiSquareLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ fixedErrorDiagonalDistinctChiSquareLoss params candidate sourceError := by
  unfold fixedErrorDiagonalDistinctChiSquareLoss
  positivity

/-- The exact fixed-error Pearson loss is bounded by the sum of the square-root losses of its
equal- and distinct-difference slices. -/
theorem fixedErrorDiagonalChiSquareLoss_le_self_add_distinct [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalChiSquareLoss params candidate sourceError ≤
      fixedErrorDiagonalSelfChiSquareLoss params candidate sourceError +
        fixedErrorDiagonalDistinctChiSquareLoss params candidate sourceError := by
  rw [fixedErrorDiagonalChiSquareLoss, fixedErrorDiagonalChiSquare_eq_normalizedPairCollisionExcess,
    fixedErrorDiagonalNormalizedPairCollisionExcess_eq_self_add_distinct]
  unfold fixedErrorDiagonalSelfChiSquareLoss fixedErrorDiagonalDistinctChiSquareLoss
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply (Real.sqrt_le_left
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
  rw [add_sq,
    Real.sq_sqrt (fixedErrorDiagonalNormalizedSelfPairCollisionExcess_nonneg
      params candidate sourceError),
    Real.sq_sqrt (fixedErrorDiagonalNormalizedDistinctPairCollisionExcess_nonneg
      params candidate sourceError)]
  nlinarith [mul_nonneg
    (Real.sqrt_nonneg
      (fixedErrorDiagonalNormalizedSelfPairCollisionExcess
        params candidate sourceError))
    (Real.sqrt_nonneg
      (fixedErrorDiagonalNormalizedDistinctPairCollisionExcess
        params candidate sourceError))]

/-- Source-error average of the retained equal-difference square-root loss. -/
noncomputable def averagedSourceErrorDiagonalSelfChiSquareLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) : ℝ :=
  ∑' sourceError : DiagonalErrorVector q degree ringRank params.levels,
    Pr[= sourceError |
      ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler].toReal *
      fixedErrorDiagonalSelfChiSquareLoss params candidate sourceError

/-- Source-error average of the retained distinct-difference square-root loss. -/
noncomputable def averagedSourceErrorDiagonalDistinctChiSquareLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) : ℝ :=
  ∑' sourceError : DiagonalErrorVector q degree ringRank params.levels,
    Pr[= sourceError |
      ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler].toReal *
      fixedErrorDiagonalDistinctChiSquareLoss params candidate sourceError

theorem averagedSourceErrorDiagonalSelfChiSquareLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    0 ≤ averagedSourceErrorDiagonalSelfChiSquareLoss (ringRank := ringRank)
      params sourceErrorSampler candidate := by
  unfold averagedSourceErrorDiagonalSelfChiSquareLoss
  exact tsum_nonneg fun sourceError =>
    mul_nonneg ENNReal.toReal_nonneg
      (fixedErrorDiagonalSelfChiSquareLoss_nonneg params candidate sourceError)

theorem averagedSourceErrorDiagonalDistinctChiSquareLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    0 ≤ averagedSourceErrorDiagonalDistinctChiSquareLoss (ringRank := ringRank)
      params sourceErrorSampler candidate := by
  unfold averagedSourceErrorDiagonalDistinctChiSquareLoss
  exact tsum_nonneg fun sourceError =>
    mul_nonneg ENNReal.toReal_nonneg
      (fixedErrorDiagonalDistinctChiSquareLoss_nonneg params candidate sourceError)

/-- The exact averaged native mask loss is controlled by the two retained-fiber slices. -/
theorem averagedSourceErrorDiagonalChiSquareLoss_le_self_add_distinct [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    averagedSourceErrorDiagonalChiSquareLoss (ringRank := ringRank)
        params sourceErrorSampler candidate ≤
      averagedSourceErrorDiagonalSelfChiSquareLoss (ringRank := ringRank)
          params sourceErrorSampler candidate +
        averagedSourceErrorDiagonalDistinctChiSquareLoss (ringRank := ringRank)
          params sourceErrorSampler candidate := by
  classical
  letI : Fintype (DiagonalErrorVector q degree ringRank params.levels) :=
    Fintype.ofFinite _
  unfold averagedSourceErrorDiagonalChiSquareLoss
    averagedSourceErrorDiagonalSelfChiSquareLoss
    averagedSourceErrorDiagonalDistinctChiSquareLoss
  simp only [tsum_fintype]
  calc
    ∑ sourceError : DiagonalErrorVector q degree ringRank params.levels,
        Pr[= sourceError |
          ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
            sourceErrorSampler].toReal *
          fixedErrorDiagonalChiSquareLoss params candidate sourceError ≤
      ∑ sourceError : DiagonalErrorVector q degree ringRank params.levels,
        Pr[= sourceError |
          ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
            sourceErrorSampler].toReal *
          (fixedErrorDiagonalSelfChiSquareLoss params candidate sourceError +
            fixedErrorDiagonalDistinctChiSquareLoss params candidate sourceError) := by
      apply Finset.sum_le_sum
      intro sourceError _
      exact mul_le_mul_of_nonneg_left
        (fixedErrorDiagonalChiSquareLoss_le_self_add_distinct
          params candidate sourceError) ENNReal.toReal_nonneg
    _ = _ := by
      simp_rw [mul_add]
      exact Finset.sum_add_distrib

/-- Kernel-only form of the normalized equal-difference slice.  The complete challenge
cardinality cancels exactly; retaining the side-fiber size is essential for this identity. -/
theorem fixedErrorDiagonalNormalizedSelfPairCollisionExcess_eq_kernelFiberAverage
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess params candidate sourceError =
      ∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
        if fixedErrorDifferenceFiberCard params candidate sourceError transformedError = 0 then
          0
        else
          (∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
              if fixedErrorDifferenceSide params candidate sourceError difference =
                  transformedError then
                differenceSelfKernelFactor params candidate difference
              else 0) /
            ((Fintype.card
                (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) *
              (fixedErrorDifferenceFiberCard params candidate sourceError
                transformedError : ℝ)) := by
  unfold fixedErrorDiagonalNormalizedSelfPairCollisionExcess
  apply Finset.sum_congr rfl
  intro transformedError _
  by_cases hfiber :
      fixedErrorDifferenceFiberCard params candidate sourceError transformedError = 0
  · simp [hfiber]
  · simp only [hfiber, if_false]
    rw [fixedErrorDiagonalSelfPairCollisionExcess_eq_challengeCard_mul_kernelSum]
    have hD : (0 : ℝ) < Fintype.card
        (RingGSWCiphertext q (degree + 1) ringRank params.levels) := by
      exact_mod_cast Fintype.card_pos
    have hC : (0 : ℝ) < Fintype.card
        (DiagonalChallenge q degree ringRank params.levels) := by
      exact_mod_cast Fintype.card_pos
    have hK : (0 : ℝ) <
        fixedErrorDifferenceFiberCard params candidate sourceError transformedError := by
      exact_mod_cast Nat.pos_of_ne_zero hfiber
    field_simp [hD.ne', hC.ne', hK.ne']

/-- Number of transformed-error values actually reached by the fixed source error. -/
def fixedErrorDifferenceNonemptyFiberCount [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) : ℕ :=
  (Finset.univ.filter fun transformedError :
      DiagonalErrorVector q degree ringRank params.levels =>
    fixedErrorDifferenceFiberCard params candidate sourceError transformedError ≠ 0).card

/-- A distribution-aware kernel certificate.  It bounds the average self-kernel factor inside
each retained transformed-error fiber, rather than every difference ciphertext pointwise. -/
def fixedErrorDifferenceFiberKernelAverageBound [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (kernelAverageBound : ℝ) : Prop :=
  ∀ transformedError : DiagonalErrorVector q degree ringRank params.levels,
    (∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
        if fixedErrorDifferenceSide params candidate sourceError difference =
            transformedError then
          differenceSelfKernelFactor params candidate difference
        else 0) ≤
      (fixedErrorDifferenceFiberCard params candidate sourceError transformedError : ℝ) *
        kernelAverageBound

/-- A uniform pointwise kernel-factor bound controls the kernel sum in every retained fiber by
that fiber's exact cardinality. -/
theorem fixedErrorDifferenceKernelSum_le_fiberCard_mul
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (kernelBound : ℝ)
    (hKernel : ∀ difference :
        RingGSWCiphertext q (degree + 1) ringRank params.levels,
      differenceSelfKernelFactor params candidate difference ≤ kernelBound) :
    (∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
        if fixedErrorDifferenceSide params candidate sourceError difference =
            transformedError then
          differenceSelfKernelFactor params candidate difference
        else 0) ≤
      (fixedErrorDifferenceFiberCard params candidate sourceError transformedError : ℝ) *
        kernelBound := by
  classical
  calc
    (∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
        if fixedErrorDifferenceSide params candidate sourceError difference =
            transformedError then
          differenceSelfKernelFactor params candidate difference
        else 0) ≤
        ∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
          if fixedErrorDifferenceSide params candidate sourceError difference =
              transformedError then kernelBound else 0 := by
      apply Finset.sum_le_sum
      intro difference _
      by_cases hside : fixedErrorDifferenceSide params candidate sourceError difference =
          transformedError
      · simpa [hside] using hKernel difference
      · simp [hside]
    _ = (fixedErrorDifferenceFiberCard params candidate sourceError
          transformedError : ℝ) * kernelBound := by
      unfold fixedErrorDifferenceFiberCard FormalProof4FHE.ConditionalCollision.sideFiberCard
      simp

/-- A pointwise kernel-factor bound supplies the stronger retained-fiber average certificate. -/
theorem fixedErrorDifferenceFiberKernelAverageBound_of_pointwise
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (kernelBound : ℝ)
    (hKernel : ∀ difference :
        RingGSWCiphertext q (degree + 1) ringRank params.levels,
      differenceSelfKernelFactor params candidate difference ≤ kernelBound) :
    fixedErrorDifferenceFiberKernelAverageBound
      params candidate sourceError kernelBound := by
  intro transformedError
  exact fixedErrorDifferenceKernelSum_le_fiberCard_mul
    params candidate sourceError transformedError kernelBound hKernel

/-- Quantitative retained-fiber bound from a conditional average-kernel certificate.  Unlike the
obstructed global relaxation, it pays only the number of nonempty transformed-error fibers, not
the complete difference-space cardinality, and contains no challenge-cardinality factor. -/
theorem fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_nonemptyFiberCount_mul_of_fiberAverage
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (kernelAverageBound : ℝ)
    (hKernelAverage : fixedErrorDifferenceFiberKernelAverageBound
      params candidate sourceError kernelAverageBound) :
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess params candidate sourceError ≤
      (fixedErrorDifferenceNonemptyFiberCount params candidate sourceError : ℝ) *
        (kernelAverageBound /
          (Fintype.card
            (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ)) := by
  classical
  rw [fixedErrorDiagonalNormalizedSelfPairCollisionExcess_eq_kernelFiberAverage]
  let D : ℝ := Fintype.card
    (RingGSWCiphertext q (degree + 1) ringRank params.levels)
  let K := fun transformedError :
      DiagonalErrorVector q degree ringRank params.levels =>
    fixedErrorDifferenceFiberCard params candidate sourceError transformedError
  let S := fun transformedError :
      DiagonalErrorVector q degree ringRank params.levels =>
    ∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
      if fixedErrorDifferenceSide params candidate sourceError difference =
          transformedError then
        differenceSelfKernelFactor params candidate difference
      else 0
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast Fintype.card_pos
  calc
    (∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
      if K transformedError = 0 then 0
      else S transformedError / (D * (K transformedError : ℝ))) ≤
        ∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
          if K transformedError = 0 then 0 else kernelAverageBound / D := by
      apply Finset.sum_le_sum
      intro transformedError _
      by_cases hfiber : K transformedError = 0
      · simp [hfiber]
      · simp only [hfiber, if_false]
        have hK : (0 : ℝ) < K transformedError := by
          exact_mod_cast Nat.pos_of_ne_zero hfiber
        apply (div_le_iff₀ (mul_pos hD hK)).2
        calc
          S transformedError ≤
              (K transformedError : ℝ) * kernelAverageBound := by
            exact hKernelAverage transformedError
          _ = kernelAverageBound / D * (D * (K transformedError : ℝ)) := by
            field_simp [hD.ne']
    _ = (fixedErrorDifferenceNonemptyFiberCount params candidate sourceError : ℝ) *
          (kernelAverageBound / D) := by
      unfold fixedErrorDifferenceNonemptyFiberCount
      have hsum :
          (∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
            if K transformedError = 0 then 0 else kernelAverageBound / D) =
            ∑ transformedError ∈
                Finset.univ.filter (fun transformedError :
                  DiagonalErrorVector q degree ringRank params.levels =>
                    K transformedError ≠ 0),
              kernelAverageBound / D := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro transformedError _
        by_cases hfiber : K transformedError = 0 <;> simp [hfiber]
      rw [hsum]
      simp [K]

/-- Pointwise specialization of the retained-fiber average-kernel bound. -/
theorem fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_nonemptyFiberCount_mul
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (kernelBound : ℝ)
    (hKernel : ∀ difference :
        RingGSWCiphertext q (degree + 1) ringRank params.levels,
      differenceSelfKernelFactor params candidate difference ≤ kernelBound) :
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess params candidate sourceError ≤
      (fixedErrorDifferenceNonemptyFiberCount params candidate sourceError : ℝ) *
        (kernelBound /
          (Fintype.card
            (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ)) :=
  fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_nonemptyFiberCount_mul_of_fiberAverage
    params candidate sourceError kernelBound
      (fixedErrorDifferenceFiberKernelAverageBound_of_pointwise
        params candidate sourceError kernelBound hKernel)

/-- The number of reached transformed-error fibers is at most the complete transformed-error
space. -/
theorem fixedErrorDifferenceNonemptyFiberCount_le_card [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDifferenceNonemptyFiberCount params candidate sourceError ≤
      Fintype.card (DiagonalErrorVector q degree ringRank params.levels) := by
  unfold fixedErrorDifferenceNonemptyFiberCount
  simpa using
    (Finset.card_filter_le
      (Finset.univ : Finset (DiagonalErrorVector q degree ringRank params.levels))
      (fun transformedError =>
        fixedErrorDifferenceFiberCard params candidate sourceError transformedError ≠ 0))

/-- A native difference ciphertext is exactly a public challenge matrix paired with one body
vector, whose carrier is the transformed-error space. -/
theorem differenceCiphertextCard_eq_challengeCard_mul_errorCard [NeZero q]
    (params : Gadget.Base.Parameters q) :
    Fintype.card
        (RingGSWCiphertext q (degree + 1) ringRank params.levels) =
      Fintype.card (DiagonalChallenge q degree ringRank params.levels) *
        Fintype.card (DiagonalErrorVector q degree ringRank params.levels) := by
  simp [Fintype.card_prod]

/-- Clean retained-fiber self bound.  A conditional average-kernel factor `B` costs only
`B / |Challenge|`; the complete error-vector cardinality cancels against the body component of
the hidden difference ciphertext. -/
theorem fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_fiberAverage_div_challengeCard
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (kernelAverageBound : ℝ) (hKernelAverageBound : 0 ≤ kernelAverageBound)
    (hKernelAverage : fixedErrorDifferenceFiberKernelAverageBound
      params candidate sourceError kernelAverageBound) :
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess params candidate sourceError ≤
      kernelAverageBound /
        (Fintype.card (DiagonalChallenge q degree ringRank params.levels) : ℝ) := by
  let C : ℝ := Fintype.card (DiagonalChallenge q degree ringRank params.levels)
  let E : ℝ := Fintype.card (DiagonalErrorVector q degree ringRank params.levels)
  let D : ℝ :=
    Fintype.card (RingGSWCiphertext q (degree + 1) ringRank params.levels)
  have hC : 0 < C := by
    dsimp [C]
    exact_mod_cast Fintype.card_pos
  have hE : 0 < E := by
    dsimp [E]
    exact_mod_cast Fintype.card_pos
  have hD : D = C * E := by
    dsimp [D, C, E]
    exact_mod_cast
      differenceCiphertextCard_eq_challengeCard_mul_errorCard
        (degree := degree) (ringRank := ringRank) params
  have hcount :
      (fixedErrorDifferenceNonemptyFiberCount
          params candidate sourceError : ℝ) ≤ E := by
    dsimp [E]
    exact_mod_cast fixedErrorDifferenceNonemptyFiberCount_le_card
      params candidate sourceError
  calc
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess
        params candidate sourceError ≤
      (fixedErrorDifferenceNonemptyFiberCount
          params candidate sourceError : ℝ) *
        (kernelAverageBound / D) :=
      fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_nonemptyFiberCount_mul_of_fiberAverage
        params candidate sourceError kernelAverageBound hKernelAverage
    _ ≤ E * (kernelAverageBound / D) := by
      exact mul_le_mul_of_nonneg_right hcount
        (div_nonneg hKernelAverageBound (le_of_lt (by
          rw [hD]
          positivity)))
    _ = kernelAverageBound / C := by
      rw [hD]
      field_simp [hC.ne', hE.ne']

/-- Square-root statistical form of the retained-fiber average-kernel certificate. -/
theorem fixedErrorDiagonalSelfChiSquareLoss_le_fiberAverage
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (kernelAverageBound : ℝ) (hKernelAverageBound : 0 ≤ kernelAverageBound)
    (hKernelAverage : fixedErrorDifferenceFiberKernelAverageBound
      params candidate sourceError kernelAverageBound) :
    fixedErrorDiagonalSelfChiSquareLoss params candidate sourceError ≤
      Real.sqrt
          (kernelAverageBound /
            (Fintype.card
              (DiagonalChallenge q degree ringRank params.levels) : ℝ)) /
        2 := by
  unfold fixedErrorDiagonalSelfChiSquareLoss
  gcongr
  exact
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_fiberAverage_div_challengeCard
      params candidate sourceError kernelAverageBound hKernelAverageBound hKernelAverage

/-- A support-wise conditional average-kernel certificate bounds the complete source-error
average by the same challenge-normalized square-root quantity. -/
theorem averagedSourceErrorDiagonalSelfChiSquareLoss_le_fiberAverage
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) (kernelAverageBound : ℝ)
    (hKernelAverageBound : 0 ≤ kernelAverageBound)
    (hKernelAverage : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      fixedErrorDifferenceFiberKernelAverageBound
        params candidate sourceError kernelAverageBound) :
    averagedSourceErrorDiagonalSelfChiSquareLoss (ringRank := ringRank)
        params sourceErrorSampler candidate ≤
      Real.sqrt
          (kernelAverageBound /
            (Fintype.card
              (DiagonalChallenge q degree ringRank params.levels) : ℝ)) /
        2 := by
  let ErrorVector := DiagonalErrorVector q degree ringRank params.levels
  let Errors : ProbComp ErrorVector :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  letI : Fintype ErrorVector := Fintype.ofFinite ErrorVector
  have hmass : (∑ sourceError : ErrorVector,
      Pr[= sourceError | Errors].toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun _ _ => probOutput_ne_top),
      sum_probOutput_eq_one (by simp), ENNReal.toReal_one]
  unfold averagedSourceErrorDiagonalSelfChiSquareLoss
  rw [tsum_fintype]
  calc
    ∑ sourceError : ErrorVector,
        Pr[= sourceError | Errors].toReal *
          fixedErrorDiagonalSelfChiSquareLoss params candidate sourceError ≤
      ∑ sourceError : ErrorVector,
        Pr[= sourceError | Errors].toReal *
          (Real.sqrt
              (kernelAverageBound /
                (Fintype.card
                  (DiagonalChallenge q degree ringRank params.levels) : ℝ)) /
            2) := by
      apply Finset.sum_le_sum
      intro sourceError _
      by_cases hsource : sourceError ∈ support Errors
      · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        apply fixedErrorDiagonalSelfChiSquareLoss_le_fiberAverage
        · exact hKernelAverageBound
        · exact hKernelAverage sourceError (by
            simpa [Errors, ErrorVector] using hsource)
      · have hzero : Pr[= sourceError | Errors] = 0 :=
          probOutput_eq_zero_of_not_mem_support hsource
        simp [hzero]
    _ = (∑ sourceError : ErrorVector,
        Pr[= sourceError | Errors].toReal) *
          (Real.sqrt
              (kernelAverageBound /
                (Fintype.card
                  (DiagonalChallenge q degree ringRank params.levels) : ℝ)) /
            2) := by
      rw [Finset.sum_mul]
    _ = Real.sqrt
          (kernelAverageBound /
            (Fintype.card
              (DiagonalChallenge q degree ringRank params.levels) : ℝ)) /
        2 := by rw [hmass, one_mul]

/-- A retained-fiber certificate for distinct difference pairs.  Inside each transformed-error
fiber, their total challenge-collision excess is at most the number of retained first differences
times one challenge cardinality times `collisionAverageBound`. -/
def fixedErrorDifferenceFiberDistinctCollisionAverageBound [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (collisionAverageBound : ℝ) : Prop :=
  ∀ transformedError : DiagonalErrorVector q degree ringRank params.levels,
    fixedErrorDiagonalDistinctPairCollisionExcess
        params candidate sourceError transformedError ≤
      (fixedErrorDifferenceFiberCard
          params candidate sourceError transformedError : ℝ) *
        (Fintype.card
          (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
        collisionAverageBound

/-- Rank-sensitive envelope summed only over distinct difference pairs in one retained
transformed-error fiber.  In contrast with the source-independent global rank budget, both side
constraints remain inside the sum. -/
noncomputable def fixedErrorDiagonalDistinctPairBinaryRankCollisionEnvelope [NeZero q]
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
        differencePairBinaryRankCollisionEnvelope params
          (leftDifference, rightDifference)
      else 0

/-- Every exact retained-fiber distinct collision sum is bounded by the matching conditioned
binary-rank envelope.  No pair outside the retained transformed-error fiber is charged. -/
theorem fixedErrorDiagonalDistinctPairCollisionExcess_le_binaryRankEnvelope
    [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalDistinctPairCollisionExcess
        params candidate sourceError transformedError ≤
      fixedErrorDiagonalDistinctPairBinaryRankCollisionEnvelope
        params candidate sourceError transformedError := by
  classical
  unfold fixedErrorDiagonalDistinctPairCollisionExcess
    fixedErrorDiagonalDistinctPairBinaryRankCollisionEnvelope
  apply Finset.sum_le_sum
  intro leftDifference _
  apply Finset.sum_le_sum
  intro rightDifference _
  by_cases hretained :
      fixedErrorDifferenceSide params candidate sourceError leftDifference =
            transformedError ∧
        fixedErrorDifferenceSide params candidate sourceError rightDifference =
            transformedError ∧
        leftDifference ≠ rightDifference
  · rcases hretained with ⟨hleft, hright, hne⟩
    simpa [hleft, hright, hne] using
      (differencePairChallengeCollisionExcess_le_binaryRankEnvelope
        params heven candidate localParity leftDifference rightDifference)
  · simp [hretained]

/-- Finite rank-profile certificate required inside every retained transformed-error fiber.  Its
normalization is exactly the one consumed by the distinct collision-average certificate. -/
def fixedErrorDifferenceFiberDistinctBinaryRankEnvelopeAverageBound [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (collisionAverageBound : ℝ) : Prop :=
  ∀ transformedError : DiagonalErrorVector q degree ringRank params.levels,
    fixedErrorDiagonalDistinctPairBinaryRankCollisionEnvelope
        params candidate sourceError transformedError ≤
      (fixedErrorDifferenceFiberCard
          params candidate sourceError transformedError : ℝ) *
        (Fintype.card
          (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
        collisionAverageBound

/-- A conditioned binary-rank-envelope certificate supplies the exact retained-fiber distinct
collision certificate.  This is the bridge from the native paired-rank analysis to the Pearson
loss used by the security reduction. -/
theorem fixedErrorDifferenceFiberDistinctCollisionAverageBound_of_binaryRankEnvelope
    [NeZero q]
    (params : Gadget.Base.Parameters q) (heven : 2 ∣ q)
    (candidate : Bool)
    (localParity : IsLocalHom
      (rqParityEval heven (Nat.succ_pos degree)))
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (collisionAverageBound : ℝ)
    (hRankEnvelope :
      fixedErrorDifferenceFiberDistinctBinaryRankEnvelopeAverageBound
        params candidate sourceError collisionAverageBound) :
    fixedErrorDifferenceFiberDistinctCollisionAverageBound
      params candidate sourceError collisionAverageBound := by
  intro transformedError
  exact
    (fixedErrorDiagonalDistinctPairCollisionExcess_le_binaryRankEnvelope
      params heven candidate localParity sourceError transformedError).trans
        (hRankEnvelope transformedError)

/-- Before the native ciphertext cardinalities are simplified, a distinct-pair fiber-average
certificate pays only the number of reached transformed-error fibers. -/
theorem fixedErrorDiagonalNormalizedDistinctPairCollisionExcess_le_nonemptyFiberCount_mul_of_fiberAverage
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (collisionAverageBound : ℝ)
    (hCollisionAverage : fixedErrorDifferenceFiberDistinctCollisionAverageBound
      params candidate sourceError collisionAverageBound) :
    fixedErrorDiagonalNormalizedDistinctPairCollisionExcess
        params candidate sourceError ≤
      (fixedErrorDifferenceNonemptyFiberCount params candidate sourceError : ℝ) *
        (collisionAverageBound /
          (Fintype.card
            (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ)) := by
  classical
  unfold fixedErrorDiagonalNormalizedDistinctPairCollisionExcess
  let D : ℝ := Fintype.card
    (RingGSWCiphertext q (degree + 1) ringRank params.levels)
  let C : ℝ := Fintype.card
    (DiagonalChallenge q degree ringRank params.levels)
  let K := fun transformedError :
      DiagonalErrorVector q degree ringRank params.levels =>
    fixedErrorDifferenceFiberCard params candidate sourceError transformedError
  let E := fun transformedError :
      DiagonalErrorVector q degree ringRank params.levels =>
    fixedErrorDiagonalDistinctPairCollisionExcess
      params candidate sourceError transformedError
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast Fintype.card_pos
  have hC : 0 < C := by
    dsimp [C]
    exact_mod_cast Fintype.card_pos
  calc
    (∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
      if K transformedError = 0 then 0
      else E transformedError /
        (D * C * (K transformedError : ℝ))) ≤
      ∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
        if K transformedError = 0 then 0 else collisionAverageBound / D := by
      apply Finset.sum_le_sum
      intro transformedError _
      by_cases hfiber : K transformedError = 0
      · simp [hfiber]
      · simp only [hfiber, if_false]
        have hK : (0 : ℝ) < K transformedError := by
          exact_mod_cast Nat.pos_of_ne_zero hfiber
        apply (div_le_iff₀ (mul_pos (mul_pos hD hC) hK)).2
        calc
          E transformedError ≤
              (K transformedError : ℝ) * C * collisionAverageBound := by
            exact hCollisionAverage transformedError
          _ = collisionAverageBound / D *
                (D * C * (K transformedError : ℝ)) := by
            field_simp [hD.ne']
    _ = (fixedErrorDifferenceNonemptyFiberCount
          params candidate sourceError : ℝ) *
        (collisionAverageBound / D) := by
      unfold fixedErrorDifferenceNonemptyFiberCount
      have hsum :
          (∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
            if K transformedError = 0 then 0 else collisionAverageBound / D) =
            ∑ transformedError ∈
                Finset.univ.filter (fun transformedError :
                  DiagonalErrorVector q degree ringRank params.levels =>
                    K transformedError ≠ 0),
              collisionAverageBound / D := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro transformedError _
        by_cases hfiber : K transformedError = 0 <;> simp [hfiber]
      rw [hsum]
      simp [K]

/-- Clean distinct-pair counterpart of the self-slice bound.  The same challenge/body
cardinality factorization turns a retained-fiber average collision factor `B` into `B /
|Challenge|`. -/
theorem fixedErrorDiagonalNormalizedDistinctPairCollisionExcess_le_fiberAverage_div_challengeCard
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (collisionAverageBound : ℝ) (hCollisionAverageBound : 0 ≤ collisionAverageBound)
    (hCollisionAverage : fixedErrorDifferenceFiberDistinctCollisionAverageBound
      params candidate sourceError collisionAverageBound) :
    fixedErrorDiagonalNormalizedDistinctPairCollisionExcess
        params candidate sourceError ≤
      collisionAverageBound /
        (Fintype.card (DiagonalChallenge q degree ringRank params.levels) : ℝ) := by
  let C : ℝ := Fintype.card (DiagonalChallenge q degree ringRank params.levels)
  let ErrorCard : ℝ := Fintype.card
    (DiagonalErrorVector q degree ringRank params.levels)
  let D : ℝ :=
    Fintype.card (RingGSWCiphertext q (degree + 1) ringRank params.levels)
  have hC : 0 < C := by
    dsimp [C]
    exact_mod_cast Fintype.card_pos
  have hErrorCard : 0 < ErrorCard := by
    dsimp [ErrorCard]
    exact_mod_cast Fintype.card_pos
  have hD : D = C * ErrorCard := by
    dsimp [D, C, ErrorCard]
    exact_mod_cast
      differenceCiphertextCard_eq_challengeCard_mul_errorCard
        (degree := degree) (ringRank := ringRank) params
  have hcount :
      (fixedErrorDifferenceNonemptyFiberCount
          params candidate sourceError : ℝ) ≤ ErrorCard := by
    dsimp [ErrorCard]
    exact_mod_cast fixedErrorDifferenceNonemptyFiberCount_le_card
      params candidate sourceError
  calc
    fixedErrorDiagonalNormalizedDistinctPairCollisionExcess
        params candidate sourceError ≤
      (fixedErrorDifferenceNonemptyFiberCount
          params candidate sourceError : ℝ) *
        (collisionAverageBound / D) :=
      fixedErrorDiagonalNormalizedDistinctPairCollisionExcess_le_nonemptyFiberCount_mul_of_fiberAverage
        params candidate sourceError collisionAverageBound hCollisionAverage
    _ ≤ ErrorCard * (collisionAverageBound / D) := by
      exact mul_le_mul_of_nonneg_right hcount
        (div_nonneg hCollisionAverageBound (le_of_lt (by
          rw [hD]
          positivity)))
    _ = collisionAverageBound / C := by
      rw [hD]
      field_simp [hC.ne', hErrorCard.ne']

/-- Square-root statistical form of the retained distinct-pair average-collision certificate. -/
theorem fixedErrorDiagonalDistinctChiSquareLoss_le_fiberAverage
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (collisionAverageBound : ℝ) (hCollisionAverageBound : 0 ≤ collisionAverageBound)
    (hCollisionAverage : fixedErrorDifferenceFiberDistinctCollisionAverageBound
      params candidate sourceError collisionAverageBound) :
    fixedErrorDiagonalDistinctChiSquareLoss params candidate sourceError ≤
      Real.sqrt
          (collisionAverageBound /
            (Fintype.card
              (DiagonalChallenge q degree ringRank params.levels) : ℝ)) /
        2 := by
  unfold fixedErrorDiagonalDistinctChiSquareLoss
  gcongr
  exact
    fixedErrorDiagonalNormalizedDistinctPairCollisionExcess_le_fiberAverage_div_challengeCard
      params candidate sourceError collisionAverageBound hCollisionAverageBound
        hCollisionAverage

/-- A support-wise retained distinct-pair certificate bounds its complete source-error average. -/
theorem averagedSourceErrorDiagonalDistinctChiSquareLoss_le_fiberAverage
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) (collisionAverageBound : ℝ)
    (hCollisionAverageBound : 0 ≤ collisionAverageBound)
    (hCollisionAverage : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      fixedErrorDifferenceFiberDistinctCollisionAverageBound
        params candidate sourceError collisionAverageBound) :
    averagedSourceErrorDiagonalDistinctChiSquareLoss (ringRank := ringRank)
        params sourceErrorSampler candidate ≤
      Real.sqrt
          (collisionAverageBound /
            (Fintype.card
              (DiagonalChallenge q degree ringRank params.levels) : ℝ)) /
        2 := by
  let ErrorVector := DiagonalErrorVector q degree ringRank params.levels
  let Errors : ProbComp ErrorVector :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  letI : Fintype ErrorVector := Fintype.ofFinite ErrorVector
  have hmass : (∑ sourceError : ErrorVector,
      Pr[= sourceError | Errors].toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun _ _ => probOutput_ne_top),
      sum_probOutput_eq_one (by simp), ENNReal.toReal_one]
  unfold averagedSourceErrorDiagonalDistinctChiSquareLoss
  rw [tsum_fintype]
  calc
    ∑ sourceError : ErrorVector,
        Pr[= sourceError | Errors].toReal *
          fixedErrorDiagonalDistinctChiSquareLoss params candidate sourceError ≤
      ∑ sourceError : ErrorVector,
        Pr[= sourceError | Errors].toReal *
          (Real.sqrt
              (collisionAverageBound /
                (Fintype.card
                  (DiagonalChallenge q degree ringRank params.levels) : ℝ)) /
            2) := by
      apply Finset.sum_le_sum
      intro sourceError _
      by_cases hsource : sourceError ∈ support Errors
      · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        apply fixedErrorDiagonalDistinctChiSquareLoss_le_fiberAverage
        · exact hCollisionAverageBound
        · exact hCollisionAverage sourceError (by
            simpa [Errors, ErrorVector] using hsource)
      · have hzero : Pr[= sourceError | Errors] = 0 :=
          probOutput_eq_zero_of_not_mem_support hsource
        simp [hzero]
    _ = (∑ sourceError : ErrorVector,
        Pr[= sourceError | Errors].toReal) *
          (Real.sqrt
              (collisionAverageBound /
                (Fintype.card
                  (DiagonalChallenge q degree ringRank params.levels) : ℝ)) /
            2) := by
      rw [Finset.sum_mul]
    _ = Real.sqrt
          (collisionAverageBound /
            (Fintype.card
              (DiagonalChallenge q degree ringRank params.levels) : ℝ)) /
        2 := by rw [hmass, one_mul]

/-- A zero source-error vector is retained as zero for every difference ciphertext. -/
@[simp]
theorem fixedErrorDifferenceSide_zero [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    fixedErrorDifferenceSide params candidate 0 difference = 0 := by
  unfold fixedErrorDifferenceSide
  exact (rowOperatorAddHom candidate
    (differenceEntryDigits params difference)).map_zero

/-- For zero source error there is one retained fiber, containing every difference ciphertext. -/
theorem fixedErrorDifferenceFiberCard_zero [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (transformedError : DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDifferenceFiberCard params candidate 0 transformedError =
      if transformedError = 0 then
        Fintype.card
          (RingGSWCiphertext q (degree + 1) ringRank params.levels)
      else 0 := by
  classical
  unfold fixedErrorDifferenceFiberCard FormalProof4FHE.ConditionalCollision.sideFiberCard
  by_cases hzero : transformedError = 0
  · subst transformedError
    simp
  · have hzero' : (0 : DiagonalErrorVector q degree ringRank params.levels) ≠
        transformedError := Ne.symm hzero
    simp [hzero, hzero']

/-- The zero source-error case reaches exactly one transformed-error value. -/
@[simp]
theorem fixedErrorDifferenceNonemptyFiberCount_zero [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool) :
    fixedErrorDifferenceNonemptyFiberCount
      (degree := degree) (ringRank := ringRank) params candidate 0 = 1 := by
  classical
  unfold fixedErrorDifferenceNonemptyFiberCount
  have hfilter :
      (Finset.univ.filter fun transformedError :
          DiagonalErrorVector q degree ringRank params.levels =>
        fixedErrorDifferenceFiberCard params candidate 0 transformedError ≠ 0) =
        {0} := by
    ext transformedError
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [fixedErrorDifferenceFiberCard_zero]
    by_cases hzero : transformedError = 0
    · simp [hzero]
    · simp [hzero]
  rw [hfilter]
  simp

/-- In the zero source-error case, the exact self slice is bounded by one pointwise kernel factor
divided by the complete difference-space cardinality.  This is the simplest concrete witness that
the equal-difference obstruction of the global relaxation disappears after retaining `K_t`. -/
theorem fixedErrorDiagonalNormalizedSelfPairCollisionExcess_zero_le
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (kernelBound : ℝ)
    (hKernel : ∀ difference :
        RingGSWCiphertext q (degree + 1) ringRank params.levels,
      differenceSelfKernelFactor params candidate difference ≤ kernelBound) :
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess
        (degree := degree) (ringRank := ringRank) params candidate 0 ≤
      kernelBound /
        (Fintype.card
          (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) := by
  simpa using
    (fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_nonemptyFiberCount_mul
      (degree := degree) (ringRank := ringRank) params candidate 0 kernelBound hKernel)

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
