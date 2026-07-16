/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE

open scoped ENNReal

example {Sample Secret Output : Type} [Add Output]
    (problem : LearningWithErrors.Problem Sample Secret Output)
    (adversary : LearningWithErrors.Adversary problem) :
    0 ≤ LearningWithErrors.advantage problem adversary := by
  exact FormalProof4FHE.LWE.advantage_nonneg problem adversary

example {Sample Secret Output : Type} [Add Output]
    (problem : LearningWithErrors.Problem Sample Secret Output)
    (adversary : LearningWithErrors.Adversary problem) :
    LearningWithErrors.advantage problem adversary ≤ 1 := by
  exact FormalProof4FHE.LWE.advantage_le_one problem adversary

example (blockLength blockCount : ℕ) :
    Fintype.card (FormalProof4FHE.BlockBinary.Key blockLength blockCount) =
      (blockLength + 1) ^ blockCount := by
  exact FormalProof4FHE.BlockBinary.card_key blockLength blockCount

example {R : Type} [Semiring R] [DecidableEq R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (smallErrorSampler largeErrorSampler : ProbComp R) :
    FormalProof4FHE.SharedRandomness.problem n k m
        prefixSampler suffixSampler smallErrorSampler largeErrorSampler =
      FormalProof4FHE.GeneralizedSubspaceLWE.problem m
        (FormalProof4FHE.GeneralizedSubspaceLWE.sharedSpec n k
          prefixSampler suffixSampler smallErrorSampler largeErrorSampler) := by
  exact FormalProof4FHE.GeneralizedSubspaceLWE.shared_problem_eq_generalized
    n k m prefixSampler suffixSampler smallErrorSampler largeErrorSampler

example {F : Type} [Field F] [Fintype F] [SampleableType F]
    (dimension slack : ℕ) :
    Pr[(fun matrix : Matrix (Fin (dimension + slack)) (Fin dimension) F ↦
      matrix.rank < dimension) |
      ($ᵗ Matrix (Fin (dimension + slack)) (Fin dimension) F)] ≤
      2 / (Fintype.card F : ℝ≥0∞) ^ (slack + 1) := by
  exact FormalProof4FHE.FiniteFieldRank.rankFailure_le dimension slack

example {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {ambient dimension : ℕ} (slack queryCount : ℕ)
    (errorSampler : ProbComp F)
    (adversary :
      FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.Adversary F ambient)
    (hbound : OracleComp.IsQueryBoundP adversary
      (FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.isSLWEQuery (F := F))
      queryCount) :
    FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.advantage
        (dimension + slack) errorSampler adversary ≤
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem dimension queryCount
          ($ᵗ (Fin dimension → F)) errorSampler)
        (FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.batchReduction
          (dimension := dimension) (dimension + slack) queryCount adversary) +
      2 * ((queryCount : ℝ≥0∞) *
        FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.pietrzakRankError F slack).toReal := by
  exact
    FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.advantage_le_batchLWE_add_rankLoss
      slack queryCount errorSampler adversary hbound
