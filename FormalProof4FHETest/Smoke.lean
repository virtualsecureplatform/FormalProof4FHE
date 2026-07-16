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
