/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import LatticeCrypto.HardnessAssumptions.LearningWithErrors

/-!
# Decisional Learning With Errors

This module specializes VCVio's generic LWE experiment to a batch of matrix-form samples.
The matrix has one column per public LWE sample, so every column shares the same secret.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE

/-- A batch LWE problem with an explicit secret sampler.

For a challenge matrix `A : Matrix (Fin n) (Fin m) R` and secret `s : Fin n → R`, the
noiseless output is `s ᵀ A : Fin m → R`. The error sampler is repeated independently in
each of the `m` output coordinates. -/
def batchProblem {R : Type} [Semiring R] [DecidableEq R] [SampleableType R]
    (n m : ℕ) (secretSampler : ProbComp (Fin n → R)) (errorSampler : ProbComp R) :
    LearningWithErrors.Problem
      (Matrix (Fin n) (Fin m) R) (Fin n → R) (Fin m → R) where
  sampleChallenge := $ᵗ Matrix (Fin n) (Fin m) R
  sampleSecret := secretSampler
  sampleError := ProbComp.sampleIID m errorSampler
  noiseless := fun secret challenge ↦ vecMul secret challenge
  sampleUniform := $ᵗ (Fin m → R)

/-- Ordinary batch LWE over `ZMod q` with a uniform secret. -/
def zmodBatchProblem (n m q : ℕ) [NeZero q] (errorSampler : ProbComp (ZMod q)) :
    LearningWithErrors.Problem
      (Matrix (Fin n) (Fin m) (ZMod q)) (Fin n → ZMod q) (Fin m → ZMod q) :=
  batchProblem n m ($ᵗ (Fin n → ZMod q)) errorSampler

end FormalProof4FHE.LWE
