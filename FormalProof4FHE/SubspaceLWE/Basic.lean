/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.SharedRandomness.Ordinary

/-!
# Generalized Two-Subspace LWE

This module isolates the common game behind LWE samples obtained from two possibly different
views of one master secret.  The row types may differ, the two error distributions may differ,
and each secret view is an arbitrary map out of the master-secret type.  Linear projections of a
module secret give the usual static subspace interpretation.

The final section proves that shared-randomness LWE is the nested-view instance in which the first
view selects the shared prefix and the second view selects the entire appended secret.
-/

open Matrix OracleComp

namespace FormalProof4FHE.GeneralizedSubspaceLWE

/-- Public matrices for two heterogeneous secret views. -/
abbrev Challenge (R LeftRows RightRows : Type) (m : ℕ) :=
  Matrix LeftRows (Fin m) R × Matrix RightRows (Fin m) R

/-- Noisy right-hand sides for the two secret views. -/
abbrev Output (R : Type) (m : ℕ) :=
  (Fin m → R) × (Fin m → R)

/-- A generalized two-subspace LWE specification.

`leftView` and `rightView` derive the secrets used in the two public matrix products from one
master secret.  They can be linear projections, affine views encoded into an augmented master
secret, or concrete restriction/extension maps. -/
structure Spec (R Master LeftRows RightRows : Type) where
  sampleMasterSecret : ProbComp Master
  leftView : Master → LeftRows → R
  rightView : Master → RightRows → R
  leftErrorSampler : ProbComp R
  rightErrorSampler : ProbComp R

/-- The generalized two-subspace decisional-LWE problem. -/
def problem {R Master LeftRows RightRows : Type}
    [Semiring R] [SampleableType R]
    [Fintype LeftRows] [Fintype RightRows]
    [FinEnum LeftRows] [FinEnum RightRows]
    (m : ℕ) (spec : Spec R Master LeftRows RightRows) :
    LearningWithErrors.Problem
      (Challenge R LeftRows RightRows m) Master (Output R m) where
  sampleChallenge := $ᵗ (Challenge R LeftRows RightRows m)
  sampleSecret := spec.sampleMasterSecret
  sampleError := do
    let leftError ← ProbComp.sampleIID m spec.leftErrorSampler
    let rightError ← ProbComp.sampleIID m spec.rightErrorSampler
    return (leftError, rightError)
  noiseless := fun master challenge ↦
    (vecMul (spec.leftView master) challenge.1,
      vecMul (spec.rightView master) challenge.2)
  sampleUniform := $ᵗ (Output R m)

/-- A generalized specification is nested along `embedding` when the left secret view is the
restriction of the right view to the embedded row indices. -/
def IsNested {R Master LeftRows RightRows : Type}
    (spec : Spec R Master LeftRows RightRows)
    (embedding : LeftRows → RightRows) : Prop :=
  Function.Injective embedding ∧
    ∀ master row, spec.leftView master row = spec.rightView master (embedding row)

section SharedRandomness

/-- Shared-randomness LWE as a generalized two-subspace specification. -/
def sharedSpec {R : Type} (n k : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (smallErrorSampler largeErrorSampler : ProbComp R) :
    Spec R (FormalProof4FHE.SharedRandomness.Secret R n k)
      (Fin n) (Fin (n + k)) where
  sampleMasterSecret := do
    let head ← prefixSampler
    let suffix ← suffixSampler
    return (head, suffix)
  leftView := fun master ↦ master.1
  rightView := fun master ↦ Fin.append master.1 master.2
  leftErrorSampler := smallErrorSampler
  rightErrorSampler := largeErrorSampler

/-- The shared prefix view is literally the restriction of the appended long-secret view. -/
theorem sharedSpec_isNested {R : Type} (n k : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (smallErrorSampler largeErrorSampler : ProbComp R) :
    IsNested
      (sharedSpec n k prefixSampler suffixSampler
        smallErrorSampler largeErrorSampler)
      (Fin.castAdd k) := by
  refine ⟨Fin.castAdd_injective n k, ?_⟩
  intro master row
  simp [sharedSpec]

/-- Shared-randomness LWE is definitionally the nested generalized two-subspace instance. -/
theorem shared_problem_eq_generalized {R : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (smallErrorSampler largeErrorSampler : ProbComp R) :
    FormalProof4FHE.SharedRandomness.problem n k m
        prefixSampler suffixSampler smallErrorSampler largeErrorSampler =
      problem m (sharedSpec n k prefixSampler suffixSampler
        smallErrorSampler largeErrorSampler) := by
  simp [FormalProof4FHE.SharedRandomness.problem, problem, sharedSpec, monad_norm]

/-- Consequently, every adversary has exactly the same advantage in the shared-randomness and
generalized-subspace presentations. -/
theorem shared_advantage_eq_generalized {R : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (smallErrorSampler largeErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (FormalProof4FHE.SharedRandomness.problem n k m
        prefixSampler suffixSampler smallErrorSampler largeErrorSampler)) :
    LearningWithErrors.advantage
        (FormalProof4FHE.SharedRandomness.problem n k m
          prefixSampler suffixSampler smallErrorSampler largeErrorSampler) adversary =
      LearningWithErrors.advantage
        (problem m (sharedSpec n k prefixSampler suffixSampler
          smallErrorSampler largeErrorSampler)) adversary := by
  rw [← shared_problem_eq_generalized n k m prefixSampler suffixSampler
    smallErrorSampler largeErrorSampler]

end SharedRandomness

end FormalProof4FHE.GeneralizedSubspaceLWE
