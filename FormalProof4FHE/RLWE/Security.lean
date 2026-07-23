/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.Security
import FormalProof4FHE.RLWE.Basic

/-!
# Security Interface for Decisional RLWE

This module specializes FormalProof4FHE's checked decisional-LWE security interface to
the negacyclic ring from `FormalProof4FHE.RLWE.Basic`. It establishes that the hidden-bit
experiment has exactly the usual real-versus-uniform distinguishing advantage and exposes the
concrete hardness predicate for the finite quotient-ring game.

These results define and normalize the average-case RLWE assumption. They do not claim a
worst-case ideal-lattice reduction; formalizing that substantially larger theorem requires
the number-field, ideal-lattice, Gaussian, and quantum-reduction development described in
`docs/RLWE.md`.
-/

open OracleComp

namespace FormalProof4FHE.RLWE

variable {q degree sampleCount : ℕ} [NeZero q]

/-- The hidden-bit RLWE advantage equals the absolute real-versus-uniform output gap. -/
theorem advantage_eq_boolDistAdvantage
    (secretSampler : ProbComp (Secret q degree))
    (errorSampler : ProbComp (Rq q degree))
    (adversary : LearningWithErrors.Adversary
      (problem q degree sampleCount secretSampler errorSampler)) :
    LearningWithErrors.advantage
        (problem q degree sampleCount secretSampler errorSampler) adversary =
      (LearningWithErrors.game0
          (problem q degree sampleCount secretSampler errorSampler) adversary).boolDistAdvantage
        (LearningWithErrors.game1
          (problem q degree sampleCount secretSampler errorSampler) adversary) :=
  LWE.advantage_eq_boolDistAdvantage _ _

/-- Decisional RLWE advantage is nonnegative. -/
theorem advantage_nonneg
    (secretSampler : ProbComp (Secret q degree))
    (errorSampler : ProbComp (Rq q degree))
    (adversary : LearningWithErrors.Adversary
      (problem q degree sampleCount secretSampler errorSampler)) :
    0 ≤ LearningWithErrors.advantage
      (problem q degree sampleCount secretSampler errorSampler) adversary :=
  LWE.advantage_nonneg _ _

/-- Decisional RLWE advantage is at most one. -/
theorem advantage_le_one
    (secretSampler : ProbComp (Secret q degree))
    (errorSampler : ProbComp (Rq q degree))
    (adversary : LearningWithErrors.Adversary
      (problem q degree sampleCount secretSampler errorSampler)) :
    LearningWithErrors.advantage
      (problem q degree sampleCount secretSampler errorSampler) adversary ≤ 1 :=
  LWE.advantage_le_one _ _

/-- Uniform-secret finite decisional RLWE advantage is nonnegative. -/
theorem uniformAdvantage_nonneg
    (errorSampler : ProbComp (Rq q degree))
    (adversary : LearningWithErrors.Adversary
      (uniformSecretProblem q degree sampleCount errorSampler)) :
    0 ≤ LearningWithErrors.advantage
      (uniformSecretProblem q degree sampleCount errorSampler) adversary :=
  LWE.advantage_nonneg _ _

/-- Uniform-secret finite decisional RLWE advantage is at most one. -/
theorem uniformAdvantage_le_one
    (errorSampler : ProbComp (Rq q degree))
    (adversary : LearningWithErrors.Adversary
      (uniformSecretProblem q degree sampleCount errorSampler)) :
    LearningWithErrors.advantage
      (uniformSecretProblem q degree sampleCount errorSampler) adversary ≤ 1 :=
  LWE.advantage_le_one _ _

/-- A concrete RLWE problem is hard against the selected adversaries up to `bound`. -/
abbrev HardAgainst
    (secretSampler : ProbComp (Secret q degree))
    (errorSampler : ProbComp (Rq q degree))
    (allowed : LearningWithErrors.Adversary
      (problem q degree sampleCount secretSampler errorSampler) → Prop)
    (bound : ℝ) : Prop :=
  LWE.HardAgainst (problem q degree sampleCount secretSampler errorSampler) allowed bound

/-- Uniform-secret finite RLWE is hard against the selected adversaries up to `bound`. -/
abbrev UniformHardAgainst
    (errorSampler : ProbComp (Rq q degree))
    (allowed : LearningWithErrors.Adversary
      (uniformSecretProblem q degree sampleCount errorSampler) → Prop)
    (bound : ℝ) : Prop :=
  LWE.HardAgainst (uniformSecretProblem q degree sampleCount errorSampler) allowed bound

/-- The advantage against uniform-secret RLWE is exactly the advantage against rank-one
module-LWE; the specialization has no reduction loss. -/
theorem uniformAdvantage_eq_moduleRankOne
    (errorSampler : ProbComp (Rq q degree))
    (adversary : LearningWithErrors.Adversary
      (uniformSecretProblem q degree sampleCount errorSampler)) :
    LearningWithErrors.advantage
        (uniformSecretProblem q degree sampleCount errorSampler) adversary =
      LearningWithErrors.advantage
        (moduleProblem q degree 1 sampleCount errorSampler) adversary := by
  rw [uniformSecretProblem_eq_moduleProblem_one]

/-- Any rank-one module-LWE bound transfers to uniform-secret finite RLWE with the same
adversary and no loss in the bound. -/
theorem uniformHardAgainst_of_moduleRankOne
    (errorSampler : ProbComp (Rq q degree))
    (allowed : LearningWithErrors.Adversary
      (uniformSecretProblem q degree sampleCount errorSampler) → Prop)
    (bound : ℝ)
    (h : LWE.HardAgainst (moduleProblem q degree 1 sampleCount errorSampler)
      allowed bound) :
    UniformHardAgainst errorSampler allowed bound := by
  intro adversary hadversary
  rw [uniformSecretProblem_eq_moduleProblem_one]
  exact h adversary hadversary

end FormalProof4FHE.RLWE
