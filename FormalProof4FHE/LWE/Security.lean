/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.Basic
import VCVio.CryptoFoundations.Asymptotics.Security

/-!
# Security Interface for Decisional LWE

LWE hardness is an assumption about a class of efficient adversaries. This module proves that
VCVio's hidden-bit experiment has exactly the usual real-versus-uniform distinguishing advantage,
then packages that advantage for concrete and asymptotic security statements.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.LWE

section Concrete

variable {Sample Secret Output : Type} [Add Output]

/-- The hidden-bit LWE experiment and the two-branch distinguishing formulation have exactly the
same advantage. -/
theorem advantage_eq_boolDistAdvantage
    (problem : LearningWithErrors.Problem Sample Secret Output)
    (adversary : LearningWithErrors.Adversary problem) :
    LearningWithErrors.advantage problem adversary =
      (LearningWithErrors.game0 problem adversary).boolDistAdvantage
        (LearningWithErrors.game1 problem adversary) := by
  rw [LearningWithErrors.advantage]
  rw [show LearningWithErrors.experiment problem adversary =
      (do
        let bit ← ($ᵗ Bool)
        let guess ← if bit then LearningWithErrors.game0 problem adversary
          else LearningWithErrors.game1 problem adversary
        pure (bit == guess)) by
    simp only [LearningWithErrors.experiment, LearningWithErrors.game0,
      LearningWithErrors.game1, bind_assoc]]
  exact ProbComp.boolBiasAdvantage_eq_boolDistAdvantage_uniformBool_branch _ _

/-- Decisional LWE advantage is nonnegative. -/
theorem advantage_nonneg
    (problem : LearningWithErrors.Problem Sample Secret Output)
    (adversary : LearningWithErrors.Adversary problem) :
    0 ≤ LearningWithErrors.advantage problem adversary := by
  rw [advantage_eq_boolDistAdvantage]
  exact abs_nonneg _

/-- A Boolean distinguishing advantage is always at most one. -/
theorem advantage_le_one
    (problem : LearningWithErrors.Problem Sample Secret Output)
    (adversary : LearningWithErrors.Adversary problem) :
    LearningWithErrors.advantage problem adversary ≤ 1 := by
  rw [advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  have hreal :
      (Pr[= true | LearningWithErrors.game0 problem adversary]).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top probOutput_le_one
  have huniform :
      (Pr[= true | LearningWithErrors.game1 problem adversary]).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top probOutput_le_one
  have hreal_nonneg :
      0 ≤ (Pr[= true | LearningWithErrors.game0 problem adversary]).toReal :=
    ENNReal.toReal_nonneg
  have huniform_nonneg :
      0 ≤ (Pr[= true | LearningWithErrors.game1 problem adversary]).toReal :=
    ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- A concrete LWE problem is hard against the selected adversaries up to `bound`. -/
def HardAgainst (problem : LearningWithErrors.Problem Sample Secret Output)
    (allowed : LearningWithErrors.Adversary problem → Prop) (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary → LearningWithErrors.advantage problem adversary ≤ bound

end Concrete

section Asymptotic

variable {Sample Secret Output : Type} [Add Output]

/-- An asymptotic decisional-LWE game for a family of problems sharing the same public types.

Parameter-dependent dimensions and moduli can be represented later by choosing sigma types for
`Sample`, `Secret`, and `Output`; keeping this constructor nondependent makes it directly compatible
with VCVio's generic `SecurityGame` reduction lemmas. -/
noncomputable def securityGame
    (problems : ℕ → LearningWithErrors.Problem Sample Secret Output) :
    SecurityGame (Sample × Output → ProbComp Bool) where
  advantage adversary securityParameter := ENNReal.ofReal
    (LearningWithErrors.advantage (problems securityParameter) adversary)

end Asymptotic

end FormalProof4FHE.LWE
