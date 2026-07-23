/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessOneCycleShearInvariantCenteredBinomial

/-!
# Relative-Key and Complement Composition for One-Cycle TFHE

The complete binary master key decomposes into `N-1` relative bits and one anchor bit.  A uniform
relative mask followed by a uniform global-complement bit produces an exactly fresh master key.
The complement half is now available exactly for the shear-symmetrized BRK plus shared KSK.

This module formalizes the remaining composition boundary.  A `RelativeThenComplementEvaluator`
contains a possibly lossy nonlinear evaluator for normalized anchor-zero relative masks and a
second evaluator for the global complement.  Their errors add once.  The resulting object is the
generic `ViewRandomization` required by the auxiliary-input CircLWE search-to-decision framework,
with an exact uniform fresh-secret law.

Thus a future construction can focus solely on the relative shifted function.  This module does
not assume that such a nonlinear evaluator already exists.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization

noncomputable section

/-- A normalized relative-key evaluator followed by a global-complement evaluator. -/
structure RelativeThenComplementEvaluator (degree : ℕ) (View : Type) where
  sampleNarrowView : BinarySecret (degree + 1) → ProbComp View
  sampleWideView : BinarySecret (degree + 1) → ProbComp View
  evaluateRelative : BinarySecret degree → View → ProbComp View
  evaluateComplement : Bool → View → ProbComp View
  relativeError : ℝ
  complementError : ℝ
  relativeError_nonneg : 0 ≤ relativeError
  complementError_nonneg : 0 ≤ complementError
  relativeDistance_le : ∀ secret relativeMask,
    tvDist
        (sampleNarrowView secret >>= evaluateRelative relativeMask)
        (sampleWideView
          (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
            secret (relativeMaskLift relativeMask))) ≤ relativeError
  complementDistance_le : ∀ secret toggle,
    tvDist
        (sampleWideView secret >>= evaluateComplement toggle)
        (sampleWideView (globalComplementAction secret toggle)) ≤ complementError

namespace RelativeThenComplementEvaluator

variable {degree : ℕ} {View : Type}

/-- Package a relative evaluator with a deterministic complement transform whose distributional
law is exact.  The complement contributes zero to the resulting error budget. -/
noncomputable def ofExactComplement
    (sampleNarrowView sampleWideView :
      BinarySecret (degree + 1) → ProbComp View)
    (evaluateRelative : BinarySecret degree → View → ProbComp View)
    (relativeError : ℝ) (relativeError_nonneg : 0 ≤ relativeError)
    (relativeDistance_le : ∀ secret relativeMask,
      tvDist
          (sampleNarrowView secret >>= evaluateRelative relativeMask)
          (sampleWideView
            (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
              secret (relativeMaskLift relativeMask))) ≤ relativeError)
    (transformComplement : Bool → View → View)
    (complementLaw : ∀ secret toggle,
      evalDist (sampleWideView secret >>= fun view ↦
          pure (transformComplement toggle view)) =
        evalDist (sampleWideView (globalComplementAction secret toggle))) :
    RelativeThenComplementEvaluator degree View where
  sampleNarrowView := sampleNarrowView
  sampleWideView := sampleWideView
  evaluateRelative := evaluateRelative
  evaluateComplement := fun toggle view ↦ pure (transformComplement toggle view)
  relativeError := relativeError
  complementError := 0
  relativeError_nonneg := relativeError_nonneg
  complementError_nonneg := le_rfl
  relativeDistance_le := relativeDistance_le
  complementDistance_le := by
    intro secret toggle
    unfold tvDist
    rw [complementLaw secret toggle]
    exact le_of_eq (SPMF.tvDist_self _)

/-- Execute the nonlinear normalized-relative step before the exact affine anchor step. -/
def evaluateAndSmudge
    (evaluator : RelativeThenComplementEvaluator degree View)
    (mask : BinarySecret degree × Bool) (view : View) : ProbComp View :=
  evaluator.evaluateRelative mask.1 view >>=
    evaluator.evaluateComplement mask.2

/-- The two evaluator errors add once under sequential composition. -/
theorem viewDistance_le
    (evaluator : RelativeThenComplementEvaluator degree View)
    (secret : BinarySecret (degree + 1))
    (mask : BinarySecret degree × Bool) :
    tvDist
        (evaluator.sampleNarrowView secret >>=
          evaluator.evaluateAndSmudge mask)
        (evaluator.sampleWideView (relativeGlobalAction secret mask)) ≤
      evaluator.relativeError + evaluator.complementError := by
  let relativeSecret :=
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
      secret (relativeMaskLift mask.1)
  let afterRelative := evaluator.sampleNarrowView secret >>=
    evaluator.evaluateRelative mask.1
  let wideRelative := evaluator.sampleWideView relativeSecret
  let afterComplement := afterRelative >>= evaluator.evaluateComplement mask.2
  let wideAfterComplement := wideRelative >>= evaluator.evaluateComplement mask.2
  have hrelative : tvDist afterRelative wideRelative ≤ evaluator.relativeError := by
    exact evaluator.relativeDistance_le secret mask.1
  have hpost : tvDist afterComplement wideAfterComplement ≤
      tvDist afterRelative wideRelative := by
    exact tvDist_bind_right_le (evaluator.evaluateComplement mask.2)
      afterRelative wideRelative
  have hcomplement : tvDist wideAfterComplement
      (evaluator.sampleWideView (globalComplementAction relativeSecret mask.2)) ≤
      evaluator.complementError := by
    exact evaluator.complementDistance_le relativeSecret mask.2
  calc
    tvDist
        (evaluator.sampleNarrowView secret >>=
          evaluator.evaluateAndSmudge mask)
        (evaluator.sampleWideView (relativeGlobalAction secret mask)) =
      tvDist afterComplement
        (evaluator.sampleWideView (globalComplementAction relativeSecret mask.2)) := by
      unfold RelativeThenComplementEvaluator.evaluateAndSmudge
      simp [afterComplement, afterRelative,
        relativeGlobalAction, relativeSecret, bind_assoc]
    _ ≤ tvDist afterComplement wideAfterComplement +
        tvDist wideAfterComplement
          (evaluator.sampleWideView
            (globalComplementAction relativeSecret mask.2)) :=
      tvDist_triangle _ _ _
    _ ≤ evaluator.relativeError + evaluator.complementError :=
      add_le_add (hpost.trans hrelative) hcomplement

/-- A relative evaluator plus complement evaluator is a complete paper-aligned fresh-key view
randomizer. -/
noncomputable def toViewRandomization
    (evaluator : RelativeThenComplementEvaluator degree View) :
    LWE.AuxiliaryInput.SearchToDecision.ViewRandomization
      (BinarySecret (degree + 1)) (BinarySecret degree × Bool) View where
  sampleMask := $ᵗ (BinarySecret degree × Bool)
  act := relativeGlobalAction
  sampleFreshSecret := $ᵗ BinarySecret (degree + 1)
  sampleNarrowView := evaluator.sampleNarrowView
  sampleWideView := evaluator.sampleWideView
  evaluateAndSmudge := evaluator.evaluateAndSmudge
  error := evaluator.relativeError + evaluator.complementError
  error_nonneg := add_nonneg evaluator.relativeError_nonneg
    evaluator.complementError_nonneg
  secretLaw := relativeGlobalAction_uniform_evalDist
  viewDistance_le := evaluator.viewDistance_le

end RelativeThenComplementEvaluator

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization
