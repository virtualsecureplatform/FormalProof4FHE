/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveRelativeCandidateView
import FormalProof4FHE.SharedRandomness.Reduction

set_option autoImplicit false

/-!
# One-Coordinate Guess-and-Check for Direct Adaptive TFHE CircLWE

The exact candidate-tape algebra and the relative/anchor fresh-secret compiler are postcomposed
with an arbitrary public direct-CircLWE distinguisher.  For each extracted target-key coordinate,
the correct candidate is checked against the fresh real branch and the opposite candidate against
the fresh uniform-tape branch.  Data processing and the generic binary guess-and-check theorem
give an executable one-shot predictor with success at least

`(1 + directCircLWEAdvantage - 2 * evaluatorBudget) / 2`.

This closes the probabilistic guess-and-check layer.  It remains conditional on the explicit
`RelativeKeyShiftMaterialEvaluator` endpoint compiled into `RelativeEvaluationMaterialEvaluator`;
it does not construct the nonlinear native ring-key shift.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE

noncomputable section

open FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision

/-- Public distinguishers for the rank-one direct adaptive TFHE CircLWE view. -/
abbrev DirectDistinguisher
    (q degree suffixRank levels queryCount : ℕ) :=
  PublicDistinguisher
    (Challenge q (degree + 1) 1 suffixRank queryCount)
    (Auxiliary q (degree + 1) 1 suffixRank levels)

/-- Run a public distinguisher on the averaged fresh real view. -/
def freshRealDecisionGame
    (q degree suffixRank levels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) :
    ProbComp Bool := do
  let view ← sampleFreshRealPublicView q degree suffixRank levels queryCount
    bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
  distinguisher view.1 view.2

/-- Run the same public distinguisher on the averaged fresh uniform-tape view. -/
def freshUniformDecisionGame
    (q degree suffixRank levels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) :
    ProbComp Bool := do
  let view ← sampleFreshUniformTapePublicView q degree suffixRank levels queryCount
    bootstrapErrorSampler extensionErrorSampler gadget
  distinguisher view.1 view.2

/-- The direct real-versus-uniform-tape Boolean advantage in fresh-public-view form. -/
noncomputable def freshDecisionAdvantage
    (q degree suffixRank levels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) : ℝ :=
  ProbComp.boolDistAdvantage
    (freshRealDecisionGame q degree suffixRank levels queryCount
      bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget distinguisher)
    (freshUniformDecisionGame q degree suffixRank levels queryCount
      bootstrapErrorSampler extensionErrorSampler gadget distinguisher)

/-- The fresh-public-view presentation is the existing direct public CircLWE advantage. -/
theorem freshDecisionAdvantage_eq_publicAdvantage
    (q degree suffixRank levels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) :
    freshDecisionAdvantage q degree suffixRank levels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget distinguisher =
      publicAdvantage
        (problem q (degree + 1) 1 suffixRank levels queryCount
          bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget)
        distinguisher := by
  unfold freshDecisionAdvantage publicAdvantage
    FormalProof4FHE.LWE.AuxiliaryInput.circularLweAdvantage
  congr 1 <;>
    simp [freshRealDecisionGame, freshUniformDecisionGame,
      sampleFreshRealPublicView, sampleFreshUniformTapePublicView,
      sampleUniformTapeMaterialView, sampleRealView, sampleEvaluationMaterial,
      problem, FormalProof4FHE.TFHE.SamplerReplacement.independentPair,
      FormalProof4FHE.LWE.AuxiliaryInput.realGame,
      FormalProof4FHE.LWE.AuxiliaryInput.uniformGame, publicContinuation,
      map_eq_bind_pure_comp, bind_assoc, monad_norm]

namespace RelativeEvaluationMaterialEvaluator

/-- The common real/uniform candidate-view error paid by the compiled relative evaluator. -/
noncomputable def candidateErrorBudget
    {q degree suffixRank levels : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget) : ℝ :=
  evaluator.error + globalComplementViewError
    (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler

theorem candidateErrorBudget_nonneg
    {q degree suffixRank levels : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget) :
    0 ≤ evaluator.candidateErrorBudget := by
  exact add_nonneg evaluator.error_nonneg
    (globalComplementViewError_nonneg wideBootstrapErrorSampler)

/-- Candidate transformation followed by a public direct-CircLWE distinguisher. -/
def candidateCheck
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1)))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (candidate : Bool)
    (view : View q (degree + 1) 1 suffixRank levels queryCount) : ProbComp Bool := do
  let transformed ← evaluator.evaluateCandidateView coordinate candidate view
  distinguisher transformed.1 transformed.2

/-- Average the correct-candidate pointwise law over the original hidden nested key. -/
theorem correctCandidateView_tvDist_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    tvDist
        (do
          let hiddenAndView ← targetCoordinateSource q degree suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
            gadget coordinate
          evaluator.evaluateCandidateView coordinate hiddenAndView.1 hiddenAndView.2)
        (sampleFreshRealPublicView q degree suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget) ≤
      evaluator.candidateErrorBudget := by
  let secrets := sampleNestedSecret 1 suffixRank (degree + 1)
  let target := sampleFreshRealPublicView q degree suffixRank levels queryCount
    wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
  let sourceView := fun secret : Secret 1 suffixRank (degree + 1) ↦
    sampleRealView q (degree + 1) 1 suffixRank levels queryCount
        narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
        gadget secret >>=
      evaluator.evaluateCandidateView coordinate
        (targetMessages secret.1 secret.2 coordinate)
  have hmix := tvDist_bind_left_le_const' (m := ProbComp) secrets sourceView
    (fun _ ↦ target) evaluator.candidateErrorBudget
    (fun secret ↦ by
      simpa only [sourceView, target, candidateErrorBudget] using
        (evaluator.evaluateCandidateView_correct_tvDist_le inputErrorSampler
          hextensionSymmetric secret coordinate))
  have htarget : evalDist (secrets >>= fun _ ↦ target) = evalDist target :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      secrets (by simp [secrets, sampleNestedSecret]) target
  unfold tvDist at hmix ⊢
  rw [htarget] at hmix
  simpa [targetCoordinateSource, secrets, sourceView, target, bind_assoc, monad_norm]
    using hmix

/-- Average the wrong-candidate pointwise law over the original hidden nested key. -/
theorem wrongCandidateView_tvDist_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    tvDist
        (do
          let hiddenAndView ← targetCoordinateSource q degree suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
            gadget coordinate
          evaluator.evaluateCandidateView coordinate (!hiddenAndView.1) hiddenAndView.2)
        (sampleFreshUniformTapePublicView q degree suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler gadget) ≤
      evaluator.candidateErrorBudget := by
  let secrets := sampleNestedSecret 1 suffixRank (degree + 1)
  let target := sampleFreshUniformTapePublicView q degree suffixRank levels queryCount
    wideBootstrapErrorSampler wideExtensionErrorSampler gadget
  let sourceView := fun secret : Secret 1 suffixRank (degree + 1) ↦
    sampleRealView q (degree + 1) 1 suffixRank levels queryCount
        narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
        gadget secret >>=
      evaluator.evaluateCandidateView coordinate
        (!(targetMessages secret.1 secret.2 coordinate))
  have hmix := tvDist_bind_left_le_const' (m := ProbComp) secrets sourceView
    (fun _ ↦ target) evaluator.candidateErrorBudget
    (fun secret ↦ by
      simpa only [sourceView, target, candidateErrorBudget] using
        (evaluator.evaluateCandidateView_wrong_tvDist_le inputErrorSampler hInputError
          hextensionSymmetric secret coordinate
          (!(targetMessages secret.1 secret.2 coordinate)) (by simp)))
  have htarget : evalDist (secrets >>= fun _ ↦ target) = evalDist target :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      secrets (by simp [secrets, sampleNestedSecret]) target
  unfold tvDist at hmix ⊢
  rw [htarget] at hmix
  simpa [targetCoordinateSource, secrets, sourceView, target, bind_assoc, monad_norm]
    using hmix

/-- Canonical acceptance orientation of a direct public CircLWE distinguisher. -/
noncomputable def candidateOrientation
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) : Bool :=
  if (Pr[= true | freshUniformDecisionGame q degree suffixRank levels queryCount
      bootstrapErrorSampler extensionErrorSampler gadget distinguisher]).toReal ≤
      (Pr[= true | freshRealDecisionGame q degree suffixRank levels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
        distinguisher]).toReal then true else false

theorem candidateOrientation_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) :
    if candidateOrientation bootstrapErrorSampler extensionErrorSampler
        inputErrorSampler gadget distinguisher then
      (Pr[= true | freshUniformDecisionGame q degree suffixRank levels queryCount
        bootstrapErrorSampler extensionErrorSampler gadget distinguisher]).toReal ≤
      (Pr[= true | freshRealDecisionGame q degree suffixRank levels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
        distinguisher]).toReal
    else
      (Pr[= true | freshRealDecisionGame q degree suffixRank levels queryCount
        bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget
        distinguisher]).toReal ≤
      (Pr[= true | freshUniformDecisionGame q degree suffixRank levels queryCount
        bootstrapErrorSampler extensionErrorSampler gadget distinguisher]).toReal := by
  unfold candidateOrientation
  split
  · assumption
  · exact le_of_not_ge ‹_›

/-- The one-shot public coordinate-recovery experiment induced by guess-and-check. -/
def coordinateRecoveryGame
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) : ProbComp Bool :=
  FormalProof4FHE.BinaryGuessCheck.game
    (targetCoordinateSource q degree suffixRank levels queryCount
      narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget
      coordinate)
    (candidateOrientation wideBootstrapErrorSampler wideExtensionErrorSampler
      inputErrorSampler gadget distinguisher)
    (evaluator.candidateCheck coordinate distinguisher)

/-- The direct CircLWE advantage, minus the two candidate-view errors, lower-bounds the oriented
candidate-check gap. -/
theorem freshDecisionAdvantage_sub_errors_le_orientedGap
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    freshDecisionAdvantage q degree suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler
          gadget distinguisher -
        evaluator.candidateErrorBudget - evaluator.candidateErrorBudget ≤
      FormalProof4FHE.BinaryGuessCheck.orientedGap
        (targetCoordinateSource q degree suffixRank levels queryCount
          narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
          gadget coordinate)
        (candidateOrientation wideBootstrapErrorSampler wideExtensionErrorSampler
          inputErrorSampler gadget distinguisher)
        (evaluator.candidateCheck coordinate distinguisher) := by
  let source := targetCoordinateSource q degree suffixRank levels queryCount
    narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget
    coordinate
  let check := evaluator.candidateCheck coordinate distinguisher
  let finish := fun view : View q (degree + 1) 1 suffixRank levels queryCount ↦
    distinguisher view.1 view.2
  let correct := FormalProof4FHE.BinaryGuessCheck.correctCheck source check
  let wrong := FormalProof4FHE.BinaryGuessCheck.wrongCheck source check
  let real := freshRealDecisionGame q degree suffixRank levels queryCount
    wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
    distinguisher
  let uniform := freshUniformDecisionGame q degree suffixRank levels queryCount
    wideBootstrapErrorSampler wideExtensionErrorSampler gadget distinguisher
  have hcorrect : tvDist correct real ≤ evaluator.candidateErrorBudget := by
    have hdata := tvDist_bind_right_le finish
      (do
        let hiddenAndView ← source
        evaluator.evaluateCandidateView coordinate hiddenAndView.1 hiddenAndView.2)
      (sampleFreshRealPublicView q degree suffixRank levels queryCount
        wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget)
    have hpost : tvDist correct real ≤
        tvDist
          (do
            let hiddenAndView ← source
            evaluator.evaluateCandidateView coordinate hiddenAndView.1 hiddenAndView.2)
          (sampleFreshRealPublicView q degree suffixRank levels queryCount
            wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget) := by
      simpa [correct, real, source, check, finish,
        FormalProof4FHE.BinaryGuessCheck.correctCheck, candidateCheck,
        freshRealDecisionGame, bind_assoc]
        using hdata
    exact hpost.trans (evaluator.correctCandidateView_tvDist_le inputErrorSampler
      hextensionSymmetric coordinate)
  have hwrong : tvDist wrong uniform ≤ evaluator.candidateErrorBudget := by
    have hdata := tvDist_bind_right_le finish
      (do
        let hiddenAndView ← source
        evaluator.evaluateCandidateView coordinate (!hiddenAndView.1) hiddenAndView.2)
      (sampleFreshUniformTapePublicView q degree suffixRank levels queryCount
        wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    have hpost : tvDist wrong uniform ≤
        tvDist
          (do
            let hiddenAndView ← source
            evaluator.evaluateCandidateView coordinate (!hiddenAndView.1) hiddenAndView.2)
          (sampleFreshUniformTapePublicView q degree suffixRank levels queryCount
            wideBootstrapErrorSampler wideExtensionErrorSampler gadget) := by
      simpa [wrong, uniform, source, check, finish,
        FormalProof4FHE.BinaryGuessCheck.wrongCheck, candidateCheck,
        freshUniformDecisionGame, bind_assoc]
        using hdata
    exact hpost.trans (evaluator.wrongCandidateView_tvDist_le inputErrorSampler
      hInputError hextensionSymmetric coordinate)
  have hgap := FormalProof4FHE.BinaryGuessCheck.orientedAcceptanceGap_lowerBound_of_tvDist
    correct wrong real uniform
    (candidateOrientation wideBootstrapErrorSampler wideExtensionErrorSampler
      inputErrorSampler gadget distinguisher)
    evaluator.candidateErrorBudget evaluator.candidateErrorBudget
    (candidateOrientation_le wideBootstrapErrorSampler wideExtensionErrorSampler
      inputErrorSampler gadget distinguisher)
    hcorrect hwrong
  simpa [freshDecisionAdvantage, source, check, correct, wrong, real, uniform,
    FormalProof4FHE.BinaryGuessCheck.orientedGap] using hgap

/-- The equivalent one-shot coordinate failure bound. -/
theorem coordinateRecoveryGame_failureProbability_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    Pr[= false |
        evaluator.coordinateRecoveryGame inputErrorSampler distinguisher coordinate] ≤
      ENNReal.ofReal
        ((1 - (freshDecisionAdvantage q degree suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
          distinguisher - 2 * evaluator.candidateErrorBudget)) / 2) := by
  unfold coordinateRecoveryGame
  rw [FormalProof4FHE.BinaryGuessCheck.failureProbability_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  have hgap := evaluator.freshDecisionAdvantage_sub_errors_le_orientedGap
    inputErrorSampler hInputError hextensionSymmetric distinguisher coordinate
  linarith

/-- The failure bound in the project's direct public CircLWE notation. -/
theorem coordinateRecoveryGame_failureProbability_publicAdvantage_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    Pr[= false |
        evaluator.coordinateRecoveryGame inputErrorSampler distinguisher coordinate] ≤
      ENNReal.ofReal
        ((1 - (publicAdvantage
          (problem q (degree + 1) 1 suffixRank levels queryCount
            wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget)
          distinguisher - 2 * evaluator.candidateErrorBudget)) / 2) := by
  rw [← freshDecisionAdvantage_eq_publicAdvantage q degree suffixRank levels queryCount
    wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
    distinguisher]
  exact evaluator.coordinateRecoveryGame_failureProbability_le inputErrorSampler
    hInputError hextensionSymmetric distinguisher coordinate

/-- Executable one-coordinate recovery succeeds with the canonical PKC one-shot bound. -/
theorem coordinateRecoveryGame_successProbability_lowerBound
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    (1 + freshDecisionAdvantage q degree suffixRank levels queryCount
        wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
        distinguisher - 2 * evaluator.candidateErrorBudget) / 2 ≤
      (Pr[= true |
        evaluator.coordinateRecoveryGame inputErrorSampler distinguisher coordinate]).toReal := by
  rw [coordinateRecoveryGame,
    FormalProof4FHE.BinaryGuessCheck.successProbability_eq_half_add_orientedGap]
  have hgap := evaluator.freshDecisionAdvantage_sub_errors_le_orientedGap
    inputErrorSampler hInputError hextensionSymmetric distinguisher coordinate
  linarith

/-- The same one-shot bound stated with the project's direct public CircLWE problem. -/
theorem coordinateRecoveryGame_successProbability_publicAdvantage_lowerBound
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    (1 + publicAdvantage
        (problem q (degree + 1) 1 suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget)
        distinguisher - 2 * evaluator.candidateErrorBudget) / 2 ≤
      (Pr[= true |
        evaluator.coordinateRecoveryGame inputErrorSampler distinguisher coordinate]).toReal := by
  rw [← freshDecisionAdvantage_eq_publicAdvantage q degree suffixRank levels queryCount
    wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
    distinguisher]
  exact evaluator.coordinateRecoveryGame_successProbability_lowerBound
    inputErrorSampler hInputError hextensionSymmetric distinguisher coordinate

end RelativeEvaluationMaterialEvaluator

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE
