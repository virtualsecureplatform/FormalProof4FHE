/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteProduct
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Binary Guess-and-Check from a Distinguishing Gap

This module isolates the probabilistic core of a binary search-to-decision step.  A public check
procedure receives a uniformly chosen candidate bit and returns a Boolean distinguisher answer.
The tester keeps the candidate when the answer has the selected orientation and flips it
otherwise.  Its exact success probability is one half plus one half of the signed acceptance gap
between checking the correct and incorrect candidates.

The source may correlate the hidden bit with an arbitrary public context.  No independence or
cryptographic assumption is used here.
-/

open OracleComp

namespace FormalProof4FHE.BinaryGuessCheck

/-- A fair choice between a positive Boolean experiment and the complement of a negative one. -/
def signedChoice (positive negative : ProbComp Bool) : ProbComp Bool := do
  let choosePositive ← $ᵗ Bool
  if choosePositive then positive else (! ·) <$> negative

/-- Independent source sampling commutes with `signedChoice`. -/
theorem evalDist_bind_signedChoice {Source : Type}
    (source : ProbComp Source) (positive negative : Source → ProbComp Bool) :
    evalDist (source >>= fun value => signedChoice (positive value) (negative value)) =
      evalDist (signedChoice (source >>= positive) (source >>= negative)) := by
  let choices : ProbComp Bool := $ᵗ Bool
  unfold signedChoice
  change evalDist (source >>= fun value =>
      choices >>= fun choosePositive =>
        if choosePositive then positive value else (! ·) <$> negative value) = _
  calc
    _ = evalDist (choices >>= fun choosePositive =>
        source >>= fun value =>
          if choosePositive then positive value else (! ·) <$> negative value) :=
      OracleComp.DeferredSampling.evalDist_bind_comm source choices _
    _ = _ := by
      apply evalDist_bind_congr' choices
      intro choosePositive
      cases choosePositive <;> simp

/-- Exact real-valued acceptance probability of `signedChoice`. -/
theorem probOutput_true_signedChoice (positive negative : ProbComp Bool) :
    (Pr[= true | signedChoice positive negative]).toReal =
      ((Pr[= true | positive]).toReal + 1 -
        (Pr[= true | negative]).toReal) / 2 := by
  have hformula : Pr[= true | signedChoice positive negative] =
      (Pr[= true | positive] + Pr[= false | negative]) / 2 := by
    simp [signedChoice, probOutput_bind_uniformBool]
  have hfalse : Pr[= false | negative] = 1 - Pr[= true | negative] := by
    simp [probOutput_false_eq_sub]
  rw [hformula, hfalse, ENNReal.toReal_div,
    ENNReal.toReal_add probOutput_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top),
    ENNReal.toReal_sub_of_le probOutput_le_one ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat]
  ring

/-- Public binary tester: sample a candidate, run its check, and keep or flip that candidate
according to the selected distinguisher orientation. -/
def tester {Context : Type} (orientation : Bool)
    (check : Bool → Context → ProbComp Bool) (context : Context) : ProbComp Bool := do
  let candidate ← $ᵗ Bool
  let answer ← check candidate context
  return if answer = orientation then candidate else !candidate

/-- Experiment checking whether `tester` recovers the hidden bit from its correlated context. -/
def game {Context : Type} (source : ProbComp (Bool × Context)) (orientation : Bool)
    (check : Bool → Context → ProbComp Bool) : ProbComp Bool := do
  let hiddenAndContext ← source
  let candidate ← tester orientation check hiddenAndContext.2
  return decide (candidate = hiddenAndContext.1)

/-- Run the public check on the actual hidden bit. -/
def correctCheck {Context : Type} (source : ProbComp (Bool × Context))
    (check : Bool → Context → ProbComp Bool) : ProbComp Bool := do
  let hiddenAndContext ← source
  check hiddenAndContext.1 hiddenAndContext.2

/-- Run the public check on the opposite of the hidden bit. -/
def wrongCheck {Context : Type} (source : ProbComp (Bool × Context))
    (check : Bool → Context → ProbComp Bool) : ProbComp Bool := do
  let hiddenAndContext ← source
  check (!hiddenAndContext.1) hiddenAndContext.2

private theorem evalDist_localGame_true {Context : Type} (hidden : Bool) (context : Context)
    (check : Bool → Context → ProbComp Bool) :
    evalDist (do
        let candidate ← tester true check context
        return decide (candidate = hidden)) =
      evalDist (signedChoice (check hidden context) (check (!hidden) context)) := by
  cases hidden <;>
    apply evalDist_ext <;>
    intro output <;>
    cases output <;>
    simp [tester, signedChoice, probOutput_bind_eq_tsum, map_eq_bind_pure_comp] <;>
    ac_rfl

private theorem evalDist_localGame_false {Context : Type} (hidden : Bool) (context : Context)
    (check : Bool → Context → ProbComp Bool) :
    evalDist (do
        let candidate ← tester false check context
        return decide (candidate = hidden)) =
      evalDist (signedChoice (check (!hidden) context) (check hidden context)) := by
  cases hidden <;>
    apply evalDist_ext <;>
    intro output <;>
    cases output <;>
    simp [tester, signedChoice, probOutput_bind_eq_tsum, map_eq_bind_pure_comp] <;>
    ac_rfl

/-- With positive orientation, the recovery game is the signed choice of the correct and wrong
check experiments. -/
theorem evalDist_game_true {Context : Type} (source : ProbComp (Bool × Context))
    (check : Bool → Context → ProbComp Bool) :
    evalDist (game source true check) =
      evalDist (signedChoice (correctCheck source check) (wrongCheck source check)) := by
  unfold game correctCheck wrongCheck
  rw [evalDist_bind]
  have hlocal : ∀ hiddenAndContext : Bool × Context,
      evalDist (do
          let candidate ← tester true check hiddenAndContext.2
          return decide (candidate = hiddenAndContext.1)) =
        evalDist (signedChoice
          (check hiddenAndContext.1 hiddenAndContext.2)
          (check (!hiddenAndContext.1) hiddenAndContext.2)) := by
    intro hiddenAndContext
    exact evalDist_localGame_true hiddenAndContext.1 hiddenAndContext.2 check
  simp_rw [hlocal]
  rw [← evalDist_bind]
  exact evalDist_bind_signedChoice source
    (fun hiddenAndContext => check hiddenAndContext.1 hiddenAndContext.2)
    (fun hiddenAndContext => check (!hiddenAndContext.1) hiddenAndContext.2)

/-- With negative orientation, the roles of the correct and wrong check experiments swap. -/
theorem evalDist_game_false {Context : Type} (source : ProbComp (Bool × Context))
    (check : Bool → Context → ProbComp Bool) :
    evalDist (game source false check) =
      evalDist (signedChoice (wrongCheck source check) (correctCheck source check)) := by
  unfold game correctCheck wrongCheck
  rw [evalDist_bind]
  have hlocal : ∀ hiddenAndContext : Bool × Context,
      evalDist (do
          let candidate ← tester false check hiddenAndContext.2
          return decide (candidate = hiddenAndContext.1)) =
        evalDist (signedChoice
          (check (!hiddenAndContext.1) hiddenAndContext.2)
          (check hiddenAndContext.1 hiddenAndContext.2)) := by
    intro hiddenAndContext
    exact evalDist_localGame_false hiddenAndContext.1 hiddenAndContext.2 check
  simp_rw [hlocal]
  rw [← evalDist_bind]
  exact evalDist_bind_signedChoice source
    (fun hiddenAndContext => check (!hiddenAndContext.1) hiddenAndContext.2)
    (fun hiddenAndContext => check hiddenAndContext.1 hiddenAndContext.2)

/-- Exact success formula for the positive orientation. -/
theorem successProbability_true {Context : Type} (source : ProbComp (Bool × Context))
    (check : Bool → Context → ProbComp Bool) :
    (Pr[= true | game source true check]).toReal =
      ((Pr[= true | correctCheck source check]).toReal + 1 -
        (Pr[= true | wrongCheck source check]).toReal) / 2 := by
  rw [probOutput_congr rfl (evalDist_game_true source check)]
  exact probOutput_true_signedChoice _ _

/-- Exact success formula for the negative orientation. -/
theorem successProbability_false {Context : Type} (source : ProbComp (Bool × Context))
    (check : Bool → Context → ProbComp Bool) :
    (Pr[= true | game source false check]).toReal =
      ((Pr[= true | wrongCheck source check]).toReal + 1 -
        (Pr[= true | correctCheck source check]).toReal) / 2 := by
  rw [probOutput_congr rfl (evalDist_game_false source check)]
  exact probOutput_true_signedChoice _ _

/-- Signed acceptance gap selected by `orientation`.  A positive gap means that the selected
orientation favors the correct-candidate check. -/
noncomputable def orientedGap {Context : Type} (source : ProbComp (Bool × Context))
    (orientation : Bool) (check : Bool → Context → ProbComp Bool) : ℝ :=
  if orientation then
    (Pr[= true | correctCheck source check]).toReal -
      (Pr[= true | wrongCheck source check]).toReal
  else
    (Pr[= true | wrongCheck source check]).toReal -
      (Pr[= true | correctCheck source check]).toReal

/-- Total-variation stability of an oriented acceptance gap.

If the positive and negative candidate experiments are respectively close to target experiments,
the target Boolean distinguishing advantage, minus both statistical errors, lower-bounds the
acceptance gap in the target's canonical orientation. -/
theorem orientedAcceptanceGap_lowerBound_of_tvDist
    (correct wrong real uniform : ProbComp Bool) (orientation : Bool)
    (correctError wrongError : ℝ)
    (horientation : if orientation then
      (Pr[= true | uniform]).toReal ≤ (Pr[= true | real]).toReal
    else
      (Pr[= true | real]).toReal ≤ (Pr[= true | uniform]).toReal)
    (hcorrect : tvDist correct real ≤ correctError)
    (hwrong : tvDist wrong uniform ≤ wrongError) :
    real.boolDistAdvantage uniform - correctError - wrongError ≤
      if orientation then
        (Pr[= true | correct]).toReal - (Pr[= true | wrong]).toReal
      else
        (Pr[= true | wrong]).toReal - (Pr[= true | correct]).toReal := by
  have hcorrectAbs :
      |(Pr[= true | correct]).toReal - (Pr[= true | real]).toReal| ≤ correctError :=
    (abs_probOutput_toReal_sub_le_tvDist correct real).trans hcorrect
  have hwrongAbs :
      |(Pr[= true | wrong]).toReal - (Pr[= true | uniform]).toReal| ≤ wrongError :=
    (abs_probOutput_toReal_sub_le_tvDist wrong uniform).trans hwrong
  have hcorrectBounds := abs_le.mp hcorrectAbs
  have hwrongBounds := abs_le.mp hwrongAbs
  unfold ProbComp.boolDistAdvantage
  cases orientation with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at horientation ⊢
      rw [abs_of_nonpos (sub_nonpos.mpr horientation)]
      linarith
  | true =>
      simp only [↓reduceIte] at horientation ⊢
      rw [abs_of_nonneg (sub_nonneg.mpr horientation)]
      linarith

/-- Uniform formula for either orientation: success is exactly `(1 + gap) / 2`. -/
theorem successProbability_eq_half_add_orientedGap {Context : Type}
    (source : ProbComp (Bool × Context)) (orientation : Bool)
    (check : Bool → Context → ProbComp Bool) :
    (Pr[= true | game source orientation check]).toReal =
      (1 + orientedGap source orientation check) / 2 := by
  cases orientation
  · rw [successProbability_false]
    simp only [orientedGap, Bool.false_eq_true, ↓reduceIte]
    ring
  · rw [successProbability_true]
    simp only [orientedGap, ↓reduceIte]
    ring

/-- Corresponding exact failure formula. -/
theorem failureProbability_eq_half_sub_orientedGap {Context : Type}
    (source : ProbComp (Bool × Context)) (orientation : Bool)
    (check : Bool → Context → ProbComp Bool) :
    (Pr[= false | game source orientation check]).toReal =
      (1 - orientedGap source orientation check) / 2 := by
  rw [probOutput_false_eq_sub]
  simp only [probFailure_eq_zero, tsub_zero]
  rw [
    ENNReal.toReal_sub_of_le probOutput_le_one ENNReal.one_ne_top,
    successProbability_eq_half_add_orientedGap]
  simp only [ENNReal.toReal_one]
  ring

/-- ENNReal form of the exact failure formula. -/
theorem failureProbability_eq_ofReal {Context : Type}
    (source : ProbComp (Bool × Context)) (orientation : Bool)
    (check : Bool → Context → ProbComp Bool) :
    Pr[= false | game source orientation check] =
      ENNReal.ofReal ((1 - orientedGap source orientation check) / 2) := by
  calc
    _ = ENNReal.ofReal (Pr[= false | game source orientation check]).toReal :=
      (ENNReal.ofReal_toReal probOutput_ne_top).symm
    _ = _ := congrArg ENNReal.ofReal
      (failureProbability_eq_half_sub_orientedGap source orientation check)

end FormalProof4FHE.BinaryGuessCheck
