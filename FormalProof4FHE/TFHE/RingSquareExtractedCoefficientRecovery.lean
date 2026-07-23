/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.BinaryGuessCheck
import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.TFHE.RingSquareExtractedGuessCheck

/-!
# Coefficient Recovery from an Extracted `RGSW_S(-S)` Decision Gap

This module averages the exact fixed-secret sample-extracted candidate laws over a uniform
binary rank-one ring secret.  Any distinguisher between

* a genuine `RGSW_S(-S)` together with extracted scalar-LWE rows under the coefficients of `S`;
  and
* the same genuine circular auxiliary together with a uniform scalar transcript

therefore gives an exact binary guess/check procedure for every coefficient of `S`.  With the
canonical orientation, one coordinate is recovered with probability
`(1 + decisionAdvantage) / 2`.

The circular auxiliary remains in both endpoints.  Consequently this is a search-to-decision
theorem for the extracted circular problem, not a reduction of `RGSW_S(-S)` security to ordinary
RLWE.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.ExtractedGuessCheck.CoefficientRecovery

open FormalProof4FHE.TFHE

noncomputable section

/-- Public algorithm distinguishing the real extracted tests from uniform tests while retaining
the genuine circular RGSW auxiliary. -/
abbrev Distinguisher (q degree levels samples : ℕ) :=
  ExtractedCircularView q degree levels samples → ProbComp Bool

/-- Real public view, averaged over a uniformly sampled binary rank-one ring secret. -/
def realPublicView
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree) :
    ProbComp (ExtractedCircularView q degree levels samples) := do
  let secret ← Native.sampleRingSecret 1 (degree + 1)
  fixedSecretRealViewSampler q degree levels samples auxiliaryErrorSampler
    testRingErrorSampler secret gadget

/-- Uniform-test endpoint, averaged over the same binary ring-secret law and retaining the
genuine `RGSW_S(-S)` auxiliary. -/
def uniformPublicView
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree) :
    ProbComp (ExtractedCircularView q degree levels samples) := do
  let secret ← Native.sampleRingSecret 1 (degree + 1)
  fixedSecretUniformViewSampler q degree levels samples auxiliaryErrorSampler secret gadget

/-- Real decision experiment. -/
def realDecisionGame
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples) : ProbComp Bool := do
  let view ← realPublicView q degree levels samples auxiliaryErrorSampler
    testRingErrorSampler gadget
  distinguisher view

/-- Uniform-test decision experiment. -/
def uniformDecisionGame
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples) : ProbComp Bool := do
  let view ← uniformPublicView q degree levels samples auxiliaryErrorSampler gadget
  distinguisher view

/-- Absolute real-versus-uniform-test decision advantage. -/
def decisionAdvantage
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples) : ℝ :=
  (realDecisionGame q degree levels samples auxiliaryErrorSampler testRingErrorSampler
    gadget distinguisher).boolDistAdvantage
  (uniformDecisionGame q degree levels samples auxiliaryErrorSampler gadget distinguisher)

/-- The hidden coefficient paired with its complete genuine-RGSW/real-test public context. -/
def coordinateSource
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (coordinate : Fin (scalarDimension degree)) :
    ProbComp (Bool × ExtractedCircularView q degree levels samples) := do
  let secret ← Native.sampleRingSecret 1 (degree + 1)
  let view ← fixedSecretRealViewSampler q degree levels samples auxiliaryErrorSampler
    testRingErrorSampler secret gadget
  return (keyExtract secret coordinate, view)

/-- Candidate transformation followed by a supplied public distinguisher. -/
def candidateCheck
    {q degree levels samples : ℕ} [NeZero q]
    (distinguisher : Distinguisher q degree levels samples)
    (coordinate : Fin (scalarDimension degree)) (candidate : Bool)
    (view : ExtractedCircularView q degree levels samples) : ProbComp Bool := do
  let transformed ← randomizeView coordinate candidate view
  distinguisher transformed

/-- Averaging the true-candidate transform over the uniform ring-secret law reproduces the real
public view exactly. -/
theorem correctCandidateView_evalDist
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (coordinate : Fin (scalarDimension degree)) :
    evalDist (do
      let hiddenAndView ← coordinateSource q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget coordinate
      randomizeView coordinate hiddenAndView.1 hiddenAndView.2) =
      evalDist (realPublicView q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget) := by
  unfold coordinateSource realPublicView
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' (Native.sampleRingSecret 1 (degree + 1)) fun secret ↦ ?_
  simpa only [fixedSecretCandidateViewSampler] using
    (fixedSecretCandidateViewSampler_correct_evalDist q degree levels samples
      auxiliaryErrorSampler testRingErrorSampler secret gadget coordinate)

/-- Averaging the opposite-candidate transform produces the uniform-test public endpoint
exactly. -/
theorem wrongCandidateView_evalDist
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (htestError : Pr[⊥ | testRingErrorSampler] = 0)
    (gadget : Fin levels → Ring q degree)
    (coordinate : Fin (scalarDimension degree)) :
    evalDist (do
      let hiddenAndView ← coordinateSource q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget coordinate
      randomizeView coordinate (!hiddenAndView.1) hiddenAndView.2) =
      evalDist (uniformPublicView q degree levels samples auxiliaryErrorSampler gadget) := by
  unfold coordinateSource uniformPublicView
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' (Native.sampleRingSecret 1 (degree + 1)) fun secret ↦ ?_
  simpa only [fixedSecretCandidateViewSampler] using
    (fixedSecretCandidateViewSampler_wrong_evalDist q degree levels samples
      auxiliaryErrorSampler testRingErrorSampler htestError secret gadget coordinate)

/-- Correct candidate checks reproduce the real decision experiment. -/
theorem correctCheck_evalDist
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples)
    (coordinate : Fin (scalarDimension degree)) :
    evalDist (FormalProof4FHE.BinaryGuessCheck.correctCheck
      (coordinateSource q degree levels samples auxiliaryErrorSampler testRingErrorSampler
        gadget coordinate)
      (candidateCheck distinguisher coordinate)) =
      evalDist (realDecisionGame q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget distinguisher) := by
  unfold FormalProof4FHE.BinaryGuessCheck.correctCheck candidateCheck realDecisionGame
  rw [← bind_assoc]
  rw [evalDist_bind,
    correctCandidateView_evalDist q degree levels samples auxiliaryErrorSampler
      testRingErrorSampler gadget coordinate,
    ← evalDist_bind]

/-- Wrong candidate checks reproduce the uniform-test decision experiment. -/
theorem wrongCheck_evalDist
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (htestError : Pr[⊥ | testRingErrorSampler] = 0)
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples)
    (coordinate : Fin (scalarDimension degree)) :
    evalDist (FormalProof4FHE.BinaryGuessCheck.wrongCheck
      (coordinateSource q degree levels samples auxiliaryErrorSampler testRingErrorSampler
        gadget coordinate)
      (candidateCheck distinguisher coordinate)) =
      evalDist (uniformDecisionGame q degree levels samples auxiliaryErrorSampler gadget
        distinguisher) := by
  unfold FormalProof4FHE.BinaryGuessCheck.wrongCheck candidateCheck uniformDecisionGame
  rw [← bind_assoc]
  rw [evalDist_bind,
    wrongCandidateView_evalDist q degree levels samples auxiliaryErrorSampler
      testRingErrorSampler htestError gadget coordinate,
    ← evalDist_bind]

/-- Canonical sign of the decision gap, used as one bit of nonuniform reduction advice. -/
def orientation
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples) : Bool :=
  if (Pr[= true | uniformDecisionGame q degree levels samples auxiliaryErrorSampler gadget
      distinguisher]).toReal ≤
      (Pr[= true | realDecisionGame q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget distinguisher]).toReal then true else false

theorem orientation_le
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples) :
    if orientation q degree levels samples auxiliaryErrorSampler testRingErrorSampler gadget
      distinguisher then
      (Pr[= true | uniformDecisionGame q degree levels samples auxiliaryErrorSampler gadget
        distinguisher]).toReal ≤
      (Pr[= true | realDecisionGame q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget distinguisher]).toReal
    else
      (Pr[= true | realDecisionGame q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget distinguisher]).toReal ≤
      (Pr[= true | uniformDecisionGame q degree levels samples auxiliaryErrorSampler gadget
        distinguisher]).toReal := by
  unfold orientation
  split
  · assumption
  · exact le_of_not_ge ‹_›

/-- The oriented candidate-check gap at every coefficient equals the original decision
advantage exactly. -/
theorem orientedGap_eq_decisionAdvantage
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (htestError : Pr[⊥ | testRingErrorSampler] = 0)
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples)
    (coordinate : Fin (scalarDimension degree)) :
    FormalProof4FHE.BinaryGuessCheck.orientedGap
        (coordinateSource q degree levels samples auxiliaryErrorSampler testRingErrorSampler
          gadget coordinate)
        (orientation q degree levels samples auxiliaryErrorSampler testRingErrorSampler gadget
          distinguisher)
        (candidateCheck distinguisher coordinate) =
      decisionAdvantage q degree levels samples auxiliaryErrorSampler testRingErrorSampler
        gadget distinguisher := by
  unfold FormalProof4FHE.BinaryGuessCheck.orientedGap decisionAdvantage
    ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (correctCheck_evalDist q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget distinguisher coordinate),
    probOutput_congr rfl
      (wrongCheck_evalDist q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler htestError gadget distinguisher coordinate)]
  by_cases horientation : orientation q degree levels samples auxiliaryErrorSampler
      testRingErrorSampler gadget distinguisher = true
  · have hle := orientation_le q degree levels samples auxiliaryErrorSampler
      testRingErrorSampler gadget distinguisher
    rw [if_pos horientation] at hle ⊢
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  · have hle := orientation_le q degree levels samples auxiliaryErrorSampler
      testRingErrorSampler gadget distinguisher
    rw [if_neg horientation] at hle ⊢
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    ring

/-- Executable one-shot recovery experiment for one coefficient of the binary ring secret. -/
def coordinateRecoveryGame
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples)
    (coordinate : Fin (scalarDimension degree)) : ProbComp Bool :=
  FormalProof4FHE.BinaryGuessCheck.game
    (coordinateSource q degree levels samples auxiliaryErrorSampler testRingErrorSampler gadget
      coordinate)
    (orientation q degree levels samples auxiliaryErrorSampler testRingErrorSampler gadget
      distinguisher)
    (candidateCheck distinguisher coordinate)

/-- **Exact coefficient recovery.**  Every coefficient is recovered with probability one half
plus one half of the real-versus-uniform-test decision advantage. -/
theorem coordinateRecoveryGame_successProbability
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (htestError : Pr[⊥ | testRingErrorSampler] = 0)
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples)
    (coordinate : Fin (scalarDimension degree)) :
    (Pr[= true | coordinateRecoveryGame q degree levels samples auxiliaryErrorSampler
      testRingErrorSampler gadget distinguisher coordinate]).toReal =
      (1 + decisionAdvantage q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget distinguisher) / 2 := by
  unfold coordinateRecoveryGame
  rw [FormalProof4FHE.BinaryGuessCheck.successProbability_eq_half_add_orientedGap,
    orientedGap_eq_decisionAdvantage q degree levels samples auxiliaryErrorSampler
      testRingErrorSampler htestError gadget distinguisher coordinate]

/-- Equivalent exact failure formula for one recovered coefficient. -/
theorem coordinateRecoveryGame_failureProbability
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (htestError : Pr[⊥ | testRingErrorSampler] = 0)
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples)
    (coordinate : Fin (scalarDimension degree)) :
    Pr[= false | coordinateRecoveryGame q degree levels samples auxiliaryErrorSampler
      testRingErrorSampler gadget distinguisher coordinate] =
      ENNReal.ofReal ((1 - decisionAdvantage q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget distinguisher) / 2) := by
  unfold coordinateRecoveryGame
  rw [FormalProof4FHE.BinaryGuessCheck.failureProbability_eq_ofReal,
    orientedGap_eq_decisionAdvantage q degree levels samples auxiliaryErrorSampler
      testRingErrorSampler htestError gadget distinguisher coordinate]

/-! ## Simultaneous one-shot coefficient recovery -/

/-- One candidate guess for a selected coefficient after fixing the supplied public view. -/
def coefficientGuess
    {q degree levels samples : ℕ} [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples)
    (coordinate : Fin (scalarDimension degree))
    (view : ExtractedCircularView q degree levels samples) : ProbComp Bool :=
  FormalProof4FHE.BinaryGuessCheck.tester
    (orientation q degree levels samples auxiliaryErrorSampler testRingErrorSampler gadget
      distinguisher)
    (candidateCheck distinguisher coordinate) view

/-- Run the one-shot candidate tester independently for every extracted coefficient, sharing only
the supplied genuine-RGSW/real-test public view. -/
def flatSecretSolver
    {q degree levels samples : ℕ} [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples) :
    ExtractedCircularView q degree levels samples →
      ProbComp (BinarySecret (scalarDimension degree)) :=
  fun view ↦ Fin.mOfFn (scalarDimension degree) fun coordinate ↦
    coefficientGuess auxiliaryErrorSampler testRingErrorSampler gadget distinguisher
      coordinate view

/-- Reassemble the recovered coefficient vector into the original rank-one binary ring-key
shape. -/
def ringSecretSolver
    {q degree levels samples : ℕ} [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples) :
    ExtractedCircularView q degree levels samples → ProbComp (BinaryRingSecret degree) :=
  fun view ↦ keyUnextract <$>
    flatSecretSolver auxiliaryErrorSampler testRingErrorSampler gadget distinguisher view

/-- Joint experiment exposing the true extracted coefficient vector and the independently
assembled one-shot candidate vector. -/
def flatJointRecoveryGame
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples) :
    ProbComp (BinarySecret (scalarDimension degree) ×
      BinarySecret (scalarDimension degree)) := do
  let secret ← Native.sampleRingSecret 1 (degree + 1)
  let view ← fixedSecretRealViewSampler q degree levels samples auxiliaryErrorSampler
    testRingErrorSampler secret gadget
  let recovered ← flatSecretSolver auxiliaryErrorSampler testRingErrorSampler gadget
    distinguisher view
  return (keyExtract secret, recovered)

/-- Exact full-vector recovery game in flattened coefficient form. -/
def flatSecretRecoveryGame
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples) : ProbComp Bool :=
  (fun output ↦ decide (output.2 = output.1)) <$>
    flatJointRecoveryGame q degree levels samples auxiliaryErrorSampler testRingErrorSampler
      gadget distinguisher

/-- Exact full-ring-key recovery game after coefficient reassembly. -/
def ringSecretRecoveryGame
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples) : ProbComp Bool := do
  let secret ← Native.sampleRingSecret 1 (degree + 1)
  let view ← fixedSecretRealViewSampler q degree levels samples auxiliaryErrorSampler
    testRingErrorSampler secret gadget
  let recovered ← ringSecretSolver auxiliaryErrorSampler testRingErrorSampler gadget
    distinguisher view
  return decide (recovered = secret)

/-- Equality after coefficient reassembly is equivalent to equality of the complete extracted
coefficient vectors. -/
@[simp]
theorem keyUnextract_eq_ringSecret_iff
    {degree : ℕ} (candidate : BinarySecret (scalarDimension degree))
    (secret : BinaryRingSecret degree) :
    keyUnextract candidate = secret ↔ candidate = keyExtract secret := by
  constructor
  · intro h
    rw [← keyExtract_keyUnextract candidate]
    exact congrArg keyExtract h
  · rintro rfl
    exact keyUnextract_keyExtract secret

/-- Reassembly through the key-extraction equivalence does not change the recovery event. -/
theorem ringSecretRecoveryGame_eq_flatSecretRecoveryGame
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples) :
    ringSecretRecoveryGame q degree levels samples auxiliaryErrorSampler testRingErrorSampler
        gadget distinguisher =
      flatSecretRecoveryGame q degree levels samples auxiliaryErrorSampler testRingErrorSampler
        gadget distinguisher := by
  simp [ringSecretRecoveryGame, flatSecretRecoveryGame, flatJointRecoveryGame,
    ringSecretSolver, keyUnextract_eq_ringSecret_iff, map_eq_bind_pure_comp, monad_norm]

/-- Projecting the assembled joint experiment to one correctness bit gives exactly the standalone
coefficient-recovery experiment. -/
theorem evalDist_map_flatJointRecoveryGame_coordinate_eq_coordinateRecoveryGame
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples)
    (coordinate : Fin (scalarDimension degree)) :
    evalDist ((fun output ↦ decide (output.2 coordinate = output.1 coordinate)) <$>
      flatJointRecoveryGame q degree levels samples auxiliaryErrorSampler testRingErrorSampler
        gadget distinguisher) =
      evalDist (coordinateRecoveryGame q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget distinguisher coordinate) := by
  simp only [flatJointRecoveryGame, coordinateRecoveryGame, coordinateSource,
    flatSecretSolver, FormalProof4FHE.BinaryGuessCheck.game, coefficientGuess,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  refine evalDist_bind_congr' (Native.sampleRingSecret 1 (degree + 1)) fun secret ↦ ?_
  refine evalDist_bind_congr'
    (fixedSecretRealViewSampler q degree levels samples auxiliaryErrorSampler
      testRingErrorSampler secret gadget) fun view ↦ ?_
  have h := FormalProof4FHE.FiniteProduct.evalDist_map_fin_mOfFn_apply
    (scalarDimension degree)
    (fun index ↦ coefficientGuess auxiliaryErrorSampler testRingErrorSampler gadget
      distinguisher index view)
    coordinate (fun candidate ↦ decide (candidate = keyExtract secret coordinate))
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp] at h
  simpa only [Function.comp_def, coefficientGuess] using h

/-- Failure probability of one coordinate inside the common-view joint experiment. -/
def coordinateFailureProbability
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples)
    (coordinate : Fin (scalarDimension degree)) : ENNReal :=
  Pr[(fun output ↦ output.2 coordinate ≠ output.1 coordinate) |
    flatJointRecoveryGame q degree levels samples auxiliaryErrorSampler testRingErrorSampler
      gadget distinguisher]

/-- The joint coordinate-failure event is exactly failure in the standalone coefficient game. -/
theorem coordinateFailureProbability_eq_coordinateRecoveryGame
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples)
    (coordinate : Fin (scalarDimension degree)) :
    coordinateFailureProbability q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget distinguisher coordinate =
      Pr[= false | coordinateRecoveryGame q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget distinguisher coordinate] := by
  unfold coordinateFailureProbability
  calc
    _ = Pr[= false |
        (fun output ↦ decide (output.2 coordinate = output.1 coordinate)) <$>
          flatJointRecoveryGame q degree levels samples auxiliaryErrorSampler
            testRingErrorSampler gadget distinguisher] := by
      rw [probOutput_map]
      congr 1
      funext output
      simp
    _ = _ := probOutput_congr rfl
      (evalDist_map_flatJointRecoveryGame_coordinate_eq_coordinateRecoveryGame q degree
        levels samples auxiliaryErrorSampler testRingErrorSampler gadget distinguisher
        coordinate)

/-- Whole extracted-key failure is contained in the union of all coefficient failures. -/
theorem wholeKeyFailure_le_sum_coordinateFailure
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples) :
    Pr[(fun output ↦ output.2 ≠ output.1) |
        flatJointRecoveryGame q degree levels samples auxiliaryErrorSampler testRingErrorSampler
          gadget distinguisher] ≤
      ∑ coordinate,
        coordinateFailureProbability q degree levels samples auxiliaryErrorSampler
          testRingErrorSampler gadget distinguisher coordinate := by
  classical
  let experiment := flatJointRecoveryGame q degree levels samples auxiliaryErrorSampler
    testRingErrorSampler gadget distinguisher
  have hevent :
      (fun output : BinarySecret (scalarDimension degree) ×
          BinarySecret (scalarDimension degree) ↦ output.2 ≠ output.1) =
      (fun output ↦ ∃ coordinate ∈
          (Finset.univ : Finset (Fin (scalarDimension degree))),
        output.2 coordinate ≠ output.1 coordinate) := by
    funext output
    apply propext
    constructor
    · intro hne
      by_contra hnone
      have hall : ∀ coordinate, output.2 coordinate = output.1 coordinate := by
        intro coordinate
        by_contra hcoordinate
        exact hnone ⟨coordinate, Finset.mem_univ coordinate, hcoordinate⟩
      exact hne (funext hall)
    · rintro ⟨coordinate, _hcoordinate, hne⟩ heq
      exact hne (congrFun heq coordinate)
  rw [show flatJointRecoveryGame q degree levels samples auxiliaryErrorSampler
      testRingErrorSampler gadget distinguisher = experiment from rfl, hevent]
  simpa [coordinateFailureProbability, experiment] using
    (probEvent_exists_finset_le_sum
      (Finset.univ : Finset (Fin (scalarDimension degree))) experiment
      (fun coordinate output ↦ output.2 coordinate ≠ output.1 coordinate))

/-- **Full one-shot coefficient recovery.**  The per-coordinate decision errors assemble by a
finite union bound into recovery of the complete binary ring secret.  This bound is exact but is
only useful without further amplification when the decision advantage is sufficiently close to
one. -/
theorem one_sub_sum_decisionError_le_ringSecretRecovery
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (htestError : Pr[⊥ | testRingErrorSampler] = 0)
    (gadget : Fin levels → Ring q degree)
    (distinguisher : Distinguisher q degree levels samples) :
    1 - ∑ _coordinate : Fin (scalarDimension degree),
        ENNReal.ofReal ((1 - decisionAdvantage q degree levels samples auxiliaryErrorSampler
          testRingErrorSampler gadget distinguisher) / 2) ≤
      Pr[= true | ringSecretRecoveryGame q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler gadget distinguisher] := by
  classical
  let experiment := flatJointRecoveryGame q degree levels samples auxiliaryErrorSampler
    testRingErrorSampler gadget distinguisher
  have hfailure :
      Pr[(fun output ↦ output.2 ≠ output.1) | experiment] ≤
        ∑ _coordinate : Fin (scalarDimension degree),
          ENNReal.ofReal ((1 - decisionAdvantage q degree levels samples
            auxiliaryErrorSampler testRingErrorSampler gadget distinguisher) / 2) := by
    exact (wholeKeyFailure_le_sum_coordinateFailure q degree levels samples
      auxiliaryErrorSampler testRingErrorSampler gadget distinguisher).trans
        (Finset.sum_le_sum fun coordinate _ ↦ by
          rw [coordinateFailureProbability_eq_coordinateRecoveryGame,
            coordinateRecoveryGame_failureProbability q degree levels samples
              auxiliaryErrorSampler testRingErrorSampler htestError gadget distinguisher
              coordinate])
  have hsuccess :
      1 - ∑ _coordinate : Fin (scalarDimension degree),
          ENNReal.ofReal ((1 - decisionAdvantage q degree levels samples
            auxiliaryErrorSampler testRingErrorSampler gadget distinguisher) / 2) ≤
        Pr[(fun output ↦ output.2 = output.1) | experiment] :=
    probEvent_one_sub_le_of_compl_le probFailure_eq_zero hfailure
  rw [ringSecretRecoveryGame_eq_flatSecretRecoveryGame]
  unfold flatSecretRecoveryGame
  rw [probOutput_map]
  simpa only [decide_eq_true_eq, experiment] using hsuccess

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.ExtractedGuessCheck.CoefficientRecovery
