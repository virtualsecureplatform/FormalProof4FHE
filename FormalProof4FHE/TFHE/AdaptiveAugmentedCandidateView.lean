/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.BinaryGuessCheck
import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.Probability.MajorityAmplification
import FormalProof4FHE.TFHE.AdaptiveAugmentedPairedRecovery

/-!
# Averaged Candidate Views for Augmented Adaptive TFHE CircLWE

This module carries the native scalar-coordinate search-to-decision accounting directly over the
public augmented view `(BRK, KSK, bounded input tape)`.  A candidate transformer sees only that
public view.  Its correct and wrong laws may hold after averaging over the complete source
experiment, and shared-context amplification retains the explicit threshold/bad-fiber loss.

The resulting scalar reduction plugs into `AdaptiveAugmentedPairedRecovery`: centered-binomial
KSK decoding then completes scalar recovery to the paired native key without loss.  Thus a future
shifted evaluator only has to construct the averaged augmented transformer and bound its two view
errors; the coordinate union bound, amplification, and paired completion are checked here.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery

open Native
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery

variable
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]

/-- Public context shared by all augmented scalar-coordinate checks. -/
abbrev PublicContext
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) :=
  Challenge q degree ringRank tgswLevels lweDimension ×
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount

/-- A randomized test for one coordinate of the native scalar key. -/
abbrev CoordinateTester
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) :=
  Fin lweDimension →
    Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount → ProbComp Bool

/-- Candidate-dependent public check for one scalar coordinate. -/
abbrev CandidateCheck
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) :=
  Fin lweDimension → Bool →
    Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount → ProbComp Bool

/-- Complete augmented real source with the scalar secret retained for vector recovery. -/
noncomputable def scalarSource
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (BinarySecret lweDimension ×
      PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let secrets ←
    (problem (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget).sampleSecret
  let challenge ←
    (problem (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget).sampleChallenge secrets
  let auxiliary ←
    (problem (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary secrets
  return (secrets.1, challenge, auxiliary)

/-- One scalar coordinate paired with the complete correlated augmented public context. -/
noncomputable def coordinateSource
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp (Bool ×
      PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let hiddenAndContext ← scalarSource (ringRank := ringRank) (queryCount := queryCount)
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
  return (hiddenAndContext.1 coordinate, hiddenAndContext.2)

/-- Turn coordinate tests into one augmented scalar solver. -/
def assemble
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount) :
    ScalarSolver q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  fun challenge auxiliary ↦
    Fin.mOfFn lweDimension fun coordinate ↦ tester coordinate challenge auxiliary

/-- One candidate guess after fixing the complete augmented public context. -/
def candidateGuess
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount →
      ProbComp Bool :=
  fun context ↦
    FormalProof4FHE.BinaryGuessCheck.tester (orientation coordinate)
      (fun candidate context ↦ check coordinate candidate context.1 context.2) context

/-- Executable unamplified coordinate tester. -/
def testerOfCheck
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount) :
    CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  fun coordinate challenge auxiliary ↦
    candidateGuess orientation check coordinate (challenge, auxiliary)

/-- Majority-amplified coordinate tester, reusing one augmented public context. -/
def amplifiedTesterOfCheck
    (rounds : Fin lweDimension → ℕ)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount) :
    CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  fun coordinate challenge auxiliary ↦
    FormalProof4FHE.MajorityAmplification.amplify (rounds coordinate)
      (candidateGuess orientation check coordinate) (challenge, auxiliary)

/-- Standalone correctness game for one augmented coordinate test. -/
noncomputable def coordinateGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) : ProbComp Bool := do
  let hiddenAndContext ← scalarSource (ringRank := ringRank) (queryCount := queryCount)
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
  let candidate ← tester coordinate hiddenAndContext.2.1 hiddenAndContext.2.2
  return decide (candidate = hiddenAndContext.1 coordinate)

/-- Native augmented candidate-check acceptance gap for one coordinate. -/
noncomputable def candidateCheckGap
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) : ℝ :=
  FormalProof4FHE.BinaryGuessCheck.orientedGap
    (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
      ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
      keySwitchGadget coordinate)
    (orientation coordinate)
    (fun candidate context ↦ check coordinate candidate context.1 context.2)

/-- Exact one-shot augmented coordinate failure. -/
theorem coordinateGame_testerOfCheck_failureProbability_eq_ofReal
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    Pr[= false |
      coordinateGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget (testerOfCheck orientation check) coordinate] =
      ENNReal.ofReal ((1 - candidateCheckGap ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget orientation check coordinate) / 2) := by
  simpa [coordinateGame, coordinateSource, scalarSource, testerOfCheck, candidateGuess,
    candidateCheckGap, FormalProof4FHE.BinaryGuessCheck.game, monad_norm] using
    (FormalProof4FHE.BinaryGuessCheck.failureProbability_eq_ofReal
      (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        keySwitchGadget coordinate)
      (orientation coordinate)
      (fun candidate context ↦ check coordinate candidate context.1 context.2))

/-- Exact one-shot augmented coordinate success.  This is the operational counterpart of the
signed candidate-check gap and does not reuse the public context. -/
theorem coordinateGame_testerOfCheck_successProbability_toReal
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    (Pr[= true |
      coordinateGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget (testerOfCheck orientation check) coordinate]).toReal =
      (1 + candidateCheckGap ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget orientation check coordinate) / 2 := by
  simpa [coordinateGame, coordinateSource, scalarSource, testerOfCheck, candidateGuess,
    candidateCheckGap, FormalProof4FHE.BinaryGuessCheck.game, monad_norm] using
    (FormalProof4FHE.BinaryGuessCheck.successProbability_eq_half_add_orientedGap
      (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        keySwitchGadget coordinate)
      (orientation coordinate)
      (fun candidate context ↦ check coordinate candidate context.1 context.2))

/-! ## Public augmented decision endpoints -/

/-- Complete real public augmented view at the target error distribution. -/
noncomputable def realPublicView
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let secrets ←
    (KeySwitchFirstFiniteView.augmentedCircularProblem
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget).sampleSecret
  let challenge ←
    (KeySwitchFirstFiniteView.augmentedCircularProblem
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget).sampleReal secrets
  let auxiliary ←
    (KeySwitchFirstFiniteView.augmentedCircularProblem
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget).sampleAuxiliary secrets
  return (challenge, auxiliary)

/-- Uniform-BRK public endpoint with the same real KSK and bounded input tape. -/
noncomputable def uniformPublicView
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let secrets ←
    (KeySwitchFirstFiniteView.augmentedCircularProblem
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget).sampleSecret
  let challenge ←
    (KeySwitchFirstFiniteView.augmentedCircularProblem
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget).sampleUniform
  let auxiliary ←
    (KeySwitchFirstFiniteView.augmentedCircularProblem
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget).sampleAuxiliary secrets
  return (challenge, auxiliary)

/-- Forgetting the hidden coordinate from the candidate source recovers exactly the complete
real augmented circular view.  In particular, the shifted-candidate construction is a
search-to-decision reduction *inside* the native CircLWE experiment: its source already contains
the real monomial BRK, real KSK, and bounded input tape. -/
theorem coordinateSource_context_evalDist_eq_realPublicView
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        ((fun hiddenAndContext ↦ hiddenAndContext.2) <$>
          coordinateSource (ringRank := ringRank) (queryCount := queryCount)
            ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget coordinate) =
      evalDist
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget) := by
  simp [coordinateSource, scalarSource, realPublicView, problem,
    LWE.AuxiliaryInput.Search.exactRecoveryProblem,
    KeySwitchFirstFiniteView.augmentedCircularProblem, liftM, monad_norm]

/-- Real public decision game in factored-view form. -/
noncomputable def realDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ProbComp Bool :=
  realPublicView (ringRank := ringRank) (queryCount := queryCount)
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget >>=
      fun context ↦ distinguisher context.1 context.2

/-- Uniform-BRK public decision game in factored-view form. -/
noncomputable def uniformDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ProbComp Bool :=
  uniformPublicView (ringRank := ringRank) (queryCount := queryCount)
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget >>=
      fun context ↦ distinguisher context.1 context.2

/-- The factored decision distance is the generic public augmented CircLWE advantage. -/
theorem boolDistAdvantage_realDecisionGame_uniformDecisionGame_eq_publicAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    (realDecisionGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher).boolDistAdvantage
      (uniformDecisionGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher) =
      LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (KeySwitchFirstFiniteView.augmentedCircularProblem
          (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
          ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget)
        distinguisher := by
  unfold LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
    LWE.AuxiliaryInput.circularLweAdvantage
  congr 1 <;>
    simp [realDecisionGame, uniformDecisionGame, realPublicView, uniformPublicView,
      LWE.AuxiliaryInput.realGame, LWE.AuxiliaryInput.uniformGame,
      LWE.AuxiliaryInput.SearchToDecision.publicContinuation, monad_norm]

/-- Canonical nonuniform sign bit of an augmented public distinguisher. -/
noncomputable def orientation
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : Bool :=
  if (Pr[= true | uniformDecisionGame ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget distinguisher]).toReal ≤
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher]).toReal then true else false

theorem orientation_le
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    if orientation ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher then
      (Pr[= true | uniformDecisionGame ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher]).toReal ≤
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher]).toReal
    else
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher]).toReal ≤
      (Pr[= true | uniformDecisionGame ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher]).toReal := by
  unfold orientation
  split
  · assumption
  · exact le_of_not_ge ‹_›

/-! ## Averaged augmented candidate-view contract -/

/-- Candidate transformation whose laws hold over the complete augmented source distribution. -/
structure AveragedCandidateViewTransformer
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  transform : Fin lweDimension → Bool →
    Challenge q degree ringRank tgswLevels lweDimension →
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)
  correctError : Fin lweDimension → ℝ
  wrongError : Fin lweDimension → ℝ
  correctError_nonneg : ∀ coordinate, 0 ≤ correctError coordinate
  wrongError_nonneg : ∀ coordinate, 0 ≤ wrongError coordinate
  correctDistance : ∀ coordinate,
    tvDist
        (do
          let hiddenAndContext ← coordinateSource (ringRank := ringRank)
            (queryCount := queryCount) sourceRingErrorSampler
            sourceKeySwitchErrorSampler inputErrorSampler tgswGadget
            keySwitchGadget coordinate
          transform coordinate hiddenAndContext.1 hiddenAndContext.2.1
            hiddenAndContext.2.2)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler
          targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget) ≤
      correctError coordinate
  wrongDistance : ∀ coordinate,
    tvDist
        (do
          let hiddenAndContext ← coordinateSource (ringRank := ringRank)
            (queryCount := queryCount) sourceRingErrorSampler
            sourceKeySwitchErrorSampler inputErrorSampler tgswGadget
            keySwitchGadget coordinate
          transform coordinate (!hiddenAndContext.1) hiddenAndContext.2.1
            hiddenAndContext.2.2)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler
          targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget) ≤
      wrongError coordinate

namespace AveragedCandidateViewTransformer

/-- Postcompose an augmented candidate transformer with its public decision distinguisher. -/
def toCheck
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  fun coordinate candidate challenge auxiliary ↦ do
    let transformed ← transformer.transform coordinate candidate challenge auxiliary
    distinguisher transformed.1 transformed.2

/-- Executable one-shot predictor induced by an averaged native candidate transformer.  The
orientation is chosen only from the public decision distinguisher. -/
noncomputable def toCoordinateTester
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  testerOfCheck
    (fun _ ↦ orientation targetRingErrorSampler targetKeySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget distinguisher)
    (transformer.toCheck distinguisher)

/-- Signed prediction bias of the executable one-shot coordinate tester. -/
noncomputable def coordinatePredictionBias
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) : ℝ :=
  2 * (Pr[= true |
    coordinateGame sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget (transformer.toCoordinateTester distinguisher)
      coordinate]).toReal - 1

/-- The operational one-shot prediction bias is exactly the averaged candidate-check gap. -/
theorem coordinatePredictionBias_eq_candidateCheckGap
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    transformer.coordinatePredictionBias distinguisher coordinate =
      candidateCheckGap sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget
        (fun _ ↦ orientation targetRingErrorSampler targetKeySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget distinguisher)
        (transformer.toCheck distinguisher) coordinate := by
  rw [coordinatePredictionBias, toCoordinateTester,
    coordinateGame_testerOfCheck_successProbability_toReal]
  ring

/-- Averaged correct/wrong augmented-view distances yield the oriented one-shot candidate gap. -/
theorem publicAdvantage_sub_errors_le_candidateCheckGap
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (KeySwitchFirstFiniteView.augmentedCircularProblem
          (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
          targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget)
        distinguisher - transformer.correctError coordinate - transformer.wrongError coordinate ≤
      candidateCheckGap sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget
        (fun _ ↦ orientation targetRingErrorSampler targetKeySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget distinguisher)
        (transformer.toCheck distinguisher) coordinate := by
  let source := coordinateSource (ringRank := ringRank) (queryCount := queryCount)
    sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget coordinate
  let finish := fun context : PublicContext q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount ↦ distinguisher context.1 context.2
  let correctView := source >>= fun hiddenAndContext ↦
    transformer.transform coordinate hiddenAndContext.1
      hiddenAndContext.2.1 hiddenAndContext.2.2
  let wrongView := source >>= fun hiddenAndContext ↦
    transformer.transform coordinate (!hiddenAndContext.1)
      hiddenAndContext.2.1 hiddenAndContext.2.2
  let correct := correctView >>= finish
  let wrong := wrongView >>= finish
  have hcorrect : tvDist correct
      (realDecisionGame targetRingErrorSampler targetKeySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher) ≤
      transformer.correctError coordinate := by
    exact (tvDist_bind_right_le finish _ _).trans
      (by simpa only [correctView, source] using transformer.correctDistance coordinate)
  have hwrong : tvDist wrong
      (uniformDecisionGame targetRingErrorSampler targetKeySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher) ≤
      transformer.wrongError coordinate := by
    exact (tvDist_bind_right_le finish _ _).trans
      (by simpa only [wrongView, source] using transformer.wrongDistance coordinate)
  have hgap := FormalProof4FHE.BinaryGuessCheck.orientedAcceptanceGap_lowerBound_of_tvDist
    correct wrong
    (realDecisionGame targetRingErrorSampler targetKeySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget distinguisher)
    (uniformDecisionGame targetRingErrorSampler targetKeySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget distinguisher)
    (orientation targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher)
    (transformer.correctError coordinate) (transformer.wrongError coordinate)
    (orientation_le targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher)
    hcorrect hwrong
  rw [← boolDistAdvantage_realDecisionGame_uniformDecisionGame_eq_publicAdvantage
    targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget distinguisher]
  simpa [candidateCheckGap, FormalProof4FHE.BinaryGuessCheck.orientedGap,
    FormalProof4FHE.BinaryGuessCheck.correctCheck,
    FormalProof4FHE.BinaryGuessCheck.wrongCheck, toCheck, correct, wrong,
    correctView, wrongView, source, finish, monad_norm] using hgap

/-- **One-coordinate search-to-decision bound.**

The public augmented CircLWE advantage is at most the signed bias of one executable scalar-bit
predictor plus the two native statistical view errors.  Unlike whole-key recovery, this theorem
uses no shared-context amplification and therefore incurs no threshold or bad-fiber loss. -/
theorem publicAdvantage_le_coordinatePredictionBias_add_errors
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (KeySwitchFirstFiniteView.augmentedCircularProblem
          (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
          targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget)
        distinguisher ≤
      transformer.coordinatePredictionBias distinguisher coordinate +
        transformer.correctError coordinate + transformer.wrongError coordinate := by
  have hgap := transformer.publicAdvantage_sub_errors_le_candidateCheckGap
    distinguisher coordinate
  rw [← transformer.coordinatePredictionBias_eq_candidateCheckGap
    distinguisher coordinate] at hgap
  linarith

/-- One-shot augmented coordinate failure induced by an averaged transformer. -/
theorem coordinateFailure_le
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    Pr[= false |
      coordinateGame sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget
        (testerOfCheck
          (fun _ ↦ orientation targetRingErrorSampler targetKeySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget distinguisher)
          (transformer.toCheck distinguisher)) coordinate] ≤
      ENNReal.ofReal
        ((1 - (LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
          (KeySwitchFirstFiniteView.augmentedCircularProblem
            (ringRank := ringRank) (lweDimension := lweDimension)
            (queryCount := queryCount) targetRingErrorSampler
            targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
          distinguisher - transformer.correctError coordinate -
            transformer.wrongError coordinate)) / 2) := by
  rw [coordinateGame_testerOfCheck_failureProbability_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  have hgap := transformer.publicAdvantage_sub_errors_le_candidateCheckGap
    distinguisher coordinate
  linarith

/-- Thresholded shared-context amplification for an averaged augmented candidate law. -/
theorem amplifiedCoordinateFailure_le_threshold
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (rounds : Fin lweDimension → ℕ) (coordinate : Fin lweDimension)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1) :
    Pr[= false |
      coordinateGame sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget
        (amplifiedTesterOfCheck rounds
          (fun _ ↦ orientation targetRingErrorSampler targetKeySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget distinguisher)
          (transformer.toCheck distinguisher)) coordinate] ≤
      FormalProof4FHE.MajorityAmplification.amplifiedError
          (rounds coordinate) threshold +
        ENNReal.ofReal
          ((1 - (LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
            (KeySwitchFirstFiniteView.augmentedCircularProblem
              (ringRank := ringRank) (lweDimension := lweDimension)
              (queryCount := queryCount) targetRingErrorSampler
              targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
            distinguisher - transformer.correctError coordinate -
              transformer.wrongError coordinate)) / 2) / threshold := by
  let source := coordinateSource (ringRank := ringRank) (queryCount := queryCount)
    sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget coordinate
  let guess := candidateGuess
    (fun _ ↦ orientation targetRingErrorSampler targetKeySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget distinguisher)
    (transformer.toCheck distinguisher) coordinate
  have haverage :
      Pr[= false | FormalProof4FHE.MajorityAmplification.recoveryGame source guess] ≤
        ENNReal.ofReal
          ((1 - (LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
            (KeySwitchFirstFiniteView.augmentedCircularProblem
              (ringRank := ringRank) (lweDimension := lweDimension)
              (queryCount := queryCount) targetRingErrorSampler
              targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
            distinguisher - transformer.correctError coordinate -
              transformer.wrongError coordinate)) / 2) := by
    simpa [coordinateGame, scalarSource, coordinateSource, testerOfCheck,
      candidateGuess, source, guess,
      FormalProof4FHE.MajorityAmplification.recoveryGame,
      FormalProof4FHE.MajorityAmplification.correctness, monad_norm] using
      (transformer.coordinateFailure_le distinguisher coordinate)
  have h := FormalProof4FHE.MajorityAmplification.recoveryGame_amplify_failure_le_of_average
    source guess (rounds coordinate) threshold
    (ENNReal.ofReal
      ((1 - (LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (KeySwitchFirstFiniteView.augmentedCircularProblem
          (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler
          targetKeySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget)
        distinguisher - transformer.correctError coordinate -
          transformer.wrongError coordinate)) / 2))
    hthreshold_pos hthreshold_one haverage
  simpa [coordinateGame, scalarSource, coordinateSource, amplifiedTesterOfCheck,
    testerOfCheck, candidateGuess, source, guess,
    FormalProof4FHE.MajorityAmplification.recoveryGame,
    FormalProof4FHE.MajorityAmplification.correctness, monad_norm] using h

end AveragedCandidateViewTransformer

/-! ## Coordinate union bound and scalar reduction -/

/-- Joint augmented experiment exposing the hidden scalar key and assembled candidate. -/
noncomputable def jointGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount) :
    ProbComp (BinarySecret lweDimension × BinarySecret lweDimension) := do
  let hiddenAndContext ← scalarSource (ringRank := ringRank) (queryCount := queryCount)
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
  let candidate ← assemble tester hiddenAndContext.2.1 hiddenAndContext.2.2
  return (hiddenAndContext.1, candidate)

/-- Projecting the assembled augmented experiment to one coordinate gives its standalone game. -/
theorem evalDist_map_jointGame_coordinate_eq_coordinateGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    evalDist
        ((fun output ↦ decide (output.2 coordinate = output.1 coordinate)) <$>
          jointGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget tester) =
      evalDist
        (coordinateGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget tester coordinate) := by
  simp only [jointGame, coordinateGame, assemble, map_eq_bind_pure_comp, bind_assoc]
  apply evalDist_bind_congr'
  intro hiddenAndContext
  simp only [pure_bind, Function.comp_apply]
  have h := FormalProof4FHE.FiniteProduct.evalDist_map_fin_mOfFn_apply lweDimension
    (fun index ↦ tester index hiddenAndContext.2.1 hiddenAndContext.2.2) coordinate
    (fun candidate ↦ decide (candidate = hiddenAndContext.1 coordinate))
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp] at h
  simpa only [Function.comp_def] using h

/-- The scalar success game for an assembled tester is equality in the joint experiment. -/
theorem scalarGame_assemble_eq_map_jointGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount) :
    scalarGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget (assemble tester) =
      (fun output ↦ decide (output.2 = output.1)) <$>
        jointGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget tester := by
  simp [scalarGame, scalarSource, jointGame, assemble, map_eq_bind_pure_comp,
    monad_norm]

/-- Failure of the assembled scalar candidate is bounded by the sum of coordinate failures. -/
theorem one_sub_sum_coordinateGameError_le_scalarSuccess
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount)
    (error : Fin lweDimension → ENNReal)
    (hcoordinate : ∀ coordinate,
      Pr[= false |
        coordinateGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget tester coordinate] ≤ error coordinate) :
    1 - ∑ coordinate, error coordinate ≤
      Pr[= true |
        scalarGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget (assemble tester)] := by
  classical
  let experiment := jointGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget tester
  have hcoordinate' (coordinate : Fin lweDimension) :
      Pr[(fun output : BinarySecret lweDimension × BinarySecret lweDimension ↦
          output.2 coordinate ≠ output.1 coordinate) | experiment] ≤
        error coordinate := by
    calc
      _ = Pr[= false |
          (fun output ↦ decide (output.2 coordinate = output.1 coordinate)) <$>
            experiment] := by
          rw [probOutput_map]
          congr 1
          funext output
          simp
      _ = Pr[= false |
          coordinateGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget tester coordinate] :=
        probOutput_congr rfl
          (evalDist_map_jointGame_coordinate_eq_coordinateGame ringErrorSampler
            keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
            tester coordinate)
      _ ≤ _ := hcoordinate coordinate
  have hevent :
      (fun output : BinarySecret lweDimension × BinarySecret lweDimension ↦
        output.2 ≠ output.1) =
      (fun output ↦ ∃ coordinate ∈ (Finset.univ : Finset (Fin lweDimension)),
        output.2 coordinate ≠ output.1 coordinate) := by
    funext output
    apply propext
    constructor
    · intro hne
      by_contra hnone
      apply hne
      funext coordinate
      by_contra hcoordinateNe
      exact hnone ⟨coordinate, Finset.mem_univ coordinate, hcoordinateNe⟩
    · rintro ⟨coordinate, _hcoordinate, hne⟩ heq
      exact hne (congrFun heq coordinate)
  have hfailure :
      Pr[(fun output : BinarySecret lweDimension × BinarySecret lweDimension ↦
          output.2 ≠ output.1) | experiment] ≤ ∑ coordinate, error coordinate := by
    rw [hevent]
    exact (probEvent_exists_finset_le_sum (Finset.univ : Finset (Fin lweDimension))
      experiment
      (fun coordinate output ↦ output.2 coordinate ≠ output.1 coordinate)).trans
        (Finset.sum_le_sum fun coordinate _ ↦ hcoordinate' coordinate)
  have hsuccess :
      1 - ∑ coordinate, error coordinate ≤
        Pr[(fun output : BinarySecret lweDimension × BinarySecret lweDimension ↦
          output.2 = output.1) | experiment] :=
    probEvent_one_sub_le_of_compl_le probFailure_eq_zero hfailure
  rw [scalarGame_assemble_eq_map_jointGame, probOutput_map]
  simpa only [decide_eq_true_eq, experiment] using hsuccess

/-- Complete averaged augmented transformer certificate with explicit amplification choices. -/
structure AveragedCandidateViewTransformerReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount
      ringEta keySwitchEta : ℕ)
    [NeZero q]
    (inputErrorSampler : ProbComp (ZMod q))
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toTransformer :
    PublicDistinguisher q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount →
    AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      (RLWE.CenteredBinomial.sampler q degree ringEta) targetRingErrorSampler
      (CenteredBinomial.scalarSampler q keySwitchEta) targetKeySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget
  rounds : PublicDistinguisher q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount → Fin lweDimension → ℕ
  threshold : PublicDistinguisher q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount → Fin lweDimension → ENNReal
  threshold_pos : ∀ distinguisher coordinate, 0 < threshold distinguisher coordinate
  threshold_le_one : ∀ distinguisher coordinate, threshold distinguisher coordinate ≤ 1

namespace AveragedCandidateViewTransformerReduction

/-- Effective public distinguishing gap after both augmented view errors. -/
noncomputable def effectiveGap
    {ringEta keySwitchEta : ℕ}
    {inputErrorSampler : ProbComp (ZMod q)}
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedCandidateViewTransformerReduction q degree ringRank
      tgswLevels lweDimension keySwitchLevels queryCount ringEta keySwitchEta
      inputErrorSampler targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) : ℝ :=
  LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
      (KeySwitchFirstFiniteView.augmentedCircularProblem
        (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
        targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget)
      distinguisher -
    (reduction.toTransformer distinguisher).correctError coordinate -
    (reduction.toTransformer distinguisher).wrongError coordinate

/-- Sound thresholded error for one augmented scalar coordinate. -/
noncomputable def thresholdedCoordinateError
    {ringEta keySwitchEta : ℕ}
    {inputErrorSampler : ProbComp (ZMod q)}
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedCandidateViewTransformerReduction q degree ringRank
      tgswLevels lweDimension keySwitchLevels queryCount ringEta keySwitchEta
      inputErrorSampler targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) : ENNReal :=
  FormalProof4FHE.MajorityAmplification.amplifiedError
      (reduction.rounds distinguisher coordinate)
      (reduction.threshold distinguisher coordinate) +
    ENNReal.ofReal ((1 - reduction.effectiveGap distinguisher coordinate) / 2) /
      reduction.threshold distinguisher coordinate

/-- Averaged augmented candidate evaluation gives the scalar cross-distribution reduction. -/
noncomputable def toScalarSecretReduction
    {ringEta keySwitchEta : ℕ}
    {inputErrorSampler : ProbComp (ZMod q)}
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedCandidateViewTransformerReduction q degree ringRank
      tgswLevels lweDimension keySwitchLevels queryCount ringEta keySwitchEta
      inputErrorSampler targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget) :
    ScalarSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      queryCount ringEta keySwitchEta inputErrorSampler targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget where
  toScalarSolver := fun distinguisher ↦ assemble
    (amplifiedTesterOfCheck (reduction.rounds distinguisher)
      (fun _ ↦ orientation targetRingErrorSampler targetKeySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher)
      ((reduction.toTransformer distinguisher).toCheck distinguisher))
  loss := fun distinguisher ↦
    (∑ coordinate, reduction.thresholdedCoordinateError distinguisher coordinate).toReal
  loss_nonneg := fun _ ↦ ENNReal.toReal_nonneg
  advantage_le := by
    intro distinguisher
    let errors : Fin lweDimension → ENNReal :=
      reduction.thresholdedCoordinateError distinguisher
    let tester := amplifiedTesterOfCheck (reduction.rounds distinguisher)
      (fun _ ↦ orientation targetRingErrorSampler targetKeySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher)
      ((reduction.toTransformer distinguisher).toCheck distinguisher)
    have hcoordinate : ∀ coordinate,
        Pr[= false |
          coordinateGame (RLWE.CenteredBinomial.sampler q degree ringEta)
            (CenteredBinomial.scalarSampler q keySwitchEta) inputErrorSampler
            tgswGadget keySwitchGadget tester coordinate] ≤ errors coordinate := by
      intro coordinate
      simpa only [errors, tester, thresholdedCoordinateError, effectiveGap] using
        (reduction.toTransformer distinguisher).amplifiedCoordinateFailure_le_threshold
          distinguisher (reduction.rounds distinguisher) coordinate
          (reduction.threshold distinguisher coordinate)
          (reduction.threshold_pos distinguisher coordinate)
          (reduction.threshold_le_one distinguisher coordinate)
    have hsuccess := one_sub_sum_coordinateGameError_le_scalarSuccess
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta) inputErrorSampler
      tgswGadget keySwitchGadget tester errors hcoordinate
    have hsuccessReal := ENNReal.toReal_mono probOutput_ne_top hsuccess
    have herror_ne_top : ∀ coordinate, errors coordinate ≠ ⊤ := by
      intro coordinate
      apply ENNReal.add_ne_top.mpr
      constructor
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top
          (FormalProof4FHE.MajorityAmplification.amplifiedError_le_one
            (reduction.rounds distinguisher coordinate)
            (reduction.threshold_le_one distinguisher coordinate))
      · apply ENNReal.div_ne_top
        · simp
        · exact ne_of_gt (reduction.threshold_pos distinguisher coordinate)
    have hsum_ne_top : (∑ coordinate, errors coordinate) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun coordinate _ ↦ herror_ne_top coordinate
    have hadv := LWE.AuxiliaryInput.SearchToDecision.publicAdvantage_le_one
      (KeySwitchFirstFiniteView.augmentedCircularProblem
        (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
        targetRingErrorSampler targetKeySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget)
      distinguisher
    have hone : (1 : ℝ) ≤
        (1 - ∑ coordinate, errors coordinate).toReal +
          (∑ coordinate, errors coordinate).toReal := by
      by_cases hsum : (∑ coordinate, errors coordinate) ≤ 1
      · rw [ENNReal.toReal_sub_of_le hsum ENNReal.one_ne_top, ENNReal.toReal_one]
        linarith
      · have honeSum : 1 ≤ ∑ coordinate, errors coordinate := le_of_not_ge hsum
        rw [tsub_eq_zero_of_le honeSum, ENNReal.toReal_zero, zero_add,
          ← ENNReal.toReal_one]
        exact ENNReal.toReal_mono hsum_ne_top honeSum
    exact (hadv.trans hone).trans (add_le_add hsuccessReal le_rfl)

/-- The same augmented certificate gives a paired-secret cross reduction under KSK decoding. -/
noncomputable def toPairedSecretReduction
    {ringEta keySwitchEta : ℕ}
    {inputErrorSampler : ProbComp (ZMod q)}
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedCandidateViewTransformerReduction q degree ringRank
      tgswLevels lweDimension keySwitchLevels queryCount ringEta keySwitchEta
      inputErrorSampler targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    PairedSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      queryCount ringEta keySwitchEta inputErrorSampler targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget :=
  reduction.toScalarSecretReduction.toPairedSecretReduction level hmargin

end AveragedCandidateViewTransformerReduction

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery
