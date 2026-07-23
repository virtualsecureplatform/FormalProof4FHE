/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.BinaryGuessCheck
import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.Probability.MajorityAmplification
import FormalProof4FHE.TFHE.AuxiliaryInputPairedRecovery

/-!
# Coordinatewise Recovery of the Native TFHE Scalar Key

After the real key-switch key completes a correct scalar-key candidate to the native ring key,
the remaining search-to-decision task is coordinatewise.  This module makes that statement
quantitative.  A `CoordinateTester` may use the complete public BRK+KSK view and fresh randomness
for every coordinate.  `assemble` runs all tests and returns a scalar-key candidate.

The main theorem is an unconditional finite union bound: if coordinate `i` fails with probability
at most `ε i`, then the assembled solver recovers the entire scalar key with probability at least
`1 - ∑ i, ε i`.  No independence between the public view and the coordinate events is assumed.
`CoordinateSecretReduction.toScalarSecretReduction` packages this result into the scalar-only
boundary consumed by KSK completion.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery

/-- A randomized test for one coordinate of the hidden native scalar key. -/
abbrev CoordinateTester
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  Fin lweDimension →
    Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q degree ringRank lweDimension keySwitchLevels → ProbComp Bool

/-- Public context shared by all scalar-coordinate checks. -/
abbrev PublicContext
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  Challenge q degree ringRank tgswLevels lweDimension ×
    Auxiliary q degree ringRank lweDimension keySwitchLevels

/-- A candidate-dependent public check for one scalar coordinate.  A concrete search-to-decision
reduction builds this by transforming the supplied BRK+KSK view and invoking its distinguisher. -/
abbrev CandidateCheck
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  Fin lweDimension → Bool →
    Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q degree ringRank lweDimension keySwitchLevels → ProbComp Bool

/-- One unamplified candidate guess as a function of the fixed public context. -/
def candidateGuess
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels → ProbComp Bool :=
  fun context =>
    FormalProof4FHE.BinaryGuessCheck.tester (orientation coordinate)
      (fun candidate context => check coordinate candidate context.1 context.2) context

/-- Turn candidate-dependent checks into executable coordinate testers. -/
def testerOfCheck
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun coordinate challenge auxiliary =>
    candidateGuess orientation check coordinate (challenge, auxiliary)

/-- Repeat a candidate tester through an iterated majority-of-three tree after fixing the public
BRK+KSK context.  Coordinate `i` executes `3 ^ rounds i` fresh base guesses. -/
def amplifiedTesterOfCheck
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (rounds : Fin lweDimension → ℕ)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun coordinate challenge auxiliary =>
    FormalProof4FHE.MajorityAmplification.amplify (rounds coordinate)
      (candidateGuess orientation check coordinate)
      (challenge, auxiliary)

/-- Run every coordinate test independently after fixing the common public BRK+KSK view. -/
def assemble
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    ScalarSolver q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun challenge auxiliary =>
    Fin.mOfFn lweDimension fun coordinate => tester coordinate challenge auxiliary

/-- Joint experiment exposing the hidden scalar key and the candidate assembled from all
coordinate tests.  It is used only to state and prove the recovery bound. -/
noncomputable def jointGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    ProbComp (BinarySecret lweDimension × BinarySecret lweDimension) := do
  let secrets ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleSecret
  let challenge ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleChallenge secrets
  let auxiliary ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary secrets
  let candidate ← assemble tester challenge auxiliary
  return (secrets.1, candidate)

/-- Standalone correctness game for one coordinate test in the same real BRK+KSK experiment. -/
noncomputable def coordinateGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) : ProbComp Bool := do
  let secrets ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleSecret
  let challenge ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleChallenge secrets
  let auxiliary ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary secrets
  let candidate ← tester coordinate challenge auxiliary
  return decide (candidate = secrets.1 coordinate)

/-- The hidden scalar bit paired with its complete correlated public BRK+KSK context. -/
noncomputable def coordinateSource
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (Bool × PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
  let secrets ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleSecret
  let challenge ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleChallenge secrets
  let auxiliary ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary secrets
  return (secrets.1 coordinate, challenge, auxiliary)

/-- Native candidate-check acceptance gap for one scalar coordinate. -/
noncomputable def candidateCheckGap
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) : ℝ :=
  FormalProof4FHE.BinaryGuessCheck.orientedGap
    (coordinateSource ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget coordinate)
    (orientation coordinate)
    (fun candidate context => check coordinate candidate context.1 context.2)

/-- Correct-versus-wrong candidate gap after fixing one hidden bit and its complete public
context.  This conditional quantity, rather than its average over `coordinateSource`, is what
sound shared-context amplification requires. -/
noncomputable def pointwiseCandidateCheckGap
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension)
    (hiddenAndContext : Bool ×
      PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) : ℝ :=
  FormalProof4FHE.BinaryGuessCheck.orientedGap
    (pure hiddenAndContext) (orientation coordinate)
    (fun candidate context => check coordinate candidate context.1 context.2)

/-- Exact conditional failure of one candidate guess at a fixed source point. -/
theorem pointwiseCandidateFailureProbability_eq_ofReal
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension)
    (hiddenAndContext : Bool ×
      PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    Pr[= false |
      FormalProof4FHE.MajorityAmplification.correctness hiddenAndContext.1
        (candidateGuess orientation check coordinate hiddenAndContext.2)] =
      ENNReal.ofReal ((1 - pointwiseCandidateCheckGap orientation check coordinate
        hiddenAndContext) / 2) := by
  simpa [candidateGuess, pointwiseCandidateCheckGap,
    FormalProof4FHE.BinaryGuessCheck.game,
    FormalProof4FHE.MajorityAmplification.correctness, monad_norm] using
    (FormalProof4FHE.BinaryGuessCheck.failureProbability_eq_ofReal
      (pure hiddenAndContext) (orientation coordinate)
      (fun candidate context => check coordinate candidate context.1 context.2))

/-- A public native BRK+KSK decision distinguisher. -/
abbrev PublicDistinguisher
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  Challenge q degree ringRank tgswLevels lweDimension →
    Auxiliary q degree ringRank lweDimension keySwitchLevels → ProbComp Bool

/-- The real public decision experiment. -/
noncomputable def realDecisionGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool := do
  let secrets ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleSecret
  let challenge ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleChallenge secrets
  let auxiliary ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary secrets
  distinguisher challenge auxiliary

/-- The uniform-challenge public decision experiment with the same real correlated KSK. -/
noncomputable def uniformDecisionGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool := do
  let secrets ←
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleSecret
  let challenge ←
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleUniform
  let auxiliary ←
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary secrets
  distinguisher challenge auxiliary

/-- Real-versus-uniform decision advantage in the native public experiment. -/
noncomputable def decisionAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  (realDecisionGame ringErrorSampler keySwitchErrorSampler tgswGadget
    keySwitchGadget distinguisher).boolDistAdvantage
  (uniformDecisionGame ringErrorSampler keySwitchErrorSampler tgswGadget
    keySwitchGadget distinguisher)

/-- The complete real public BRK+KSK view before applying a distinguisher. -/
noncomputable def realPublicView
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
  let secrets ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleSecret
  let challenge ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleChallenge secrets
  let auxiliary ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary secrets
  return (challenge, auxiliary)

/-- The uniform-BRK public endpoint with the same real correlated KSK. -/
noncomputable def uniformPublicView
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
  let secrets ←
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleSecret
  let challenge ←
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleUniform
  let auxiliary ←
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleAuxiliary secrets
  return (challenge, auxiliary)

theorem realDecisionGame_eq_bind_realPublicView
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    realDecisionGame ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget distinguisher =
      realPublicView ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget >>=
        fun context => distinguisher context.1 context.2 := by
  simp [realDecisionGame, realPublicView, monad_norm]

theorem uniformDecisionGame_eq_bind_uniformPublicView
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    uniformDecisionGame ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget distinguisher =
      uniformPublicView ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget >>=
        fun context => distinguisher context.1 context.2 := by
  simp [uniformDecisionGame, uniformPublicView, monad_norm]

/-- The averaged check experiment obtained by submitting the true scalar bit. -/
noncomputable def correctCandidateCheckGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) : ProbComp Bool :=
  FormalProof4FHE.BinaryGuessCheck.correctCheck
    (coordinateSource ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget coordinate)
    (fun candidate context => check coordinate candidate context.1 context.2)

/-- The averaged check experiment obtained by submitting the opposite scalar bit. -/
noncomputable def wrongCandidateCheckGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) : ProbComp Bool :=
  FormalProof4FHE.BinaryGuessCheck.wrongCheck
    (coordinateSource ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget coordinate)
    (fun candidate context => check coordinate candidate context.1 context.2)

/-- Concrete view-law certificate required by the textbook binary guess/check argument.

The true candidate must produce the real decision experiment, while the opposite candidate must
produce the uniform endpoint.  `orientation_le` selects the public distinguisher's sign. -/
structure CandidateCheckViewLaw
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels) : Prop where
  correctLaw : ∀ coordinate,
    evalDist (correctCandidateCheckGame ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget check coordinate) =
      evalDist (realDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher)
  wrongLaw : ∀ coordinate,
    evalDist (wrongCandidateCheckGame ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget check coordinate) =
      evalDist (uniformDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher)
  orientation_le : ∀ coordinate,
    if orientation coordinate then
      (Pr[= true | uniformDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher]).toReal ≤
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher]).toReal
    else
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher]).toReal ≤
      (Pr[= true | uniformDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher]).toReal

/-- Scheme-level shifted-evaluation/smudging contract needed for binary guess-and-check.

The transformer sees only the candidate and the supplied public view.  Averaged over the native
real experiment, the correct candidate must yield the fresh real public-view law, and the wrong
candidate must yield the uniform-BRK endpoint. -/
structure CandidateViewTransformer
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  transform : Fin lweDimension → Bool →
    Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q degree ringRank lweDimension keySwitchLevels →
        ProbComp (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels)
  correctLaw : ∀ coordinate,
    evalDist (do
      let hiddenAndContext ← coordinateSource ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget coordinate
      transform coordinate hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2) =
      evalDist (realPublicView ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget)
  wrongLaw : ∀ coordinate,
    evalDist (do
      let hiddenAndContext ← coordinateSource ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget coordinate
      transform coordinate (!hiddenAndContext.1) hiddenAndContext.2.1 hiddenAndContext.2.2) =
      evalDist (uniformPublicView ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget)

namespace CandidateViewTransformer

/-- Postcompose a candidate view transformer with a public decision distinguisher. -/
def toCheck
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {ringErrorSampler : ProbComp (RLWE.Rq q degree)}
    {keySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : CandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun coordinate candidate challenge auxiliary => do
    let transformed ← transformer.transform coordinate candidate challenge auxiliary
    distinguisher transformed.1 transformed.2

/-- Canonical sign of a decision distinguisher, used only as one bit of nonuniform reduction
advice. -/
noncomputable def orientation
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : Bool :=
  if (Pr[= true | uniformDecisionGame ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget distinguisher]).toReal ≤
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher]).toReal then true else false

theorem orientation_le
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    if orientation ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget distinguisher then
      (Pr[= true | uniformDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher]).toReal ≤
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher]).toReal
    else
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher]).toReal ≤
      (Pr[= true | uniformDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher]).toReal := by
  unfold orientation
  split
  · assumption
  · exact le_of_not_ge ‹_›

/-- A candidate view transformer supplies the exact candidate-check laws for every public
distinguisher. -/
theorem toCheck_viewLaw
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {ringErrorSampler : ProbComp (RLWE.Rq q degree)}
    {keySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : CandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    CandidateCheckViewLaw ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      distinguisher
      (fun _ => orientation ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget distinguisher)
      (transformer.toCheck distinguisher) where
  correctLaw := by
    intro coordinate
    unfold correctCandidateCheckGame FormalProof4FHE.BinaryGuessCheck.correctCheck toCheck
    rw [← bind_assoc]
    rw [evalDist_bind, transformer.correctLaw coordinate, ← evalDist_bind,
      ← realDecisionGame_eq_bind_realPublicView]
  wrongLaw := by
    intro coordinate
    unfold wrongCandidateCheckGame FormalProof4FHE.BinaryGuessCheck.wrongCheck toCheck
    rw [← bind_assoc]
    rw [evalDist_bind, transformer.wrongLaw coordinate, ← evalDist_bind,
      ← uniformDecisionGame_eq_bind_uniformPublicView]
  orientation_le := fun _ => orientation_le ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget distinguisher

end CandidateViewTransformer

/-- Under the exact correct/incorrect view laws, every coordinate check gap equals the original
public decision advantage. -/
theorem candidateCheckGap_eq_decisionAdvantage_of_viewLaw
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (law : CandidateCheckViewLaw ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget distinguisher orientation check)
    (coordinate : Fin lweDimension) :
    candidateCheckGap ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        orientation check coordinate =
      decisionAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget distinguisher := by
  unfold candidateCheckGap FormalProof4FHE.BinaryGuessCheck.orientedGap
  rw [show FormalProof4FHE.BinaryGuessCheck.correctCheck
      (coordinateSource ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate)
      (fun candidate context => check coordinate candidate context.1 context.2) =
      correctCandidateCheckGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget check coordinate from rfl]
  rw [show FormalProof4FHE.BinaryGuessCheck.wrongCheck
      (coordinateSource ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate)
      (fun candidate context => check coordinate candidate context.1 context.2) =
      wrongCandidateCheckGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget check coordinate from rfl]
  rw [probOutput_congr rfl (law.correctLaw coordinate),
    probOutput_congr rfl (law.wrongLaw coordinate)]
  unfold decisionAdvantage ProbComp.boolDistAdvantage
  by_cases horientation : orientation coordinate = true
  · have hle := law.orientation_le coordinate
    rw [if_pos horientation] at hle ⊢
    have hnonneg : (0 : ℝ) ≤
        (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget distinguisher]).toReal -
        (Pr[= true | uniformDecisionGame ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget distinguisher]).toReal := sub_nonneg.mpr hle
    rw [abs_of_nonneg hnonneg]
  · have hle := law.orientation_le coordinate
    rw [if_neg horientation] at hle ⊢
    have hnonpos :
        (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget distinguisher]).toReal -
        (Pr[= true | uniformDecisionGame ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget distinguisher]).toReal ≤ (0 : ℝ) := sub_nonpos.mpr hle
    rw [abs_of_nonpos hnonpos]
    ring

/-- A scheme-level candidate-view transformer makes the oriented candidate-check gap exactly the
original real-versus-uniform decision advantage. -/
theorem candidateViewTransformer_gap_eq_decisionAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (transformer : CandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    candidateCheckGap ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (fun _ => CandidateViewTransformer.orientation ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget distinguisher)
        (transformer.toCheck distinguisher) coordinate =
      decisionAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget distinguisher :=
  candidateCheckGap_eq_decisionAdvantage_of_viewLaw ringErrorSampler
    keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher
    (fun _ => CandidateViewTransformer.orientation ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget distinguisher)
    (transformer.toCheck distinguisher) (transformer.toCheck_viewLaw distinguisher) coordinate

/-- The native coordinate game of `testerOfCheck` is definitionally the generic correlated-context
binary guess-and-check game. -/
theorem coordinateGame_testerOfCheck_eq
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (testerOfCheck orientation check) coordinate =
      FormalProof4FHE.BinaryGuessCheck.game
        (coordinateSource ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget coordinate)
        (orientation coordinate)
        (fun candidate context => check coordinate candidate context.1 context.2) := by
  simp [coordinateGame, coordinateSource, candidateGuess,
    FormalProof4FHE.BinaryGuessCheck.game, testerOfCheck, monad_norm]

/-- The amplified native coordinate game is exactly the generic shared-context recovery game.
The native source is sampled once; only the candidate guess is repeated. -/
theorem coordinateGame_amplifiedTesterOfCheck_eq
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : Fin lweDimension → ℕ)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (amplifiedTesterOfCheck rounds orientation check) coordinate =
      FormalProof4FHE.MajorityAmplification.recoveryGame
        (coordinateSource ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget coordinate)
        (FormalProof4FHE.MajorityAmplification.amplify (rounds coordinate)
          (candidateGuess orientation check coordinate)) := by
  simp [coordinateGame, coordinateSource, amplifiedTesterOfCheck,
    FormalProof4FHE.MajorityAmplification.recoveryGame,
    FormalProof4FHE.MajorityAmplification.correctness, monad_norm]

/-- A support-wise conditional base error amplifies soundly even though all repetitions share the
same native BRK+KSK context. -/
theorem coordinateGame_amplifiedTesterOfCheck_failureProbability_le
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : Fin lweDimension → ℕ)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) (baseError : ENNReal)
    (hbaseError_one : baseError ≤ 1)
    (hbaseError : ∀ hiddenAndContext ∈ support
      (coordinateSource ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate),
      Pr[= false |
        FormalProof4FHE.MajorityAmplification.correctness hiddenAndContext.1
          (candidateGuess orientation check coordinate hiddenAndContext.2)] ≤ baseError) :
    Pr[= false |
      coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (amplifiedTesterOfCheck rounds orientation check) coordinate] ≤
      FormalProof4FHE.MajorityAmplification.amplifiedError
        (rounds coordinate) baseError := by
  rw [coordinateGame_amplifiedTesterOfCheck_eq]
  exact FormalProof4FHE.MajorityAmplification.recoveryGame_amplify_failure_le
    (coordinateSource ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget coordinate)
    (candidateGuess orientation check coordinate) (rounds coordinate) baseError
    hbaseError_one hbaseError

/-- A uniform pointwise lower bound on the signed candidate gap yields the exact iterated-majority
coordinate error bound.  This is the strengthened hypothesis needed for sound shared-context
amplification; the averaged `candidateCheckGap` alone is insufficient. -/
theorem coordinateGame_amplifiedTesterOfCheck_failureProbability_le_of_pointwiseGap
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : Fin lweDimension → ℕ)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) (gapLowerBound : ℝ)
    (hgap_nonneg : 0 ≤ gapLowerBound)
    (hgap : ∀ hiddenAndContext ∈ support
      (coordinateSource ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate),
      gapLowerBound ≤
        pointwiseCandidateCheckGap orientation check coordinate hiddenAndContext) :
    Pr[= false |
      coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (amplifiedTesterOfCheck rounds orientation check) coordinate] ≤
      FormalProof4FHE.MajorityAmplification.amplifiedError (rounds coordinate)
        (ENNReal.ofReal ((1 - gapLowerBound) / 2)) := by
  apply coordinateGame_amplifiedTesterOfCheck_failureProbability_le
  · exact ENNReal.ofReal_le_one.mpr (by linarith)
  · intro hiddenAndContext hsupport
    rw [pointwiseCandidateFailureProbability_eq_ofReal]
    apply ENNReal.ofReal_le_ofReal
    linarith [hgap hiddenAndContext hsupport]

/-- Exact real-valued coordinate failure in terms of the correct-versus-wrong candidate check
gap. -/
theorem coordinateGame_testerOfCheck_failureProbability
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    (Pr[= false |
      coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (testerOfCheck orientation check) coordinate]).toReal =
      (1 - candidateCheckGap ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget orientation check coordinate) / 2 := by
  rw [coordinateGame_testerOfCheck_eq]
  exact FormalProof4FHE.BinaryGuessCheck.failureProbability_eq_half_sub_orientedGap _ _ _

/-- If correct and wrong candidates reproduce the real and uniform decision endpoints, one-shot
coordinate failure is exactly `(1 - decisionAdvantage) / 2`. -/
theorem coordinateGame_testerOfCheck_failureProbability_of_viewLaw
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (law : CandidateCheckViewLaw ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget distinguisher orientation check)
    (coordinate : Fin lweDimension) :
    (Pr[= false |
      coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (testerOfCheck orientation check) coordinate]).toReal =
      (1 - decisionAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget distinguisher) / 2 := by
  rw [coordinateGame_testerOfCheck_failureProbability,
    candidateCheckGap_eq_decisionAdvantage_of_viewLaw ringErrorSampler
      keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher orientation check law]

/-- Exact one-shot coordinate error supplied by a scheme-level candidate-view transformer.  This
is deliberately a one-run theorem; amplification is a separate reduction obligation. -/
theorem coordinateGame_candidateViewTransformer_failureProbability
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (transformer : CandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    (Pr[= false |
      coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (testerOfCheck
          (fun _ => CandidateViewTransformer.orientation ringErrorSampler
            keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
          (transformer.toCheck distinguisher)) coordinate]).toReal =
      (1 - decisionAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget distinguisher) / 2 :=
  coordinateGame_testerOfCheck_failureProbability_of_viewLaw ringErrorSampler
    keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher
    (fun _ => CandidateViewTransformer.orientation ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget distinguisher)
    (transformer.toCheck distinguisher) (transformer.toCheck_viewLaw distinguisher) coordinate

/-- ENNReal form of the exact coordinate failure formula. -/
theorem coordinateGame_testerOfCheck_failureProbability_eq_ofReal
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    Pr[= false |
      coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (testerOfCheck orientation check) coordinate] =
      ENNReal.ofReal ((1 - candidateCheckGap ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget orientation check coordinate) / 2) := by
  calc
    _ = ENNReal.ofReal
        (Pr[= false |
          coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
            (testerOfCheck orientation check) coordinate]).toReal :=
      (ENNReal.ofReal_toReal probOutput_ne_top).symm
    _ = _ := congrArg ENNReal.ofReal
      (coordinateGame_testerOfCheck_failureProbability ringErrorSampler
        keySwitchErrorSampler tgswGadget keySwitchGadget orientation check coordinate)

/-- Sound shared-context amplification from an averaged one-shot coordinate error.  The explicit
`averageError / threshold` term is the price of bad fixed public contexts; unlike the pointwise
theorem above, no conditional-gap premise is assumed. -/
theorem coordinateGame_amplifiedTesterOfCheck_failureProbability_le_of_average
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : Fin lweDimension → ℕ)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) (threshold averageError : ENNReal)
    (hthreshold_pos : 0 < threshold) (hthreshold_one : threshold ≤ 1)
    (haverage :
      Pr[= false |
        coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          (testerOfCheck orientation check) coordinate] ≤ averageError) :
    Pr[= false |
      coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (amplifiedTesterOfCheck rounds orientation check) coordinate] ≤
      FormalProof4FHE.MajorityAmplification.amplifiedError
          (rounds coordinate) threshold + averageError / threshold := by
  rw [coordinateGame_amplifiedTesterOfCheck_eq]
  apply FormalProof4FHE.MajorityAmplification.recoveryGame_amplify_failure_le_of_average
    (coordinateSource ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget coordinate)
    (candidateGuess orientation check coordinate) (rounds coordinate)
    threshold averageError hthreshold_pos hthreshold_one
  simpa [FormalProof4FHE.MajorityAmplification.recoveryGame,
    FormalProof4FHE.MajorityAmplification.correctness,
    coordinateGame, coordinateSource, candidateGuess, testerOfCheck, monad_norm] using haverage

/-- An averaged native candidate-view law therefore supports only thresholded amplification.
This theorem is deliberately quantitative about the bad-context term; it does not silently treat
the averaged decision advantage as a pointwise conditional gap. -/
theorem coordinateGame_amplifiedCandidateViewTransformer_failureProbability_le_threshold
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (transformer : CandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (rounds : Fin lweDimension → ℕ) (coordinate : Fin lweDimension)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1) :
    Pr[= false |
      coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (amplifiedTesterOfCheck rounds
          (fun _ ↦ CandidateViewTransformer.orientation ringErrorSampler
            keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
          (transformer.toCheck distinguisher)) coordinate] ≤
      FormalProof4FHE.MajorityAmplification.amplifiedError
          (rounds coordinate) threshold +
        ENNReal.ofReal ((1 - decisionAdvantage ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget distinguisher) / 2) / threshold := by
  apply coordinateGame_amplifiedTesterOfCheck_failureProbability_le_of_average
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget rounds
    (fun _ ↦ CandidateViewTransformer.orientation ringErrorSampler
      keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
    (transformer.toCheck distinguisher) coordinate threshold
    (ENNReal.ofReal ((1 - decisionAdvantage ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget distinguisher) / 2))
    hthreshold_pos hthreshold_one
  rw [coordinateGame_testerOfCheck_failureProbability_eq_ofReal]
  rw [candidateViewTransformer_gap_eq_decisionAdvantage]

/-- A lower bound on the oriented correct-versus-wrong check gap gives an explicit upper bound on
coordinate failure. -/
theorem coordinateGame_testerOfCheck_failureProbability_le_of_gap
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) (gapLowerBound : ℝ)
    (hgap : gapLowerBound ≤
      candidateCheckGap ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget orientation check coordinate) :
    Pr[= false |
      coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (testerOfCheck orientation check) coordinate] ≤
      ENNReal.ofReal ((1 - gapLowerBound) / 2) := by
  rw [coordinateGame_testerOfCheck_failureProbability_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  linarith

/-- Failure probability of one coordinate inside the common-view joint experiment. -/
noncomputable def coordinateFailureProbability
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) : ENNReal :=
  Pr[(fun output => output.2 coordinate ≠ output.1 coordinate) |
    jointGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget tester]

/-- Projecting the assembled joint experiment to one correctness bit gives exactly the standalone
coordinate game. -/
theorem evalDist_map_jointGame_coordinate_eq_coordinateGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    evalDist
        ((fun output => decide (output.2 coordinate = output.1 coordinate)) <$>
          jointGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget tester) =
      evalDist
        (coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          tester coordinate) := by
  simp only [jointGame, coordinateGame, assemble, map_eq_bind_pure_comp, bind_assoc]
  apply evalDist_bind_congr'
  intro secrets
  apply evalDist_bind_congr'
  intro challenge
  apply evalDist_bind_congr'
  intro auxiliary
  simp only [pure_bind, Function.comp_apply]
  have h := FormalProof4FHE.FiniteProduct.evalDist_map_fin_mOfFn_apply lweDimension
    (fun index => tester index challenge auxiliary) coordinate
    (fun candidate => decide (candidate = secrets.1 coordinate))
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp] at h
  simpa only [Function.comp_def] using h

/-- The coordinate error used by the union bound is exactly failure in the corresponding
standalone coordinate game. -/
theorem coordinateFailureProbability_eq_probOutput_false_coordinateGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    coordinateFailureProbability ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget tester coordinate =
      Pr[= false |
        coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          tester coordinate] := by
  rw [coordinateFailureProbability]
  calc
    _ = Pr[= false |
        (fun output => decide (output.2 coordinate = output.1 coordinate)) <$>
          jointGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget tester] := by
      rw [probOutput_map]
      congr 1
      funext output
      simp
    _ = _ := probOutput_congr rfl
      (evalDist_map_jointGame_coordinate_eq_coordinateGame ringErrorSampler
        keySwitchErrorSampler tgswGadget keySwitchGadget tester coordinate)

/-- The scalar success game for an assembled tester is the equality event in `jointGame`. -/
theorem scalarGame_assemble_eq_map_jointGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    scalarGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (assemble tester) =
      (fun output => decide (output.2 = output.1)) <$>
        jointGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget tester := by
  simp [scalarGame, jointGame, assemble, map_eq_bind_pure_comp, monad_norm]

/-- Whole-key failure is contained in the union of the coordinate-failure events. -/
theorem wholeKeyFailure_le_sum_coordinateFailure
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    Pr[(fun output => output.2 ≠ output.1) |
        jointGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget tester] ≤
      ∑ coordinate,
        coordinateFailureProbability ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget tester coordinate := by
  classical
  let experiment :=
    jointGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget tester
  have hevent :
      (fun output : BinarySecret lweDimension × BinarySecret lweDimension =>
        output.2 ≠ output.1) =
      (fun output => ∃ coordinate ∈ (Finset.univ : Finset (Fin lweDimension)),
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
  rw [show jointGame ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget tester = experiment from rfl, hevent]
  simpa [coordinateFailureProbability, experiment] using
    (probEvent_exists_finset_le_sum (Finset.univ : Finset (Fin lweDimension))
      experiment
      (fun coordinate output => output.2 coordinate ≠ output.1 coordinate))

/-- **Coordinate-to-scalar recovery.** Pointwise error bounds assemble by a finite union bound
into an exact-key recovery lower bound. -/
theorem one_sub_sum_coordinateError_le_scalarSuccess
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (error : Fin lweDimension → ENNReal)
    (hcoordinate : ∀ coordinate,
      coordinateFailureProbability ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget tester coordinate ≤ error coordinate) :
    1 - ∑ coordinate, error coordinate ≤
      Pr[= true |
        scalarGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          (assemble tester)] := by
  classical
  let experiment :=
    jointGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget tester
  have hfailure :
      Pr[(fun output => output.2 ≠ output.1) | experiment] ≤
        ∑ coordinate, error coordinate := by
    exact (wholeKeyFailure_le_sum_coordinateFailure ringErrorSampler
      keySwitchErrorSampler tgswGadget keySwitchGadget tester).trans
        (Finset.sum_le_sum fun coordinate _ => hcoordinate coordinate)
  have hsuccess :
      1 - ∑ coordinate, error coordinate ≤
        Pr[(fun output => output.2 = output.1) | experiment] :=
    probEvent_one_sub_le_of_compl_le probFailure_eq_zero hfailure
  rw [scalarGame_assemble_eq_map_jointGame, probOutput_map]
  simpa only [decide_eq_true_eq, experiment] using hsuccess

/-- Standalone per-coordinate game bounds imply the same assembled scalar-key success bound. -/
theorem one_sub_sum_coordinateGameError_le_scalarSuccess
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (tester : CoordinateTester q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (error : Fin lweDimension → ENNReal)
    (hcoordinate : ∀ coordinate,
      Pr[= false |
        coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          tester coordinate] ≤ error coordinate) :
    1 - ∑ coordinate, error coordinate ≤
      Pr[= true |
        scalarGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          (assemble tester)] := by
  apply one_sub_sum_coordinateError_le_scalarSuccess ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget tester error
  intro coordinate
  rw [coordinateFailureProbability_eq_probOutput_false_coordinateGame]
  exact hcoordinate coordinate

/-- Candidate-check gap bounds for every coordinate assemble into a whole scalar-key recovery
bound. -/
theorem one_sub_sum_gapError_le_scalarSuccess
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (orientation : Fin lweDimension → Bool)
    (check : CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (gapLowerBound : Fin lweDimension → ℝ)
    (hgap : ∀ coordinate, gapLowerBound coordinate ≤
      candidateCheckGap ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget orientation check coordinate) :
    1 - ∑ coordinate, ENNReal.ofReal ((1 - gapLowerBound coordinate) / 2) ≤
      Pr[= true |
        scalarGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          (assemble (testerOfCheck orientation check))] := by
  apply one_sub_sum_coordinateGameError_le_scalarSuccess ringErrorSampler
    keySwitchErrorSampler tgswGadget keySwitchGadget (testerOfCheck orientation check)
    (fun coordinate => ENNReal.ofReal ((1 - gapLowerBound coordinate) / 2))
  intro coordinate
  exact coordinateGame_testerOfCheck_failureProbability_le_of_gap ringErrorSampler
    keySwitchErrorSampler tgswGadget keySwitchGadget orientation check coordinate
    (gapLowerBound coordinate) (hgap coordinate)

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery
