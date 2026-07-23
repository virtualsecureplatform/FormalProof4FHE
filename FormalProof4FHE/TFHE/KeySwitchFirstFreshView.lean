/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.KeySwitchFirstSearchToDecision

/-!
# Fresh-View Amplification for the KSK-First TFHE Reduction

The one-shot KSK-first reduction receives one fixed BRK+KSK context.  Repeating candidate tests
against that same context cannot amplify an averaged decision gap without a large bad-context
term.  This module isolates the stronger sampling model used by standard search-to-decision
arguments: a solver receives an opaque handle that returns independently sampled native public
views under one fixed hidden key pair.

The concrete solver queries a fresh view for every leaf of every majority tree.  Conditional on
the hidden key pair, the fixed-secret correct/wrong KSK laws make every scalar coordinate have the
same base error.  The whole-vector amplification theorem therefore charges the bad hidden-key
fiber once, not once per coordinate.

This is a genuine strengthening of the search premise.  It does not identify fresh-view search
hardness with single-evaluation-key search hardness or ordinary LWE/RLWE; those are separate
reduction obligations.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstFreshView

open KeySwitchFirstCandidateView

/-- An opaque sampling handle for fresh public views.  The reduction can query the handle but its
solver interface does not receive either hidden key. -/
structure ViewOracle (View : Type) where
  private mk ::
  private sampler : ProbComp View

namespace ViewOracle

/-- Obtain one independent draw from the public-view sampler represented by the handle. -/
def query {View : Type} (oracle : ViewOracle View) : ProbComp View :=
  oracle.sampler

/-- Construct a handle inside the defining security experiment. -/
private def ofSampler {View : Type} (sampler : ProbComp View) : ViewOracle View :=
  ⟨sampler⟩

end ViewOracle

/-- Fresh-view handle for the complete native BRK+KSK context. -/
abbrev Oracle
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  ViewOracle
    (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels)

/-- Fixed-secret real public view used by one oracle query. -/
noncomputable def fixedSecretView
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree) :
    ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) :=
  Search.fixedSecretRealView q degree ringRank tgswLevels lweDimension
    keySwitchLevels ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget secrets

/-- The executable centered-binomial fresh-view sampler never fails. -/
@[simp] theorem probFailure_fixedSecretView_centeredBinomial
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree) :
    Pr[⊥ |
      fixedSecretView (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget secrets] = 0 := by
  simp [fixedSecretView, Search.fixedSecretRealView, AuxiliaryInput.problem,
    RLWE.CenteredBinomial.sampler, CenteredBinomial.scalarSampler]

/-- Build the fresh-view handle associated with one fixed native key pair.  Constructing this
handle requires the hidden pair; the public solver interface still receives only the handle. -/
noncomputable def oracleOfSecrets
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree) :
    Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  ViewOracle.ofSampler
    (fixedSecretView ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget secrets)

/-- Querying the native handle is exactly fixed-secret public-view sampling. -/
@[simp] theorem query_oracleOfSecrets
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree) :
    (oracleOfSecrets ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget secrets).query =
        fixedSecretView ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget secrets := rfl

/-- Hidden scalar vector paired with an opaque fresh-view handle for the same complete key pair. -/
noncomputable def scalarSource
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp
      (BinarySecret lweDimension ×
        Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
  let secrets ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleSecret
  return (secrets.1, oracleOfSecrets ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget secrets)

/-- Fixed-secret real decision experiment. -/
noncomputable def fixedRealDecisionGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool := do
  let context ← fixedSecretView ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget secrets
  distinguisher context.1 context.2

/-- Fixed-secret real-BRK/uniform-KSK decision experiment. -/
noncomputable def fixedUniformKeySwitchDecisionGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool := do
  let challenge ← MonomialKDM.generateBootstrappingKey
    q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
    secrets.1 secrets.2
  let auxiliary ← $ᵗ (Auxiliary q degree ringRank lweDimension keySwitchLevels)
  distinguisher challenge auxiliary

/-- The fixed-secret signed decision gap, using the global orientation advice. -/
noncomputable def fixedOrientedGap
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  if KeySwitchFirstCandidateView.orientation ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget distinguisher then
    (Pr[= true | fixedRealDecisionGame ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget secrets distinguisher]).toReal -
    (Pr[= true | fixedUniformKeySwitchDecisionGame ringErrorSampler
      tgswGadget secrets distinguisher]).toReal
  else
    (Pr[= true | fixedUniformKeySwitchDecisionGame ringErrorSampler
      tgswGadget secrets distinguisher]).toReal -
    (Pr[= true | fixedRealDecisionGame ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget secrets distinguisher]).toReal

/-- One fresh-view candidate guess for a scalar coordinate. -/
noncomputable def coordinateGuess
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension)
    (oracle : Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    ProbComp Bool := do
  let context ← oracle.query
  candidateGuess
    (fun _ ↦ KeySwitchFirstCandidateView.orientation ringErrorSampler
      keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
    (KeySwitchFirstCandidateView.toCandidateCheck distinguisher)
    coordinate context

/-! ## Fixed-secret coordinate law -/

/-- One fixed hidden scalar bit paired with a freshly sampled real public view under the complete
fixed native key pair. -/
noncomputable def fixedCoordinateSource
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree)
    (coordinate : Fin lweDimension) :
    ProbComp
      (Bool × PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
  let context ← fixedSecretView ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget secrets
  return (secrets.1 coordinate, context)

/-- At fixed native secrets, the correct candidate preserves the fresh real public view. -/
theorem fixedCoordinateSource_randomize_correct_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree)
    (coordinate : Fin lweDimension) :
    evalDist (do
      let hiddenAndContext ← fixedCoordinateSource ringErrorSampler
        keySwitchErrorSampler tgswGadget keySwitchGadget secrets coordinate
      KeySwitchFirstCandidateView.randomizeContext coordinate hiddenAndContext.1
        hiddenAndContext.2.1 hiddenAndContext.2.2) =
      evalDist (fixedSecretView ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget secrets) := by
  simp only [fixedCoordinateSource, fixedSecretView, Search.fixedSecretRealView,
    AuxiliaryInput.problem]
  simp only [bind_assoc, pure_bind]
  exact KeySwitchFirstCandidateView.randomize_generatedPair_correct_evalDist
    (MonomialKDM.generateBootstrappingKey
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
      secrets.1 secrets.2)
    keySwitchErrorSampler keySwitchGadget secrets.1 secrets.2 coordinate

/-- At fixed native secrets, the wrong candidate makes the KSK uniformly random while preserving
the independently sampled real BRK. -/
theorem fixedCoordinateSource_randomize_wrong_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree)
    (coordinate : Fin lweDimension) :
    evalDist (do
      let hiddenAndContext ← fixedCoordinateSource ringErrorSampler
        keySwitchErrorSampler tgswGadget keySwitchGadget secrets coordinate
      KeySwitchFirstCandidateView.randomizeContext coordinate (!hiddenAndContext.1)
        hiddenAndContext.2.1 hiddenAndContext.2.2) =
      evalDist (do
        let challenge ← MonomialKDM.generateBootstrappingKey
          q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
          secrets.1 secrets.2
        let auxiliary ← $ᵗ (Auxiliary q degree ringRank lweDimension keySwitchLevels)
        return (challenge, auxiliary)) := by
  simp only [fixedCoordinateSource, fixedSecretView, Search.fixedSecretRealView,
    AuxiliaryInput.problem]
  simp only [bind_assoc, pure_bind]
  exact KeySwitchFirstCandidateView.randomize_generatedPair_wrong_evalDist
    (MonomialKDM.generateBootstrappingKey
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
      secrets.1 secrets.2)
    keySwitchErrorSampler hError keySwitchGadget secrets.1 secrets.2 coordinate
    (!(secrets.1 coordinate)) (by simp)

/-- Correct-candidate checking at fixed secrets is exactly the fixed real decision experiment. -/
theorem fixedCorrectCheck_evalDist_eq_fixedRealDecisionGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    evalDist
        (FormalProof4FHE.BinaryGuessCheck.correctCheck
          (fixedCoordinateSource ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget secrets coordinate)
          (fun candidate context ↦
            KeySwitchFirstCandidateView.toCandidateCheck distinguisher
              coordinate candidate context.1 context.2)) =
      evalDist (fixedRealDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget secrets distinguisher) := by
  unfold FormalProof4FHE.BinaryGuessCheck.correctCheck
    KeySwitchFirstCandidateView.toCandidateCheck fixedRealDecisionGame
  rw [← bind_assoc]
  rw [evalDist_bind,
    fixedCoordinateSource_randomize_correct_evalDist ringErrorSampler
      keySwitchErrorSampler tgswGadget keySwitchGadget secrets coordinate,
    ← evalDist_bind]

/-- Wrong-candidate checking at fixed secrets is exactly the fixed
real-BRK/uniform-KSK decision experiment. -/
theorem fixedWrongCheck_evalDist_eq_fixedUniformKeySwitchDecisionGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    evalDist
        (FormalProof4FHE.BinaryGuessCheck.wrongCheck
          (fixedCoordinateSource ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget secrets coordinate)
          (fun candidate context ↦
            KeySwitchFirstCandidateView.toCandidateCheck distinguisher
              coordinate candidate context.1 context.2)) =
      evalDist (fixedUniformKeySwitchDecisionGame ringErrorSampler
        tgswGadget secrets distinguisher) := by
  unfold FormalProof4FHE.BinaryGuessCheck.wrongCheck
    KeySwitchFirstCandidateView.toCandidateCheck
    fixedUniformKeySwitchDecisionGame
  rw [← bind_assoc]
  rw [evalDist_bind,
    fixedCoordinateSource_randomize_wrong_evalDist ringErrorSampler
      keySwitchErrorSampler hError tgswGadget keySwitchGadget secrets coordinate,
    ← evalDist_bind]
  simp [bind_assoc]

/-- The fixed-secret candidate gap is independent of the selected scalar coordinate. -/
theorem fixedCandidateGap_eq_fixedOrientedGap
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    FormalProof4FHE.BinaryGuessCheck.orientedGap
        (fixedCoordinateSource ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget secrets coordinate)
        (KeySwitchFirstCandidateView.orientation ringErrorSampler
          keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
        (fun candidate context ↦
          KeySwitchFirstCandidateView.toCandidateCheck distinguisher
            coordinate candidate context.1 context.2) =
      fixedOrientedGap ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget secrets distinguisher := by
  unfold FormalProof4FHE.BinaryGuessCheck.orientedGap fixedOrientedGap
  rw [probOutput_congr rfl
      (fixedCorrectCheck_evalDist_eq_fixedRealDecisionGame ringErrorSampler
        keySwitchErrorSampler tgswGadget keySwitchGadget secrets distinguisher coordinate),
    probOutput_congr rfl
      (fixedWrongCheck_evalDist_eq_fixedUniformKeySwitchDecisionGame ringErrorSampler
        keySwitchErrorSampler hError tgswGadget keySwitchGadget secrets
        distinguisher coordinate)]

/-- Conditional one-shot coordinate failure depends only on the hidden key-pair fiber, not on the
coordinate. -/
theorem fixedCoordinateFailureProbability_eq_ofReal
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : AuxiliaryInput.Secret lweDimension ringRank degree)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    Pr[= false |
      FormalProof4FHE.MajorityAmplification.correctness
        (secrets.1 coordinate)
        (coordinateGuess ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget distinguisher coordinate
          (oracleOfSecrets ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget secrets))] =
      ENNReal.ofReal
        ((1 - fixedOrientedGap ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget secrets distinguisher) / 2) := by
  simpa [coordinateGuess, oracleOfSecrets, ViewOracle.query,
      ViewOracle.ofSampler, fixedCoordinateSource,
      candidateGuess,
      FormalProof4FHE.MajorityAmplification.correctness,
      FormalProof4FHE.BinaryGuessCheck.game, monad_norm] using
    (FormalProof4FHE.BinaryGuessCheck.failureProbability_eq_ofReal
      (fixedCoordinateSource ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget secrets coordinate)
      (KeySwitchFirstCandidateView.orientation ringErrorSampler
        keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
      (fun candidate context ↦
        KeySwitchFirstCandidateView.toCandidateCheck distinguisher
          coordinate candidate context.1 context.2)).trans
      (congrArg ENNReal.ofReal
        (congrArg (fun gap : ℝ ↦ (1 - gap) / 2)
          (fixedCandidateGap_eq_fixedOrientedGap ringErrorSampler
            keySwitchErrorSampler hError tgswGadget keySwitchGadget
            secrets distinguisher coordinate)))

/-! ## Common hidden-key-fiber error -/

/-- Conditional one-shot error at a fixed reference coordinate.  On every supported source
fiber, the fixed-secret law proves that this same quantity bounds every coordinate. -/
noncomputable def fiberError
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (reference : Fin lweDimension)
    (hiddenAndOracle : BinarySecret lweDimension ×
      Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels) : ENNReal :=
  Pr[= false |
    FormalProof4FHE.MajorityAmplification.correctness
      (hiddenAndOracle.1 reference)
      (coordinateGuess ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher reference hiddenAndOracle.2)]

/-- Every coordinate has the same conditional base error on a supported fresh-view source
fiber. -/
theorem coordinateFailureProbability_eq_fiberError_of_mem_support
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (reference coordinate : Fin lweDimension)
    (hiddenAndOracle : BinarySecret lweDimension ×
      Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (hsupport : hiddenAndOracle ∈ support
      (scalarSource ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget)) :
    Pr[= false |
      FormalProof4FHE.MajorityAmplification.correctness
        (hiddenAndOracle.1 coordinate)
        (coordinateGuess ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget distinguisher coordinate hiddenAndOracle.2)] =
      fiberError ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher reference hiddenAndOracle := by
  unfold scalarSource at hsupport
  rw [mem_support_bind_iff] at hsupport
  obtain ⟨secrets, _hsecrets, hpure⟩ := hsupport
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst hiddenAndOracle
  unfold fiberError
  rw [fixedCoordinateFailureProbability_eq_ofReal ringErrorSampler
      keySwitchErrorSampler hError tgswGadget keySwitchGadget
      secrets distinguisher coordinate,
    fixedCoordinateFailureProbability_eq_ofReal ringErrorSampler
      keySwitchErrorSampler hError tgswGadget keySwitchGadget
      secrets distinguisher reference]

/-- Averaging the common fiber error gives exactly the global one-shot coordinate error. -/
theorem expectedFiberError_eq_keySwitchDecisionError
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (reference : Fin lweDimension) :
    (∑' hiddenAndOracle,
      Pr[= hiddenAndOracle |
        scalarSource ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget] *
        fiberError ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget distinguisher reference hiddenAndOracle) =
      ENNReal.ofReal
        ((1 - KeySwitchFirstCandidateView.keySwitchDecisionAdvantage
          ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget distinguisher) / 2) := by
  unfold fiberError
  rw [← probOutput_bind_eq_tsum]
  have hgame :
      evalDist (do
        let hiddenAndOracle ← scalarSource ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget
        FormalProof4FHE.MajorityAmplification.correctness
          (hiddenAndOracle.1 reference)
          (coordinateGuess ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget distinguisher reference hiddenAndOracle.2)) =
        evalDist
          (coordinateGame ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget
            (testerOfCheck
              (fun _ ↦ KeySwitchFirstCandidateView.orientation ringErrorSampler
                keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
              (KeySwitchFirstCandidateView.toCandidateCheck distinguisher))
            reference) := by
    simp [scalarSource, oracleOfSecrets, coordinateGuess, ViewOracle.query,
      ViewOracle.ofSampler, fixedSecretView, Search.fixedSecretRealView,
      coordinateGame, Search.problem,
      LWE.AuxiliaryInput.Search.exactRecoveryProblem, AuxiliaryInput.problem,
      candidateGuess, testerOfCheck,
      FormalProof4FHE.MajorityAmplification.correctness, monad_norm]
  rw [probOutput_congr rfl hgame]
  calc
    _ = ENNReal.ofReal
        (Pr[= false |
          coordinateGame ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget
            (testerOfCheck
              (fun _ ↦ KeySwitchFirstCandidateView.orientation ringErrorSampler
                keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
              (KeySwitchFirstCandidateView.toCandidateCheck distinguisher))
            reference]).toReal :=
      (ENNReal.ofReal_toReal probOutput_ne_top).symm
    _ = _ := congrArg ENNReal.ofReal
      (KeySwitchFirstCandidateView.coordinateGame_failureProbability
        ringErrorSampler keySwitchErrorSampler hError tgswGadget
        keySwitchGadget distinguisher reference)

/-! ## Amplified fresh-view scalar recovery -/

/-- A scalar-key solver with query access to independently sampled public views. -/
abbrev ScalarSolver
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels →
    ProbComp (BinarySecret lweDimension)

/-- Run a fresh-view scalar solver and check exact scalar-key recovery. -/
noncomputable def scalarGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : ScalarSolver q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool := do
  let hiddenAndOracle ← scalarSource ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget
  FormalProof4FHE.MajorityAmplification.vectorCorrectness
    hiddenAndOracle.1 (solver hiddenAndOracle.2)

/-- Query one fresh public view for every leaf of every coordinate majority tree. -/
noncomputable def amplifiedScalarSolver
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : Fin lweDimension → ℕ)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    ScalarSolver q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  FormalProof4FHE.MajorityAmplification.amplifyVector rounds
    (coordinateGuess ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget distinguisher)

/-- Whole-scalar-key failure after fresh-view amplification.  The hidden-key bad-fiber term is
charged once, independently of the scalar dimension. -/
theorem amplifiedScalarFailureProbability_le
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : Fin lweDimension → ℕ)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Pr[= false |
      scalarGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget
        (amplifiedScalarSolver ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget rounds distinguisher)] ≤
      (∑ coordinate,
        FormalProof4FHE.MajorityAmplification.amplifiedError
          (rounds coordinate) threshold) +
      ENNReal.ofReal
          ((1 - KeySwitchFirstCandidateView.keySwitchDecisionAdvantage
            ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget distinguisher) / 2) /
        threshold := by
  simpa only [scalarGame, amplifiedScalarSolver,
      FormalProof4FHE.MajorityAmplification.vectorRecoveryGame] using
    (FormalProof4FHE.MajorityAmplification.vectorRecoveryGame_amplify_failure_le_of_common_average
      (scalarSource ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget)
      rounds
      (coordinateGuess ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher)
      (fiberError ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher reference)
      threshold
      (ENNReal.ofReal
        ((1 - KeySwitchFirstCandidateView.keySwitchDecisionAdvantage
          ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget distinguisher) / 2))
      hthreshold_pos hthreshold_one
      (fun hiddenAndOracle hsupport coordinate ↦
        (coordinateFailureProbability_eq_fiberError_of_mem_support
          ringErrorSampler keySwitchErrorSampler hError tgswGadget
          keySwitchGadget distinguisher reference coordinate
          hiddenAndOracle hsupport).le)
      (expectedFiberError_eq_keySwitchDecisionError
        ringErrorSampler keySwitchErrorSampler hError tgswGadget
        keySwitchGadget distinguisher reference).le)

/-- Equivalent scalar-success lower bound. -/
theorem one_sub_freshAmplifiedError_le_scalarSuccess
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : Fin lweDimension → ℕ)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    1 - ((∑ coordinate,
        FormalProof4FHE.MajorityAmplification.amplifiedError
          (rounds coordinate) threshold) +
      ENNReal.ofReal
          ((1 - KeySwitchFirstCandidateView.keySwitchDecisionAdvantage
            ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget distinguisher) / 2) /
        threshold) ≤
      Pr[= true |
        scalarGame ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget
          (amplifiedScalarSolver ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget rounds distinguisher)] := by
  let experiment := scalarGame ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget
    (amplifiedScalarSolver ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget rounds distinguisher)
  have hfailure := amplifiedScalarFailureProbability_le ringErrorSampler
    keySwitchErrorSampler hError tgswGadget keySwitchGadget
    reference rounds threshold hthreshold_pos hthreshold_one distinguisher
  have hsuccess := probEvent_one_sub_le_of_compl_le
    (mx := experiment) (p := fun output : Bool ↦ output = true)
    probFailure_eq_zero (by simpa [experiment] using hfailure)
  simpa [experiment] using hsuccess

/-! ## Centered-binomial paired-key completion -/

/-- A paired-key solver with query access to fresh public views. -/
abbrev Solver
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels →
    ProbComp (AuxiliaryInput.Secret lweDimension ringRank degree)

/-- Complete a fresh-view scalar solver by querying one additional real KSK and applying the
checked centered-binomial ring-key decoder. -/
noncomputable def completeScalarSolver
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (scalarSolver : ScalarSolver q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Solver q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun oracle ↦ do
    let candidate ← scalarSolver oracle
    let context ← oracle.query
    return Native.KeySwitchRecovery.completeCandidate
      keySwitchGadget level context.2 candidate

/-- Exact paired-key recovery game for a fresh-view solver. -/
noncomputable def game
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    ProbComp Bool := do
  let secrets ←
    (Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleSecret
  let recovered ← solver
    (oracleOfSecrets ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget secrets)
  return decide (recovered = secrets)

/-- Centered-binomial KSK decoding completes fresh-view scalar recovery without changing its
success distribution. -/
theorem evalDist_game_completeScalarSolver_eq_scalarGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (scalarSolver : ScalarSolver q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    evalDist
        (game (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget
          (completeScalarSolver keySwitchGadget level scalarSolver)) =
      evalDist
        (scalarGame (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget scalarSolver) := by
  classical
  simp only [game, scalarGame, scalarSource, completeScalarSolver,
    bind_assoc, pure_bind]
  refine evalDist_bind_congr'
    ((Search.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget).sampleSecret) fun secrets ↦ ?_
  refine evalDist_bind_congr'
    (scalarSolver
      (oracleOfSecrets (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget secrets)) fun candidate ↦ ?_
  let viewSampler := fixedSecretView
    (RLWE.CenteredBinomial.sampler q degree ringEta)
    (CenteredBinomial.scalarSampler q keySwitchEta)
    tgswGadget keySwitchGadget secrets
  have hconditional :
      (do
        let context ← viewSampler
        return decide
          (Native.KeySwitchRecovery.completeCandidate
            keySwitchGadget level context.2 candidate = secrets)) =
      (do
        let _context ← viewSampler
        return decide (candidate = secrets.1)) := by
    apply OracleComp.bind_congr_of_forall_mem_support
    intro context hcontext
    change context ∈ support (do
      let challenge ← MonomialKDM.generateBootstrappingKey
        q degree ringRank tgswLevels lweDimension
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        tgswGadget secrets.1 secrets.2
      let keySwitchKey ← Native.generateKeySwitchKey
        q lweDimension (ringRank * degree) keySwitchLevels
        (CenteredBinomial.scalarSampler q keySwitchEta)
        keySwitchGadget (keyExtract secrets.2) secrets.1
      return (challenge, keySwitchKey)) at hcontext
    rw [mem_support_bind_iff] at hcontext
    obtain ⟨challenge, _hchallenge, hrest⟩ := hcontext
    rw [mem_support_bind_iff] at hrest
    obtain ⟨keySwitchKey, hkey, hpure⟩ := hrest
    simp only [support_pure, Set.mem_singleton_iff] at hpure
    subst context
    congr 1
    have hiff :=
      Native.KeySwitchRecovery.completeCandidate_eq_iff_of_mem_support_generate_centeredBinomial
        keySwitchGadget level secrets.2 secrets.1 candidate hkey hmargin
    by_cases hcandidate : candidate = secrets.1
    · subst candidate
      have hcomplete :
          Native.KeySwitchRecovery.completeCandidate
            keySwitchGadget level keySwitchKey secrets.1 = secrets :=
        hiff.mpr rfl
      simp [hcomplete]
    · have hcomplete :
          Native.KeySwitchRecovery.completeCandidate
            keySwitchGadget level keySwitchKey candidate ≠ secrets :=
        fun heq ↦ hcandidate (hiff.mp heq)
      simp [hcandidate, hcomplete]
  rw [show (oracleOfSecrets
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget secrets).query = viewSampler by
    rfl]
  rw [hconditional]
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
    viewSampler
    (probFailure_fixedSecretView_centeredBinomial
      tgswGadget keySwitchGadget secrets)
    (pure (decide (candidate = secrets.1)))

/-- The amplified scalar lower bound therefore applies unchanged to recovery of both native
secret keys. -/
theorem one_sub_freshAmplifiedError_le_pairedSuccess_centeredBinomial
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (reference : Fin lweDimension)
    (rounds : Fin lweDimension → ℕ)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    1 - ((∑ coordinate,
        FormalProof4FHE.MajorityAmplification.amplifiedError
          (rounds coordinate) threshold) +
      ENNReal.ofReal
          ((1 - KeySwitchFirstCandidateView.keySwitchDecisionAdvantage
            (RLWE.CenteredBinomial.sampler q degree ringEta)
            (CenteredBinomial.scalarSampler q keySwitchEta)
            tgswGadget keySwitchGadget distinguisher) / 2) /
        threshold) ≤
      Pr[= true |
        game (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget
          (completeScalarSolver keySwitchGadget level
            (amplifiedScalarSolver
              (RLWE.CenteredBinomial.sampler q degree ringEta)
              (CenteredBinomial.scalarSampler q keySwitchEta)
              tgswGadget keySwitchGadget rounds distinguisher))] := by
  rw [probOutput_congr rfl
    (evalDist_game_completeScalarSolver_eq_scalarGame
      tgswGadget keySwitchGadget level
      (amplifiedScalarSolver
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget rounds distinguisher)
      hmargin)]
  exact one_sub_freshAmplifiedError_le_scalarSuccess
    (RLWE.CenteredBinomial.sampler q degree ringEta)
    (CenteredBinomial.scalarSampler q keySwitchEta)
    (by simp [CenteredBinomial.scalarSampler])
    tgswGadget keySwitchGadget reference rounds threshold
    hthreshold_pos hthreshold_one distinguisher

/-! ## Quantitative fresh-view hardness transfer -/

/-- Exact success probability of a fresh-view paired-key solver. -/
noncomputable def successProbability
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    ENNReal :=
  Pr[= true |
    game ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget solver]

/-- The complete amplified paired-key solver associated with a public distinguisher. -/
noncomputable def amplifiedSolver
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (rounds : Fin lweDimension → ℕ)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Solver q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  completeScalarSolver keySwitchGadget level
    (amplifiedScalarSolver
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget rounds distinguisher)

/-- Total quantitative error in the fresh-view paired recovery lower bound. -/
noncomputable def amplifiedErrorBound
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : Fin lweDimension → ℕ)
    (threshold : ENNReal)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ENNReal :=
  (∑ coordinate,
    FormalProof4FHE.MajorityAmplification.amplifiedError
      (rounds coordinate) threshold) +
  ENNReal.ofReal
      ((1 - KeySwitchFirstCandidateView.keySwitchDecisionAdvantage
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget distinguisher) / 2) /
    threshold

/-- Fresh-view paired recovery realizes the advertised amplified lower bound. -/
theorem one_sub_amplifiedErrorBound_le_successProbability
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (reference : Fin lweDimension)
    (rounds : Fin lweDimension → ℕ)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    1 - amplifiedErrorBound (ringEta := ringEta) (keySwitchEta := keySwitchEta)
        tgswGadget keySwitchGadget rounds threshold distinguisher ≤
      successProbability
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget
        (amplifiedSolver (ringEta := ringEta) (keySwitchEta := keySwitchEta)
          tgswGadget keySwitchGadget level rounds distinguisher) := by
  simpa only [amplifiedErrorBound, successProbability, amplifiedSolver] using
    (one_sub_freshAmplifiedError_le_pairedSuccess_centeredBinomial
      tgswGadget keySwitchGadget level hmargin reference rounds threshold
      hthreshold_pos hthreshold_one distinguisher)

/-- Exact deficit left after comparing decision advantage with the amplified paired-search lower
bound.  Suitable schedules can make this substantially smaller than the one-shot loss. -/
noncomputable def amplifiedLoss
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : Fin lweDimension → ℕ)
    (threshold : ENNReal)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  max 0
    (KeySwitchFirstCandidateView.keySwitchDecisionAdvantage
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget distinguisher -
      (1 - amplifiedErrorBound (ringEta := ringEta)
        (keySwitchEta := keySwitchEta) tgswGadget keySwitchGadget
        rounds threshold distinguisher).toReal)

theorem amplifiedLoss_nonneg
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : Fin lweDimension → ℕ)
    (threshold : ENNReal)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    0 ≤ amplifiedLoss (ringEta := ringEta) (keySwitchEta := keySwitchEta)
      tgswGadget keySwitchGadget rounds threshold distinguisher := by
  unfold amplifiedLoss
  exact le_max_left _ _

/-- Public KSK-first advantage is bounded by amplified fresh-view paired-search success plus the
explicit schedule-dependent loss. -/
theorem keySwitchDecisionAdvantage_le_successProbability_add_amplifiedLoss
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (reference : Fin lweDimension)
    (rounds : Fin lweDimension → ℕ)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    KeySwitchFirstCandidateView.keySwitchDecisionAdvantage
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget distinguisher ≤
      (successProbability
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget
        (amplifiedSolver (ringEta := ringEta) (keySwitchEta := keySwitchEta)
          tgswGadget keySwitchGadget level rounds distinguisher)).toReal +
      amplifiedLoss (ringEta := ringEta) (keySwitchEta := keySwitchEta)
        tgswGadget keySwitchGadget rounds threshold distinguisher := by
  let advantage := KeySwitchFirstCandidateView.keySwitchDecisionAdvantage
    (RLWE.CenteredBinomial.sampler q degree ringEta)
    (CenteredBinomial.scalarSampler q keySwitchEta)
    tgswGadget keySwitchGadget distinguisher
  let lower := 1 - amplifiedErrorBound (ringEta := ringEta)
    (keySwitchEta := keySwitchEta) tgswGadget keySwitchGadget
    rounds threshold distinguisher
  have haccount :
      advantage ≤ lower.toReal +
        amplifiedLoss (ringEta := ringEta) (keySwitchEta := keySwitchEta)
          tgswGadget keySwitchGadget rounds threshold distinguisher := by
    have hmax : advantage - lower.toReal ≤ max 0 (advantage - lower.toReal) :=
      le_max_right _ _
    dsimp only [advantage, lower] at hmax ⊢
    unfold amplifiedLoss
    linarith
  have hsuccess := one_sub_amplifiedErrorBound_le_successProbability
    (ringEta := ringEta) (keySwitchEta := keySwitchEta)
    tgswGadget keySwitchGadget level hmargin reference rounds threshold
    hthreshold_pos hthreshold_one distinguisher
  have hsuccessReal := ENNReal.toReal_mono probOutput_ne_top hsuccess
  exact haccount.trans (add_le_add hsuccessReal le_rfl)

/-- Fresh-view paired search hardness on the real centered-binomial native distribution. -/
def RealSearchHardAgainst
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed : Solver q degree ringRank tgswLevels lweDimension keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ freshSolver, allowed freshSolver →
    (successProbability
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget freshSolver).toReal ≤ bound

/-- Fresh-view paired-search hardness transfers to native KSK-first public-decision hardness with
the explicitly scheduled amplification loss. -/
theorem nativePublicHardAgainst_of_freshSearchHardness
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (reference : Fin lweDimension)
    (rounds : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Fin lweDimension → ℕ)
    (threshold : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels → ENNReal)
    (hthreshold_pos : ∀ distinguisher, 0 < threshold distinguisher)
    (hthreshold_one : ∀ distinguisher, threshold distinguisher ≤ 1)
    (decisionAllowed : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (solverAllowed : Solver q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (searchBound lossBound : ℝ)
    (hSearch : RealSearchHardAgainst (ringEta := ringEta)
      (keySwitchEta := keySwitchEta) tgswGadget keySwitchGadget
      solverAllowed searchBound)
    (hClosed : ∀ distinguisher, decisionAllowed distinguisher →
      solverAllowed
        (amplifiedSolver (ringEta := ringEta) (keySwitchEta := keySwitchEta)
          tgswGadget keySwitchGadget level (rounds distinguisher) distinguisher))
    (hLoss : ∀ distinguisher, decisionAllowed distinguisher →
      amplifiedLoss (ringEta := ringEta) (keySwitchEta := keySwitchEta)
        tgswGadget keySwitchGadget (rounds distinguisher)
        (threshold distinguisher) distinguisher ≤ lossBound) :
    KeySwitchFirstSearchToDecision.NativePublicHardAgainst
      (keySwitchEta := keySwitchEta)
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      tgswGadget keySwitchGadget decisionAllowed
      (searchBound + lossBound) := by
  intro distinguisher hallowed
  exact (keySwitchDecisionAdvantage_le_successProbability_add_amplifiedLoss
    tgswGadget keySwitchGadget level hmargin reference
    (rounds distinguisher) (threshold distinguisher)
    (hthreshold_pos distinguisher) (hthreshold_one distinguisher)
    distinguisher).trans
      (add_le_add
        (hSearch _ (hClosed distinguisher hallowed))
        (hLoss distinguisher hallowed))

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstFreshView
