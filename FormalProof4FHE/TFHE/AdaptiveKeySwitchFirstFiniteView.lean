/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveKeySwitchFirstSecurity
import FormalProof4FHE.TFHE.KeySwitchFirstFiniteView

/-!
# Finite Augmented Views for Adaptive KSK-First TFHE Security

This module compiles the augmented public-decision premise used by adaptive KSK-first TFHE
security into a finite scalar-key search challenge.  Every stored view contains a real native
BRK, a real native KSK, and an independently sampled zero-message input tape under the same fixed
scalar key.  At common majority depth `rounds`, the challenge contains exactly

`lweDimension * 3 ^ rounds`

such views.  Unlike paired-key completion, no extra view is needed: the reduction only recovers
the scalar key, which is the candidate randomized by the KSK-first argument.

The side tape is carried through candidate randomization unchanged.  Conditional on the fixed
hidden key pair, it is independent of the KSK randomization coins, so the correct candidate
preserves the complete augmented view and the wrong candidate makes only the KSK uniform.  This
gives a common hidden-key-fiber error and therefore sound fresh-view majority amplification.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView

open Native
open Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery
open Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery
open Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstCandidateView

variable {Message : Type}
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]

/-! ## Fixed-secret augmented views -/

/-- A complete public BRK+KSK view paired with a bounded zero-message input tape. -/
abbrev View
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) :=
  PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels ×
    KeySwitchFirstSecurity.InputTape q lweDimension queryCount

/-- Public augmented distinguisher in bundled-view form. -/
abbrev Distinguisher
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) :=
  View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount → ProbComp Bool

/-- Bundle the curried adaptive public distinguisher. -/
def bundleDistinguisher
    (distinguisher : KeySwitchFirstSecurity.PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    Distinguisher q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  fun view ↦ distinguisher view.1.1 view.1.2 view.2

/-- Fixed-secret real augmented view. -/
noncomputable def fixedSecretView
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree) :
    ProbComp (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let bootstrapKey ← Native.generateBootstrappingKey
    q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget secrets.1 secrets.2
  let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
    keySwitchLevels keySwitchErrorSampler keySwitchGadget
    (keyExtract secrets.2) secrets.1
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret secrets.1) 0
  return ((bootstrapKey, keySwitchKey), tape)

/-- Fixed-secret real-BRK/uniform-KSK augmented view. -/
noncomputable def fixedUniformKeySwitchView
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree) :
    ProbComp (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let bootstrapKey ← Native.generateBootstrappingKey
    q degree ringRank tgswLevels lweDimension
    ringErrorSampler tgswGadget secrets.1 secrets.2
  let keySwitchKey ←
    $ᵗ (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
  let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret secrets.1) 0
  return ((bootstrapKey, keySwitchKey), tape)

/-- Randomize only the KSK component and retain the supplied input tape verbatim. -/
def randomizeView
    (coordinate : Fin lweDimension) (candidate : Bool)
    (view : View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) :
    ProbComp (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let context ← KeySwitchFirstCandidateView.randomizeContext
    coordinate candidate view.1.1 view.1.2
  return (context, view.2)

/-- Candidate-dependent check on an augmented public view. -/
def toCandidateCheck
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    Fin lweDimension → Bool →
      View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount →
        ProbComp Bool :=
  fun coordinate candidate view ↦ do
    let transformed ← randomizeView coordinate candidate view
    distinguisher transformed

/-- Fixed hidden scalar bit paired with one fixed-secret augmented view. -/
noncomputable def fixedCoordinateSource
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (coordinate : Fin lweDimension) :
    ProbComp (Bool ×
      View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let view ← fixedSecretView ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget secrets
  return (secrets.1 coordinate, view)

/-- Correct-candidate randomization preserves the entire fixed-secret augmented view. -/
theorem fixedCoordinateSource_randomize_correct_evalDist
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (coordinate : Fin lweDimension) :
    evalDist (do
      let hiddenAndView ← fixedCoordinateSource
        (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget secrets coordinate
      randomizeView coordinate hiddenAndView.1 hiddenAndView.2) =
      evalDist (fixedSecretView ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget secrets) := by
  let pairs : ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
    let bootstrapKey ← Native.generateBootstrappingKey
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
      secrets.1 secrets.2
    let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
      keySwitchLevels keySwitchErrorSampler keySwitchGadget
      (keyExtract secrets.2) secrets.1
    return (bootstrapKey, keySwitchKey)
  let tapes := TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret secrets.1) 0
  let transform := fun
      (context : PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels)
      (tape : KeySwitchFirstSecurity.InputTape q lweDimension queryCount) ↦ do
    let transformed ← KeySwitchFirstCandidateView.randomizeContext
      coordinate (secrets.1 coordinate) context.1 context.2
    return (transformed, tape)
  have hpair :
      evalDist (pairs >>= fun context ↦
        KeySwitchFirstCandidateView.randomizeContext
          coordinate (secrets.1 coordinate) context.1 context.2) =
        evalDist pairs := by
    simpa [pairs, bind_assoc, monad_norm] using
      (KeySwitchFirstCandidateView.randomize_generatedPair_correct_evalDist
        (Native.generateBootstrappingKey q degree ringRank tgswLevels lweDimension
          ringErrorSampler tgswGadget secrets.1 secrets.2)
        keySwitchErrorSampler keySwitchGadget secrets.1 secrets.2 coordinate)
  calc
    evalDist (do
        let hiddenAndView ← fixedCoordinateSource
          (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget secrets coordinate
        randomizeView coordinate hiddenAndView.1 hiddenAndView.2) =
      evalDist (pairs >>= fun context ↦ tapes >>= fun tape ↦
        transform context tape) := by
          simp [fixedCoordinateSource, fixedSecretView, pairs, tapes, transform,
            randomizeView, bind_assoc, monad_norm]
    _ = evalDist (tapes >>= fun tape ↦ pairs >>= fun context ↦
        transform context tape) :=
      evalDist_bind_bind_swap pairs tapes transform
    _ = evalDist (tapes >>= fun tape ↦ pairs >>= fun context ↦
        pure (context, tape)) := by
      refine evalDist_bind_congr' tapes fun tape ↦ ?_
      simpa [transform, bind_assoc] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          hpair (fun context ↦ pure (context, tape)))
    _ = evalDist (pairs >>= fun context ↦ tapes >>= fun tape ↦
        pure (context, tape)) :=
      (evalDist_bind_bind_swap pairs tapes
        (fun context tape ↦ pure (context, tape))).symm
    _ = evalDist (fixedSecretView ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget secrets) := by
      simp [fixedSecretView, pairs, tapes, bind_assoc, monad_norm]

/-- Wrong-candidate randomization makes the KSK uniform while preserving the real BRK and the
same fixed-secret input-tape distribution. -/
theorem fixedCoordinateSource_randomize_wrong_evalDist
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (coordinate : Fin lweDimension) :
    evalDist (do
      let hiddenAndView ← fixedCoordinateSource
        (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget secrets coordinate
      randomizeView coordinate (!hiddenAndView.1) hiddenAndView.2) =
      evalDist (fixedUniformKeySwitchView (keySwitchLevels := keySwitchLevels)
        ringErrorSampler inputErrorSampler tgswGadget secrets) := by
  let pairs : ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
    let bootstrapKey ← Native.generateBootstrappingKey
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
      secrets.1 secrets.2
    let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
      keySwitchLevels keySwitchErrorSampler keySwitchGadget
      (keyExtract secrets.2) secrets.1
    return (bootstrapKey, keySwitchKey)
  let uniformPairs : ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
    let bootstrapKey ← Native.generateBootstrappingKey
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
      secrets.1 secrets.2
    let keySwitchKey ←
      $ᵗ (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
    return (bootstrapKey, keySwitchKey)
  let tapes := TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret secrets.1) 0
  let transform := fun
      (context : PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels)
      (tape : KeySwitchFirstSecurity.InputTape q lweDimension queryCount) ↦ do
    let transformed ← KeySwitchFirstCandidateView.randomizeContext
      coordinate (!(secrets.1 coordinate)) context.1 context.2
    return (transformed, tape)
  have hpair :
      evalDist (pairs >>= fun context ↦
        KeySwitchFirstCandidateView.randomizeContext
          coordinate (!(secrets.1 coordinate)) context.1 context.2) =
        evalDist uniformPairs := by
    simpa [pairs, uniformPairs, bind_assoc, monad_norm] using
      (KeySwitchFirstCandidateView.randomize_generatedPair_wrong_evalDist
        (Native.generateBootstrappingKey q degree ringRank tgswLevels lweDimension
          ringErrorSampler tgswGadget secrets.1 secrets.2)
        keySwitchErrorSampler hError keySwitchGadget secrets.1 secrets.2 coordinate
        (!(secrets.1 coordinate)) (by simp))
  calc
    evalDist (do
        let hiddenAndView ← fixedCoordinateSource
          (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget secrets coordinate
        randomizeView coordinate (!hiddenAndView.1) hiddenAndView.2) =
      evalDist (pairs >>= fun context ↦ tapes >>= fun tape ↦
        transform context tape) := by
          simp [fixedCoordinateSource, fixedSecretView, pairs, tapes, transform,
            randomizeView, bind_assoc, monad_norm]
    _ = evalDist (tapes >>= fun tape ↦ pairs >>= fun context ↦
        transform context tape) :=
      evalDist_bind_bind_swap pairs tapes transform
    _ = evalDist (tapes >>= fun tape ↦ uniformPairs >>= fun context ↦
        pure (context, tape)) := by
      refine evalDist_bind_congr' tapes fun tape ↦ ?_
      simpa [transform, bind_assoc] using
        (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
          hpair (fun context ↦ pure (context, tape)))
    _ = evalDist (uniformPairs >>= fun context ↦ tapes >>= fun tape ↦
        pure (context, tape)) :=
      (evalDist_bind_bind_swap uniformPairs tapes
        (fun context tape ↦ pure (context, tape))).symm
    _ = evalDist (fixedUniformKeySwitchView (keySwitchLevels := keySwitchLevels)
        ringErrorSampler inputErrorSampler tgswGadget secrets) := by
      simp [fixedUniformKeySwitchView, uniformPairs, tapes, bind_assoc, monad_norm]

/-! ## Fixed-secret decision law -/

/-- Fixed-secret real augmented decision experiment. -/
noncomputable def fixedRealDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ProbComp Bool := do
  let view ← fixedSecretView ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget secrets
  distinguisher view

/-- Fixed-secret real-BRK/uniform-KSK augmented decision experiment. -/
noncomputable def fixedUniformKeySwitchDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ProbComp Bool := do
  let view ← fixedUniformKeySwitchView (keySwitchLevels := keySwitchLevels)
    ringErrorSampler inputErrorSampler tgswGadget secrets
  distinguisher view

/-- Native scalar/ring key-pair sampler used by every augmented search experiment. -/
def secretSampler (lweDimension ringRank degree : ℕ) :
    ProbComp (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree) := do
  let lweSecret ← sampleLweSecret lweDimension
  let ringSecret ← sampleRingSecret ringRank degree
  return (lweSecret, ringSecret)

/-- Global real augmented decision experiment in fixed-view order. -/
noncomputable def realDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ProbComp Bool := do
  let secrets ← secretSampler lweDimension ringRank degree
  fixedRealDecisionGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget secrets distinguisher

/-- Global uniform-KSK augmented decision experiment in fixed-view order. -/
noncomputable def uniformKeySwitchDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ProbComp Bool := do
  let secrets ← secretSampler lweDimension ringRank degree
  fixedUniformKeySwitchDecisionGame (keySwitchLevels := keySwitchLevels)
    ringErrorSampler inputErrorSampler tgswGadget secrets distinguisher

/-- Real versus uniform-KSK advantage in the fixed-view sampling order. -/
noncomputable def decisionAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ℝ :=
  (realDecisionGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget distinguisher).boolDistAdvantage
  (uniformKeySwitchDecisionGame ringErrorSampler inputErrorSampler
    tgswGadget distinguisher)

/-- Canonical global sign advice for binary candidate testing. -/
noncomputable def orientation
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : Bool :=
  if (Pr[= true | uniformKeySwitchDecisionGame
      ringErrorSampler inputErrorSampler tgswGadget distinguisher]).toReal ≤
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher]).toReal
    then true else false

/-- Fixed-secret signed gap, oriented using the global advice bit. -/
noncomputable def fixedOrientedGap
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ℝ :=
  if orientation ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher then
    (Pr[= true | fixedRealDecisionGame ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget secrets distinguisher]).toReal -
    (Pr[= true | fixedUniformKeySwitchDecisionGame
      (keySwitchLevels := keySwitchLevels) ringErrorSampler inputErrorSampler
      tgswGadget secrets distinguisher]).toReal
  else
    (Pr[= true | fixedUniformKeySwitchDecisionGame
      (keySwitchLevels := keySwitchLevels) ringErrorSampler inputErrorSampler
      tgswGadget secrets distinguisher]).toReal -
    (Pr[= true | fixedRealDecisionGame ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget secrets distinguisher]).toReal

/-- Correct-candidate checking is the fixed real decision experiment. -/
theorem fixedCorrectCheck_evalDist_eq_fixedRealDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    evalDist
        (FormalProof4FHE.BinaryGuessCheck.correctCheck
          (fixedCoordinateSource (queryCount := queryCount) ringErrorSampler
            keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
            secrets coordinate)
          (fun candidate view ↦
            toCandidateCheck distinguisher coordinate candidate view)) =
      evalDist (fixedRealDecisionGame ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget secrets distinguisher) := by
  unfold FormalProof4FHE.BinaryGuessCheck.correctCheck toCandidateCheck
    fixedRealDecisionGame
  rw [← bind_assoc]
  rw [evalDist_bind,
    fixedCoordinateSource_randomize_correct_evalDist
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget secrets coordinate,
    ← evalDist_bind]

/-- Wrong-candidate checking is the fixed uniform-KSK decision experiment. -/
theorem fixedWrongCheck_evalDist_eq_fixedUniformKeySwitchDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    evalDist
        (FormalProof4FHE.BinaryGuessCheck.wrongCheck
          (fixedCoordinateSource (queryCount := queryCount) ringErrorSampler
            keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
            secrets coordinate)
          (fun candidate view ↦
            toCandidateCheck distinguisher coordinate candidate view)) =
      evalDist (fixedUniformKeySwitchDecisionGame
        (keySwitchLevels := keySwitchLevels) ringErrorSampler inputErrorSampler
        tgswGadget secrets distinguisher) := by
  unfold FormalProof4FHE.BinaryGuessCheck.wrongCheck toCandidateCheck
    fixedUniformKeySwitchDecisionGame
  rw [← bind_assoc]
  rw [evalDist_bind,
    fixedCoordinateSource_randomize_wrong_evalDist
      ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
      tgswGadget keySwitchGadget secrets coordinate,
    ← evalDist_bind]

/-- The fixed-secret candidate gap is independent of the scalar coordinate. -/
theorem fixedCandidateGap_eq_fixedOrientedGap
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    FormalProof4FHE.BinaryGuessCheck.orientedGap
        (fixedCoordinateSource (queryCount := queryCount) ringErrorSampler
          keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
          secrets coordinate)
        (orientation ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher)
        (fun candidate view ↦
          toCandidateCheck distinguisher coordinate candidate view) =
      fixedOrientedGap ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget secrets distinguisher := by
  unfold FormalProof4FHE.BinaryGuessCheck.orientedGap fixedOrientedGap
  rw [probOutput_congr rfl
      (fixedCorrectCheck_evalDist_eq_fixedRealDecisionGame
        ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        keySwitchGadget secrets distinguisher coordinate),
    probOutput_congr rfl
      (fixedWrongCheck_evalDist_eq_fixedUniformKeySwitchDecisionGame
        ringErrorSampler keySwitchErrorSampler inputErrorSampler hError tgswGadget
        keySwitchGadget secrets distinguisher coordinate)]

/-! ## Fresh augmented views and common hidden-key fibers -/

/-- Opaque handle returning fresh augmented views under one fixed hidden key pair. -/
structure Oracle
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) where
  private mk ::
  private sampler : ProbComp
    (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)

namespace Oracle

def query
    (oracle : Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) :
    ProbComp (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) :=
  oracle.sampler

private def ofSampler
    (sampler : ProbComp
      (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)) :
    Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  ⟨sampler⟩

end Oracle

/-- Fresh augmented-view oracle for one fixed native key pair. -/
noncomputable def oracleOfSecrets
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree) :
    Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  Oracle.ofSampler
    (fixedSecretView ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget secrets)

@[simp] theorem query_oracleOfSecrets
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree) :
    (oracleOfSecrets (queryCount := queryCount) ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget secrets).query =
        fixedSecretView ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget secrets := rfl

/-- Hidden scalar vector paired with an opaque fresh augmented-view handle. -/
noncomputable def scalarSource
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (BinarySecret lweDimension ×
      Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let secrets ← secretSampler lweDimension ringRank degree
  return (secrets.1, oracleOfSecrets ringErrorSampler keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget secrets)

/-- One fresh-view candidate guess for a scalar coordinate. -/
noncomputable def coordinateGuess
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension)
    (oracle : Oracle q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount) : ProbComp Bool := do
  let view ← oracle.query
  FormalProof4FHE.BinaryGuessCheck.tester
    (orientation ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher)
    (fun candidate view ↦
      toCandidateCheck distinguisher coordinate candidate view)
    view

/-- Conditional one-shot coordinate failure depends only on the hidden key-pair fiber. -/
theorem fixedCoordinateFailureProbability_eq_ofReal
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    Pr[= false |
      FormalProof4FHE.MajorityAmplification.correctness
        (secrets.1 coordinate)
        (coordinateGuess ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher coordinate
          (oracleOfSecrets ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget secrets))] =
      ENNReal.ofReal
        ((1 - fixedOrientedGap ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget secrets distinguisher) / 2) := by
  simpa [coordinateGuess, oracleOfSecrets, Oracle.query, Oracle.ofSampler,
      fixedCoordinateSource, FormalProof4FHE.MajorityAmplification.correctness,
      FormalProof4FHE.BinaryGuessCheck.game, monad_norm] using
    (FormalProof4FHE.BinaryGuessCheck.failureProbability_eq_ofReal
      (fixedCoordinateSource (queryCount := queryCount) ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
        secrets coordinate)
      (orientation ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher)
      (fun candidate view ↦
        toCandidateCheck distinguisher coordinate candidate view)).trans
      (congrArg ENNReal.ofReal
        (congrArg (fun gap : ℝ ↦ (1 - gap) / 2)
          (fixedCandidateGap_eq_fixedOrientedGap
            ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
            tgswGadget keySwitchGadget secrets distinguisher coordinate)))

/-! ## Averaged decision gap -/

/-- Global hidden coordinate paired with one real augmented public view. -/
noncomputable def coordinateSource
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp (Bool ×
      View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) := do
  let secrets ← secretSampler lweDimension ringRank degree
  fixedCoordinateSource ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget secrets coordinate

/-- Correct checking averaged over native secrets is the global real decision experiment. -/
theorem correctCheck_evalDist_eq_realDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    evalDist
        (FormalProof4FHE.BinaryGuessCheck.correctCheck
          (coordinateSource (queryCount := queryCount) ringErrorSampler
            keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget coordinate)
          (fun candidate view ↦
            toCandidateCheck distinguisher coordinate candidate view)) =
      evalDist (realDecisionGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher) := by
  unfold coordinateSource realDecisionGame
    FormalProof4FHE.BinaryGuessCheck.correctCheck
  simp only [bind_assoc]
  refine evalDist_bind_congr' (secretSampler lweDimension ringRank degree) fun secrets ↦ ?_
  simpa [FormalProof4FHE.BinaryGuessCheck.correctCheck] using
    (fixedCorrectCheck_evalDist_eq_fixedRealDecisionGame
      ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
      keySwitchGadget secrets distinguisher coordinate)

/-- Wrong checking averaged over native secrets is the global uniform-KSK experiment. -/
theorem wrongCheck_evalDist_eq_uniformKeySwitchDecisionGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    evalDist
        (FormalProof4FHE.BinaryGuessCheck.wrongCheck
          (coordinateSource (queryCount := queryCount) ringErrorSampler
            keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget coordinate)
          (fun candidate view ↦
            toCandidateCheck distinguisher coordinate candidate view)) =
      evalDist (uniformKeySwitchDecisionGame (keySwitchLevels := keySwitchLevels)
        ringErrorSampler inputErrorSampler tgswGadget distinguisher) := by
  unfold coordinateSource uniformKeySwitchDecisionGame
    FormalProof4FHE.BinaryGuessCheck.wrongCheck
  simp only [bind_assoc]
  refine evalDist_bind_congr' (secretSampler lweDimension ringRank degree) fun secrets ↦ ?_
  simpa [FormalProof4FHE.BinaryGuessCheck.wrongCheck] using
    (fixedWrongCheck_evalDist_eq_fixedUniformKeySwitchDecisionGame
      ringErrorSampler keySwitchErrorSampler inputErrorSampler hError tgswGadget
      keySwitchGadget secrets distinguisher coordinate)

theorem orientation_le
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    if orientation ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher then
      (Pr[= true | uniformKeySwitchDecisionGame
        ringErrorSampler inputErrorSampler tgswGadget distinguisher]).toReal ≤
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher]).toReal
    else
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher]).toReal ≤
      (Pr[= true | uniformKeySwitchDecisionGame
        ringErrorSampler inputErrorSampler tgswGadget distinguisher]).toReal := by
  unfold orientation
  split
  · assumption
  · exact le_of_not_ge ‹_›

/-- Every averaged coordinate candidate gap is the same augmented decision advantage. -/
theorem candidateGap_eq_decisionAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    FormalProof4FHE.BinaryGuessCheck.orientedGap
        (coordinateSource (queryCount := queryCount) ringErrorSampler
          keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget coordinate)
        (orientation ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher)
        (fun candidate view ↦
          toCandidateCheck distinguisher coordinate candidate view) =
      decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher := by
  unfold FormalProof4FHE.BinaryGuessCheck.orientedGap decisionAdvantage
  rw [probOutput_congr rfl
      (correctCheck_evalDist_eq_realDecisionGame
        ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        keySwitchGadget distinguisher coordinate),
    probOutput_congr rfl
      (wrongCheck_evalDist_eq_uniformKeySwitchDecisionGame
        ringErrorSampler keySwitchErrorSampler inputErrorSampler hError tgswGadget
        keySwitchGadget distinguisher coordinate)]
  unfold ProbComp.boolDistAdvantage
  by_cases horientation : orientation ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget distinguisher = true
  · have hle := orientation_le ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget distinguisher
    rw [if_pos horientation] at hle ⊢
    exact (abs_of_nonneg (sub_nonneg.mpr hle)).symm
  · have hle := orientation_le ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget distinguisher
    rw [if_neg horientation] at hle ⊢
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    ring

/-- Global one-shot coordinate failure is the decision-error expression. -/
theorem coordinateGame_failureProbability_eq_ofReal
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (coordinate : Fin lweDimension) :
    Pr[= false |
      FormalProof4FHE.BinaryGuessCheck.game
        (coordinateSource (queryCount := queryCount) ringErrorSampler
          keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget coordinate)
        (orientation ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher)
        (fun candidate view ↦
          toCandidateCheck distinguisher coordinate candidate view)] =
      ENNReal.ofReal
        ((1 - decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher) / 2) := by
  exact (FormalProof4FHE.BinaryGuessCheck.failureProbability_eq_ofReal
    (coordinateSource (queryCount := queryCount) ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget coordinate)
    (orientation ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher)
    (fun candidate view ↦
      toCandidateCheck distinguisher coordinate candidate view)).trans
    (congrArg ENNReal.ofReal
      (congrArg (fun gap : ℝ ↦ (1 - gap) / 2)
        (candidateGap_eq_decisionAdvantage ringErrorSampler keySwitchErrorSampler
          inputErrorSampler hError tgswGadget keySwitchGadget distinguisher coordinate)))

/-- Conditional one-shot error at a fixed reference coordinate. -/
noncomputable def fiberError
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (reference : Fin lweDimension)
    (hiddenAndOracle : BinarySecret lweDimension ×
      Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) : ENNReal :=
  Pr[= false |
    FormalProof4FHE.MajorityAmplification.correctness
      (hiddenAndOracle.1 reference)
      (coordinateGuess ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher reference hiddenAndOracle.2)]

/-- All coordinates have the same base error on every supported hidden-key fiber. -/
theorem coordinateFailureProbability_eq_fiberError_of_mem_support
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (reference coordinate : Fin lweDimension)
    (hiddenAndOracle : BinarySecret lweDimension ×
      Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)
    (hsupport : hiddenAndOracle ∈ support
      (scalarSource ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget)) :
    Pr[= false |
      FormalProof4FHE.MajorityAmplification.correctness
        (hiddenAndOracle.1 coordinate)
        (coordinateGuess ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher coordinate hiddenAndOracle.2)] =
      fiberError ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher reference hiddenAndOracle := by
  unfold scalarSource at hsupport
  rw [mem_support_bind_iff] at hsupport
  obtain ⟨secrets, _hsecrets, hpure⟩ := hsupport
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst hiddenAndOracle
  unfold fiberError
  rw [fixedCoordinateFailureProbability_eq_ofReal
      ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
      tgswGadget keySwitchGadget secrets distinguisher coordinate,
    fixedCoordinateFailureProbability_eq_ofReal
      ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
      tgswGadget keySwitchGadget secrets distinguisher reference]

/-- Averaging the common fiber error gives the global one-shot decision error. -/
theorem expectedFiberError_eq_decisionError
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount)
    (reference : Fin lweDimension) :
    (∑' hiddenAndOracle,
      Pr[= hiddenAndOracle |
        scalarSource ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget] *
        fiberError ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher reference hiddenAndOracle) =
      ENNReal.ofReal
        ((1 - decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher) / 2) := by
  unfold fiberError
  rw [← probOutput_bind_eq_tsum]
  have hgame :
      evalDist (do
        let hiddenAndOracle ← scalarSource ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget
        FormalProof4FHE.MajorityAmplification.correctness
          (hiddenAndOracle.1 reference)
          (coordinateGuess ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget distinguisher reference hiddenAndOracle.2)) =
      evalDist
        (FormalProof4FHE.BinaryGuessCheck.game
          (coordinateSource (queryCount := queryCount) ringErrorSampler
            keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget reference)
          (orientation ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget distinguisher)
          (fun candidate view ↦
            toCandidateCheck distinguisher reference candidate view)) := by
    simp [scalarSource, coordinateSource, oracleOfSecrets, coordinateGuess,
      Oracle.query, Oracle.ofSampler, fixedCoordinateSource,
      FormalProof4FHE.MajorityAmplification.correctness,
      FormalProof4FHE.BinaryGuessCheck.game, monad_norm]
  rw [probOutput_congr rfl hgame]
  exact coordinateGame_failureProbability_eq_ofReal
    ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
    tgswGadget keySwitchGadget distinguisher reference

/-! ## Fresh-view amplification -/

abbrev ScalarSolver
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) :=
  Oracle q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount →
    ProbComp (BinarySecret lweDimension)

/-- Exact scalar-key recovery experiment for a fresh-view solver. -/
noncomputable def scalarGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : ScalarSolver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount) : ProbComp Bool := do
  let hiddenAndOracle ← scalarSource ringErrorSampler keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget
  FormalProof4FHE.MajorityAmplification.vectorCorrectness
    hiddenAndOracle.1 (solver hiddenAndOracle.2)

/-- Query one fresh augmented view for every leaf of every coordinate majority tree. -/
noncomputable def amplifiedScalarSolver
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : Fin lweDimension → ℕ)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    ScalarSolver q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount :=
  FormalProof4FHE.MajorityAmplification.amplifyVector rounds
    (coordinateGuess ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher)

/-- Whole-scalar-key failure after common-fiber fresh-view amplification. -/
theorem amplifiedScalarFailureProbability_le
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : Fin lweDimension → ℕ)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    Pr[= false |
      scalarGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget
        (amplifiedScalarSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds distinguisher)] ≤
      (∑ coordinate,
        FormalProof4FHE.MajorityAmplification.amplifiedError
          (rounds coordinate) threshold) +
      ENNReal.ofReal
          ((1 - decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget distinguisher) / 2) /
        threshold := by
  simpa only [scalarGame, amplifiedScalarSolver,
      FormalProof4FHE.MajorityAmplification.vectorRecoveryGame] using
    (FormalProof4FHE.MajorityAmplification.vectorRecoveryGame_amplify_failure_le_of_common_average
      (scalarSource ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget)
      rounds
      (coordinateGuess ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher)
      (fiberError ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher reference)
      threshold
      (ENNReal.ofReal
        ((1 - decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher) / 2))
      hthreshold_pos hthreshold_one
      (fun hiddenAndOracle hsupport coordinate ↦
        (coordinateFailureProbability_eq_fiberError_of_mem_support
          ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
          tgswGadget keySwitchGadget distinguisher reference coordinate
          hiddenAndOracle hsupport).le)
      (expectedFiberError_eq_decisionError
        ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
        tgswGadget keySwitchGadget distinguisher reference).le)

/-- Total common-fiber amplification error for a selected schedule. -/
noncomputable def amplifiedErrorBound
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : Fin lweDimension → ℕ)
    (threshold : ENNReal)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ENNReal :=
  (∑ coordinate,
    FormalProof4FHE.MajorityAmplification.amplifiedError
      (rounds coordinate) threshold) +
  ENNReal.ofReal
      ((1 - decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher) / 2) /
    threshold

/-- Equivalent fresh-view scalar-success lower bound. -/
theorem one_sub_amplifiedErrorBound_le_freshScalarSuccess
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : Fin lweDimension → ℕ)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    1 - amplifiedErrorBound ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds threshold distinguisher ≤
      Pr[= true |
        scalarGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget
          (amplifiedScalarSolver ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget rounds distinguisher)] := by
  unfold amplifiedErrorBound
  let experiment := scalarGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget
    (amplifiedScalarSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget rounds distinguisher)
  have hfailure := amplifiedScalarFailureProbability_le
    ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
    tgswGadget keySwitchGadget reference rounds threshold
    hthreshold_pos hthreshold_one distinguisher
  have hsuccess := probEvent_one_sub_le_of_compl_le
    (mx := experiment) (p := fun output : Bool ↦ output = true)
    probFailure_eq_zero (by
      simpa [experiment] using hfailure)
  simpa [experiment] using hsuccess

/-! ## Explicit finite augmented batches -/

/-- One majority tree per scalar coordinate. -/
abbrev Batch
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount rounds : ℕ) :=
  Fin lweDimension →
    FormalProof4FHE.MajorityAmplification.MajorityBatch
      (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) rounds

/-- Independently sample every leaf of every scalar-coordinate majority tree. -/
def sampleBatch
    (rounds : ℕ)
    (sampler : ProbComp
      (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount)) :
    ProbComp (Batch q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :=
  Fin.mOfFn lweDimension fun _ ↦
    FormalProof4FHE.MajorityAmplification.sampleMajorityBatch rounds sampler

/-- The scalar-only finite challenge contains exactly `lweDimension * 3 ^ rounds` views. -/
def viewCount (lweDimension rounds : ℕ) : ℕ :=
  lweDimension * FormalProof4FHE.MajorityAmplification.majorityBatchViewCount rounds

theorem viewCount_eq (lweDimension rounds : ℕ) :
    viewCount lweDimension rounds = lweDimension * 3 ^ rounds := by
  simp [viewCount,
    FormalProof4FHE.MajorityAmplification.majorityBatchViewCount_eq_pow]

/-- Scalar-key solver receiving one explicit finite augmented batch. -/
abbrev Solver
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount rounds : ℕ) :=
  Batch q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount rounds →
    ProbComp (BinarySecret lweDimension)

/-- Exact scalar-key recovery experiment for a finite augmented batch. -/
noncomputable def game
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) : ProbComp Bool := do
  let secrets ← secretSampler lweDimension ringRank degree
  let batch ← sampleBatch rounds
    (fixedSecretView ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget secrets)
  let recovered ← solver batch
  return decide (recovered = secrets.1)

/-- Concrete finite reduction obtained by running the candidate test over every stored majority
tree. -/
noncomputable def amplifiedSolver
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    Solver q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount rounds :=
  fun batch ↦
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstFiniteView.runScalarBatch
      (fun coordinate view ↦
        FormalProof4FHE.BinaryGuessCheck.tester
          (orientation ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget distinguisher)
          (fun candidate view ↦
            toCandidateCheck distinguisher coordinate candidate view)
          view)
      batch

/-- For fixed secrets, the front-loaded finite scalar batch has the fresh-view output law. -/
theorem evalDist_fixedBatch_amplifiedSolver_eq_freshScalar
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (secrets : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Secret
      lweDimension ringRank degree)
    (rounds : ℕ)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    evalDist (do
      let batch ← sampleBatch rounds
        (fixedSecretView ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget secrets)
      amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds distinguisher batch) =
      evalDist
        (amplifiedScalarSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget (fun _ ↦ rounds) distinguisher
          (oracleOfSecrets ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget secrets)) := by
  let viewSampler : ProbComp
      (View q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) :=
    fixedSecretView (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget secrets
  let trial := fun coordinate view ↦
    FormalProof4FHE.BinaryGuessCheck.tester
      (orientation ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher)
      (fun candidate view ↦
        toCandidateCheck distinguisher coordinate candidate view)
      view
  let oracle : Oracle q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount :=
    oracleOfSecrets (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget secrets
  have hcoordinate (coordinate : Fin lweDimension) :
      FormalProof4FHE.MajorityAmplification.amplify rounds
          (fun _ : Unit ↦ viewSampler >>= trial coordinate) () =
        FormalProof4FHE.MajorityAmplification.amplify rounds
          (coordinateGuess ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget distinguisher coordinate) oracle := by
    apply FormalProof4FHE.MajorityAmplification.amplify_eq_of_base_eq
    simp [trial, viewSampler, oracle, coordinateGuess]
  have hvector :
      FormalProof4FHE.MajorityAmplification.amplifyVector
          (fun _ : Fin lweDimension ↦ rounds)
          (fun coordinate (_ : Unit) ↦ viewSampler >>= trial coordinate) () =
        amplifiedScalarSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget (fun _ ↦ rounds) distinguisher oracle := by
    unfold FormalProof4FHE.MajorityAmplification.amplifyVector amplifiedScalarSolver
    exact congrArg (fun samplers ↦ Fin.mOfFn lweDimension samplers)
      (funext hcoordinate)
  have hbatch :=
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstFiniteView.evalDist_sampleScalarBatch_run
      lweDimension rounds viewSampler trial
  rw [hvector] at hbatch
  simpa [sampleBatch, amplifiedSolver, viewSampler, trial, oracle] using hbatch

/-- The concrete finite game and fresh-view scalar game are distributionally identical. -/
theorem evalDist_game_amplifiedSolver_eq_freshScalarGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    evalDist
        (game ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds
          (amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget rounds distinguisher)) =
      evalDist
        (scalarGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget
          (amplifiedScalarSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget (fun _ ↦ rounds) distinguisher)) := by
  unfold game scalarGame scalarSource
    FormalProof4FHE.MajorityAmplification.vectorCorrectness
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' (secretSampler lweDimension ringRank degree) fun secrets ↦ ?_
  have hscalar := evalDist_fixedBatch_amplifiedSolver_eq_freshScalar
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
    keySwitchGadget secrets rounds distinguisher
  simpa only [bind_assoc] using
    (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      hscalar (fun recovered ↦ pure (decide (recovered = secrets.1))))

/-- Exact finite-batch scalar recovery success probability. -/
noncomputable def successProbability
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) : ENNReal :=
  Pr[= true |
    game ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget rounds solver]

/-- The explicit finite augmented challenge achieves the fresh-view amplification bound. -/
theorem one_sub_amplifiedErrorBound_le_successProbability
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    1 - amplifiedErrorBound ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget (fun _ ↦ rounds) threshold distinguisher ≤
      successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds
        (amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds distinguisher) := by
  unfold successProbability
  rw [probOutput_congr rfl
    (evalDist_game_amplifiedSolver_eq_freshScalarGame
      ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
      keySwitchGadget rounds distinguisher)]
  exact one_sub_amplifiedErrorBound_le_freshScalarSuccess
    ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
    tgswGadget keySwitchGadget reference (fun _ ↦ rounds) threshold
    hthreshold_pos hthreshold_one distinguisher

/-! ## Bridge to the adaptive public-decision interface -/

/-- The fixed-view real experiment is the adaptive augmented public real experiment. -/
theorem realDecisionGame_evalDist_eq_adaptiveSecurity
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : KeySwitchFirstSecurity.PublicDistinguisher
      q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) :
    evalDist (realDecisionGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget (bundleDistinguisher distinguisher)) =
      evalDist (KeySwitchFirstSecurity.realDecisionGame
        ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher) := by
  simp [realDecisionGame, fixedRealDecisionGame, fixedSecretView, secretSampler,
    bundleDistinguisher, KeySwitchFirstSecurity.realDecisionGame,
    bind_assoc, monad_norm]

/-- Reordering the independent uniform KSK gives the adaptive augmented public endpoint. -/
theorem uniformKeySwitchDecisionGame_evalDist_eq_adaptiveSecurity
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (distinguisher : KeySwitchFirstSecurity.PublicDistinguisher
      q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) :
    evalDist (uniformKeySwitchDecisionGame
        ringErrorSampler inputErrorSampler tgswGadget
        (bundleDistinguisher distinguisher)) =
      evalDist (KeySwitchFirstSecurity.uniformKeySwitchDecisionGame
        ringErrorSampler inputErrorSampler tgswGadget distinguisher) := by
  unfold uniformKeySwitchDecisionGame fixedUniformKeySwitchDecisionGame
    fixedUniformKeySwitchView secretSampler bundleDistinguisher
    KeySwitchFirstSecurity.uniformKeySwitchDecisionGame
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' (sampleLweSecret lweDimension) fun lweSecret ↦ ?_
  let UniformKeySwitch : ProbComp
      (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) :=
    $ᵗ (KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
  let RingSecrets := sampleRingSecret ringRank degree
  let Bootstrap := fun ringSecret ↦
    Native.generateBootstrappingKey q degree ringRank tgswLevels lweDimension
      ringErrorSampler tgswGadget lweSecret ringSecret
  let Tapes := TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
    (embedBinarySecret lweSecret) 0
  let finish := fun
      (bootstrapKey : BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (keySwitchKey : KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels)
      (tape : KeySwitchFirstSecurity.InputTape q lweDimension queryCount) ↦
    distinguisher bootstrapKey keySwitchKey tape
  calc
    evalDist (RingSecrets >>= fun ringSecret ↦
        Bootstrap ringSecret >>= fun bootstrapKey ↦
        UniformKeySwitch >>= fun keySwitchKey ↦
        Tapes >>= fun tape ↦ finish bootstrapKey keySwitchKey tape) =
      evalDist (RingSecrets >>= fun ringSecret ↦
        UniformKeySwitch >>= fun keySwitchKey ↦
        Bootstrap ringSecret >>= fun bootstrapKey ↦
        Tapes >>= fun tape ↦ finish bootstrapKey keySwitchKey tape) := by
      refine evalDist_bind_congr' RingSecrets fun ringSecret ↦ ?_
      exact evalDist_bind_bind_swap (Bootstrap ringSecret) UniformKeySwitch
        (fun bootstrapKey keySwitchKey ↦
          Tapes >>= fun tape ↦ finish bootstrapKey keySwitchKey tape)
    _ = evalDist (UniformKeySwitch >>= fun keySwitchKey ↦
        RingSecrets >>= fun ringSecret ↦
        Bootstrap ringSecret >>= fun bootstrapKey ↦
        Tapes >>= fun tape ↦ finish bootstrapKey keySwitchKey tape) :=
      (evalDist_bind_bind_swap UniformKeySwitch RingSecrets
        (fun keySwitchKey ringSecret ↦
          Bootstrap ringSecret >>= fun bootstrapKey ↦
          Tapes >>= fun tape ↦ finish bootstrapKey keySwitchKey tape)).symm

/-- The local fixed-view advantage is exactly the adaptive augmented public advantage. -/
theorem decisionAdvantage_eq_adaptiveSecurity
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : KeySwitchFirstSecurity.PublicDistinguisher
      q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) :
    decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget (bundleDistinguisher distinguisher) =
      KeySwitchFirstSecurity.keySwitchDecisionAdvantage
        ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher := by
  unfold decisionAdvantage KeySwitchFirstSecurity.keySwitchDecisionAdvantage
    ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (realDecisionGame_evalDist_eq_adaptiveSecurity
        ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher),
    probOutput_congr rfl
      (uniformKeySwitchDecisionGame_evalDist_eq_adaptiveSecurity
        ringErrorSampler inputErrorSampler tgswGadget distinguisher)]

/-! ## Quantitative finite-search reduction -/

/-- Exact deficit after comparing decision advantage with the finite amplified lower bound. -/
noncomputable def amplifiedLoss
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (threshold : ENNReal)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ℝ :=
  max 0
    (decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher -
      (1 - amplifiedErrorBound ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget (fun _ ↦ rounds) threshold distinguisher).toReal)

theorem amplifiedLoss_nonneg
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ) (threshold : ENNReal)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    0 ≤ amplifiedLoss ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget rounds threshold distinguisher := by
  unfold amplifiedLoss
  exact le_max_left _ _

/-- Augmented public advantage is bounded by finite scalar-search success plus the explicit
common-fiber amplification loss. -/
theorem decisionAdvantage_le_successProbability_add_amplifiedLoss
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher ≤
      (successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds
        (amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds distinguisher)).toReal +
      amplifiedLoss ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds threshold distinguisher := by
  let advantage := decisionAdvantage ringErrorSampler keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget distinguisher
  let lower := 1 - amplifiedErrorBound ringErrorSampler keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget (fun _ ↦ rounds)
    threshold distinguisher
  have haccount :
      advantage ≤ lower.toReal +
        amplifiedLoss ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds threshold distinguisher := by
    have hmax : advantage - lower.toReal ≤
        max 0 (advantage - lower.toReal) := le_max_right _ _
    dsimp only [advantage, lower] at hmax ⊢
    unfold amplifiedLoss
    linarith
  have hsuccess := one_sub_amplifiedErrorBound_le_successProbability
    ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
    tgswGadget keySwitchGadget reference rounds threshold
    hthreshold_pos hthreshold_one distinguisher
  have hsuccessReal := ENNReal.toReal_mono probOutput_ne_top hsuccess
  exact haccount.trans (add_le_add hsuccessReal le_rfl)

/-- Adaptive public advantage in curried form inherits the finite scalar-search bound. -/
theorem adaptiveKeySwitchDecisionAdvantage_le_finiteSearch_add_loss
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1)
    (distinguisher : KeySwitchFirstSecurity.PublicDistinguisher
      q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) :
    KeySwitchFirstSecurity.keySwitchDecisionAdvantage
        ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher ≤
      (successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds
        (amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds (bundleDistinguisher distinguisher))).toReal +
      amplifiedLoss ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds threshold
        (bundleDistinguisher distinguisher) := by
  rw [← decisionAdvantage_eq_adaptiveSecurity]
  exact decisionAdvantage_le_successProbability_add_amplifiedLoss
    ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
    tgswGadget keySwitchGadget reference rounds threshold
    hthreshold_pos hthreshold_one (bundleDistinguisher distinguisher)

/-- **Finite-search adaptive TFHE bound.**  Replace the augmented decision term in the complete
adaptive theorem by explicit finite scalar-search success and amplification loss. -/
theorem abs_signedAdvantage_real_le_finiteSearch_add_loss_add_two_moduleLwe_add_inputLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      (successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds
        (amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds
          (bundleDistinguisher
            (KeySwitchFirstSecurity.toPublicDistinguisher
              (queryCount := queryCount) encode adversary)))).toReal +
      amplifiedLoss ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds threshold
        (bundleDistinguisher
          (KeySwitchFirstSecurity.toPublicDistinguisher
            (queryCount := queryCount) encode adversary)) +
      LearningWithErrors.advantage
        (BootstrapCutSecurity.batchModuleLweProblem
          q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (BootstrapCutSecurity.realBatchReduction
          ringErrorSampler ($ᵗ (ZMod q)) tgswGadget
          (Adaptive.CutCycleSecurity.cutContinuation
            queryCount inputErrorSampler encode adversary)) +
      LearningWithErrors.advantage
        (BootstrapCutSecurity.batchModuleLweProblem
          q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (BootstrapCutSecurity.zeroBatchReduction
          ringErrorSampler ($ᵗ (ZMod q))
          (Adaptive.CutCycleSecurity.cutContinuation
            queryCount inputErrorSampler encode adversary)) +
      LearningWithErrors.advantage
        (KeySwitchSecurity.binaryLweProblem q lweDimension queryCount inputErrorSampler)
        (KeySwitchFirstSecurity.inputTapeReduction ringErrorSampler inputErrorSampler
          tgswGadget encode adversary) := by
  have hSecurity :=
    KeySwitchFirstSecurity.abs_signedAdvantage_real_le_decision_add_two_moduleLwe_add_inputLwe
      queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode adversary hbound
  have hDecision := adaptiveKeySwitchDecisionAdvantage_le_finiteSearch_add_loss
    ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
    tgswGadget keySwitchGadget reference rounds threshold
    hthreshold_pos hthreshold_one
    (KeySwitchFirstSecurity.toPublicDistinguisher
      (queryCount := queryCount) encode adversary)
  linarith

/-! ## Adversary-class hardness transfer -/

/-- Finite augmented scalar-search hardness on the real BRK+KSK+input-tape distribution. -/
def RealSearchHardAgainst
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (allowed : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds → Prop)
    (bound : ℝ) : Prop :=
  ∀ solver, allowed solver →
    (successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget rounds solver).toReal ≤ bound

/-- **Finite-search foundation for adaptive TFHE security.**  Hardness of scalar-key recovery
from exactly `lweDimension * 3 ^ rounds` augmented real views, the explicit amplification-loss
bound, two conventional ring batch-module-LWE assumptions, and one conventional scalar batch-LWE
assumption on exactly `queryCount` input rows imply security of the full bounded adaptive game. -/
theorem hardAgainst_of_finiteSearch_and_lwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (threshold : KeySwitchFirstSecurity.PublicDistinguisher
      q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount → ENNReal)
    (hthreshold_pos : ∀ distinguisher, 0 < threshold distinguisher)
    (hthreshold_one : ∀ distinguisher, threshold distinguisher ≤ 1)
    (encode : Message → ZMod q)
    (tfheAllowed : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (solverAllowed : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds → Prop)
    (moduleLweAllowed : LearningWithErrors.Adversary
      (BootstrapCutSecurity.batchModuleLweProblem
        q degree ringRank tgswLevels lweDimension ringErrorSampler) → Prop)
    (inputLweAllowed : LearningWithErrors.Adversary
      (KeySwitchSecurity.binaryLweProblem q lweDimension queryCount inputErrorSampler) → Prop)
    (searchBound lossBound moduleLweBound inputLweBound : ℝ)
    (hSearch : RealSearchHardAgainst ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget rounds solverAllowed searchBound)
    (hFiniteClosed : ∀ adversary, tfheAllowed adversary →
      solverAllowed
        (amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds
          (bundleDistinguisher
            (KeySwitchFirstSecurity.toPublicDistinguisher
              (queryCount := queryCount) encode adversary))))
    (hLoss : ∀ adversary, tfheAllowed adversary →
      amplifiedLoss ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds
        (threshold (KeySwitchFirstSecurity.toPublicDistinguisher
          (queryCount := queryCount) encode adversary))
        (bundleDistinguisher
          (KeySwitchFirstSecurity.toPublicDistinguisher
            (queryCount := queryCount) encode adversary)) ≤ lossBound)
    (hRealModuleClosed : ∀ adversary, tfheAllowed adversary →
      moduleLweAllowed
        (BootstrapCutSecurity.realBatchReduction
          ringErrorSampler ($ᵗ (ZMod q)) tgswGadget
          (Adaptive.CutCycleSecurity.cutContinuation
            queryCount inputErrorSampler encode adversary)))
    (hZeroModuleClosed : ∀ adversary, tfheAllowed adversary →
      moduleLweAllowed
        (BootstrapCutSecurity.zeroBatchReduction
          ringErrorSampler ($ᵗ (ZMod q))
          (Adaptive.CutCycleSecurity.cutContinuation
            queryCount inputErrorSampler encode adversary)))
    (hInputClosed : ∀ adversary, tfheAllowed adversary →
      inputLweAllowed
        (KeySwitchFirstSecurity.inputTapeReduction
          ringErrorSampler inputErrorSampler tgswGadget encode adversary))
    (hModuleLwe : FormalProof4FHE.LWE.HardAgainst
      (BootstrapCutSecurity.batchModuleLweProblem
        q degree ringRank tgswLevels lweDimension ringErrorSampler)
      moduleLweAllowed moduleLweBound)
    (hInputLwe : FormalProof4FHE.LWE.HardAgainst
      (KeySwitchSecurity.binaryLweProblem q lweDimension queryCount inputErrorSampler)
      inputLweAllowed inputLweBound) :
    Adaptive.HardAgainst queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode tfheAllowed
      (searchBound + lossBound + 2 * moduleLweBound + inputLweBound) := by
  intro adversary hadversary hbound
  have hExpanded :=
    abs_signedAdvantage_real_le_finiteSearch_add_loss_add_two_moduleLwe_add_inputLwe
      queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
      tgswGadget keySwitchGadget reference rounds
      (threshold (KeySwitchFirstSecurity.toPublicDistinguisher
        (queryCount := queryCount) encode adversary))
      (hthreshold_pos _) (hthreshold_one _) encode adversary hbound
  have hFinite := hSearch _ (hFiniteClosed adversary hadversary)
  have hLossBound := hLoss adversary hadversary
  have hRealModule := hModuleLwe _ (hRealModuleClosed adversary hadversary)
  have hZeroModule := hModuleLwe _ (hZeroModuleClosed adversary hadversary)
  have hInput := hInputLwe _ (hInputClosed adversary hadversary)
  linarith

end FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView
