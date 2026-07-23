/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.KeySwitchCandidateRandomization
import FormalProof4FHE.TFHE.ScalarCoordinateRecovery

/-!
# KSK-First Candidate Views for Native TFHE

This module lifts coordinate randomization of a native TLWE batch to the complete public TFHE
evaluation-key view.  The bootstrapping key is retained unchanged.  For a proposed scalar-key bit,
fresh randomness is added to the selected row of every KSK challenge and the proposed bit times
that randomness is added to the bodies.

After averaging over the actual native source experiment:

* the true candidate gives the original real BRK+KSK view exactly; and
* the opposite candidate gives a real BRK together with an independent uniform KSK exactly.

This is the KSK-first analogue of the BRK-first candidate-view interface.  It closes the exact
binary-coordinate search-to-decision algebra for the scalar TFHE key.  It does not by itself
replace the remaining real BRK by its zero or uniform endpoint, nor does it prove the resulting
computational hardness assumption.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstCandidateView

open KeySwitchCandidateRandomization

/-- Candidate transform on the complete public view: keep the BRK and randomize only the KSK. -/
def randomizeContext
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    [NeZero q]
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank tgswLevels lweDimension)
    (auxiliary : Auxiliary q degree ringRank lweDimension keySwitchLevels) :
    ProbComp (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
  let shift ← $ᵗ (Fin ((ringRank * degree) * keySwitchLevels) → ZMod q)
  return (challenge, randomizeBatch coordinate candidate shift auxiliary)

/-- KSK-first uniform endpoint: retain the native real bootstrapping key but replace the complete
key-switch table by an independent uniform transcript. -/
noncomputable def uniformKeySwitchPublicView
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
  let auxiliary ← $ᵗ (Auxiliary q degree ringRank lweDimension keySwitchLevels)
  return (challenge, auxiliary)

/-- For fixed native secrets and any sampled BRK, the correct-candidate KSK transform preserves
the real paired view. -/
theorem randomize_generatedPair_correct_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (bootstrapSampler :
      ProbComp (Challenge q degree ringRank tgswLevels lweDimension))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (coordinate : Fin lweDimension) :
    evalDist (do
      let challenge ← bootstrapSampler
      let auxiliary ← generateKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract ringSecret) lweSecret
      randomizeContext coordinate (lweSecret coordinate) challenge auxiliary) =
    evalDist (do
      let challenge ← bootstrapSampler
      let auxiliary ← generateKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract ringSecret) lweSecret
      return (challenge, auxiliary)) := by
  refine evalDist_bind_congr' bootstrapSampler fun challenge => ?_
  rw [show (generateKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract ringSecret) lweSecret >>= fun auxiliary =>
      randomizeContext coordinate (lweSecret coordinate) challenge auxiliary) =
      (randomizeKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract ringSecret) lweSecret coordinate (lweSecret coordinate) >>= fun auxiliary =>
      pure (challenge, auxiliary)) by
    simp [randomizeContext, randomizeKeySwitchKey, randomizeEncryption,
      generateKeySwitchKey, monad_norm]]
  rw [evalDist_bind,
    randomizeKeySwitchKey_correct_evalDist q lweDimension (ringRank * degree)
      keySwitchLevels keySwitchErrorSampler keySwitchGadget
      (keyExtract ringSecret) lweSecret coordinate,
    ← evalDist_bind]

/-- For fixed native secrets and any sampled BRK, the wrong-candidate transform replaces the KSK
by an independent uniform transcript exactly. -/
theorem randomize_generatedPair_wrong_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (bootstrapSampler :
      ProbComp (Challenge q degree ringRank tgswLevels lweDimension))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank degree)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (hcandidate : candidate ≠ lweSecret coordinate) :
    evalDist (do
      let challenge ← bootstrapSampler
      let auxiliary ← generateKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract ringSecret) lweSecret
      randomizeContext coordinate candidate challenge auxiliary) =
    evalDist (do
      let challenge ← bootstrapSampler
      let auxiliary ← $ᵗ (Auxiliary q degree ringRank lweDimension keySwitchLevels)
      return (challenge, auxiliary)) := by
  refine evalDist_bind_congr' bootstrapSampler fun challenge => ?_
  rw [show (generateKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract ringSecret) lweSecret >>= fun auxiliary =>
      randomizeContext coordinate candidate challenge auxiliary) =
      (randomizeKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract ringSecret) lweSecret coordinate candidate >>= fun auxiliary =>
      pure (challenge, auxiliary)) by
    simp [randomizeContext, randomizeKeySwitchKey, randomizeEncryption,
      generateKeySwitchKey, monad_norm]]
  rw [evalDist_bind,
    randomizeKeySwitchKey_wrong_evalDist q lweDimension (ringRank * degree)
      keySwitchLevels keySwitchErrorSampler hError keySwitchGadget
      (keyExtract ringSecret) lweSecret coordinate candidate hcandidate,
    ← evalDist_bind]

/-- Averaged over the native coordinate source, submitting the hidden scalar bit gives exactly
the complete real public view. -/
theorem coordinateSource_randomizeContext_correct_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist (do
      let hiddenAndContext ← coordinateSource (ringRank := ringRank)
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget coordinate
      randomizeContext coordinate hiddenAndContext.1
        hiddenAndContext.2.1 hiddenAndContext.2.2) =
      evalDist (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget) := by
  simp only [coordinateSource, realPublicView, Search.problem,
    LWE.AuxiliaryInput.Search.exactRecoveryProblem, AuxiliaryInput.problem]
  simp only [bind_assoc, pure_bind]
  change evalDist (do
      let lweSecret ← sampleLweSecret lweDimension
      let ringSecret ← sampleRingSecret ringRank degree
      let challenge ← MonomialKDM.generateBootstrappingKey
        q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
        lweSecret ringSecret
      let auxiliary ← generateKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract ringSecret) lweSecret
      randomizeContext coordinate (lweSecret coordinate) challenge auxiliary) =
    evalDist (do
      let lweSecret ← sampleLweSecret lweDimension
      let ringSecret ← sampleRingSecret ringRank degree
      let challenge ← MonomialKDM.generateBootstrappingKey
        q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
        lweSecret ringSecret
      let auxiliary ← generateKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract ringSecret) lweSecret
      return (challenge, auxiliary))
  refine evalDist_bind_congr' (sampleLweSecret lweDimension) fun lweSecret => ?_
  refine evalDist_bind_congr' (sampleRingSecret ringRank degree) fun ringSecret => ?_
  exact randomize_generatedPair_correct_evalDist
    (MonomialKDM.generateBootstrappingKey
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
      lweSecret ringSecret)
    keySwitchErrorSampler keySwitchGadget lweSecret ringSecret coordinate

/-- Averaged over the native coordinate source, submitting the opposite scalar bit gives exactly
the real-BRK/uniform-KSK endpoint. -/
theorem coordinateSource_randomizeContext_wrong_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist (do
      let hiddenAndContext ← coordinateSource (ringRank := ringRank)
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget coordinate
      randomizeContext coordinate (!hiddenAndContext.1)
        hiddenAndContext.2.1 hiddenAndContext.2.2) =
      evalDist (uniformKeySwitchPublicView (ringRank := ringRank)
        (lweDimension := lweDimension) ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget) := by
  simp only [coordinateSource, uniformKeySwitchPublicView, Search.problem,
    LWE.AuxiliaryInput.Search.exactRecoveryProblem, AuxiliaryInput.problem]
  simp only [bind_assoc, pure_bind]
  change evalDist (do
      let lweSecret ← sampleLweSecret lweDimension
      let ringSecret ← sampleRingSecret ringRank degree
      let challenge ← MonomialKDM.generateBootstrappingKey
        q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
        lweSecret ringSecret
      let auxiliary ← generateKeySwitchKey q lweDimension (ringRank * degree)
        keySwitchLevels keySwitchErrorSampler keySwitchGadget
        (keyExtract ringSecret) lweSecret
      randomizeContext coordinate (!(lweSecret coordinate)) challenge auxiliary) =
    evalDist (do
      let lweSecret ← sampleLweSecret lweDimension
      let ringSecret ← sampleRingSecret ringRank degree
      let challenge ← MonomialKDM.generateBootstrappingKey
        q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
        lweSecret ringSecret
      let auxiliary ← $ᵗ (Auxiliary q degree ringRank lweDimension keySwitchLevels)
      return (challenge, auxiliary))
  refine evalDist_bind_congr' (sampleLweSecret lweDimension) fun lweSecret => ?_
  refine evalDist_bind_congr' (sampleRingSecret ringRank degree) fun ringSecret => ?_
  exact randomize_generatedPair_wrong_evalDist
    (MonomialKDM.generateBootstrappingKey
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
      lweSecret ringSecret)
    keySwitchErrorSampler hError keySwitchGadget lweSecret ringSecret coordinate
    (!(lweSecret coordinate)) (by simp)

/-! ## KSK-first decision gap and scalar-key recovery -/

/-- Public decision experiment at the real-BRK/uniform-KSK endpoint. -/
noncomputable def uniformKeySwitchDecisionGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool := do
  let context ← uniformKeySwitchPublicView (ringRank := ringRank)
    (lweDimension := lweDimension) ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget
  distinguisher context.1 context.2

/-- Real versus real-BRK/uniform-KSK distinguishing advantage. -/
noncomputable def keySwitchDecisionAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  (realDecisionGame ringErrorSampler keySwitchErrorSampler tgswGadget
    keySwitchGadget distinguisher).boolDistAdvantage
  (uniformKeySwitchDecisionGame ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget distinguisher)

/-- Postcompose coordinate-candidate randomization with a KSK-first public distinguisher. -/
def toCandidateCheck
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun coordinate candidate challenge auxiliary => do
    let transformed ← randomizeContext coordinate candidate challenge auxiliary
    distinguisher transformed.1 transformed.2

/-- Canonical sign of the KSK-first decision gap, used as one bit of nonuniform reduction
advice. -/
noncomputable def orientation
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : Bool :=
  if (Pr[= true | uniformKeySwitchDecisionGame ringErrorSampler keySwitchErrorSampler
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
      (Pr[= true | uniformKeySwitchDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher]).toReal ≤
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher]).toReal
    else
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher]).toReal ≤
      (Pr[= true | uniformKeySwitchDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher]).toReal := by
  unfold orientation
  split
  · assumption
  · exact le_of_not_ge ‹_›

/-- The correct-candidate check is exactly the native real decision experiment. -/
theorem correctCandidateCheckGame_toCandidateCheck_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    evalDist (correctCandidateCheckGame ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget (toCandidateCheck distinguisher) coordinate) =
      evalDist (realDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher) := by
  unfold correctCandidateCheckGame FormalProof4FHE.BinaryGuessCheck.correctCheck
    toCandidateCheck
  rw [← bind_assoc]
  rw [evalDist_bind,
    coordinateSource_randomizeContext_correct_evalDist ringErrorSampler
      keySwitchErrorSampler tgswGadget keySwitchGadget coordinate,
    ← evalDist_bind, ← realDecisionGame_eq_bind_realPublicView]

/-- The wrong-candidate check is exactly the real-BRK/uniform-KSK decision experiment. -/
theorem wrongCandidateCheckGame_toCandidateCheck_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    evalDist (wrongCandidateCheckGame ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget (toCandidateCheck distinguisher) coordinate) =
      evalDist (uniformKeySwitchDecisionGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher) := by
  unfold wrongCandidateCheckGame FormalProof4FHE.BinaryGuessCheck.wrongCheck
    toCandidateCheck uniformKeySwitchDecisionGame
  rw [← bind_assoc]
  rw [evalDist_bind,
    coordinateSource_randomizeContext_wrong_evalDist ringErrorSampler
      keySwitchErrorSampler hError tgswGadget keySwitchGadget coordinate,
    ← evalDist_bind]

/-- The exact candidate-check gap equals the KSK-first public distinguishing advantage. -/
theorem candidateCheckGap_eq_keySwitchDecisionAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    candidateCheckGap ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (fun _ => orientation ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget distinguisher)
        (toCandidateCheck distinguisher) coordinate =
      keySwitchDecisionAdvantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher := by
  unfold candidateCheckGap FormalProof4FHE.BinaryGuessCheck.orientedGap
  rw [show FormalProof4FHE.BinaryGuessCheck.correctCheck
      (coordinateSource ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate)
      (fun candidate context =>
        toCandidateCheck distinguisher coordinate candidate context.1 context.2) =
      correctCandidateCheckGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget (toCandidateCheck distinguisher) coordinate from rfl]
  rw [show FormalProof4FHE.BinaryGuessCheck.wrongCheck
      (coordinateSource ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate)
      (fun candidate context =>
        toCandidateCheck distinguisher coordinate candidate context.1 context.2) =
      wrongCandidateCheckGame ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget (toCandidateCheck distinguisher) coordinate from rfl]
  rw [probOutput_congr rfl
      (correctCandidateCheckGame_toCandidateCheck_evalDist ringErrorSampler
        keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher coordinate),
    probOutput_congr rfl
      (wrongCandidateCheckGame_toCandidateCheck_evalDist ringErrorSampler
        keySwitchErrorSampler hError tgswGadget keySwitchGadget distinguisher coordinate)]
  unfold keySwitchDecisionAdvantage ProbComp.boolDistAdvantage
  by_cases horientation : orientation ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget distinguisher = true
  · have hle := orientation_le ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget distinguisher
    rw [if_pos horientation] at hle ⊢
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  · have hle := orientation_le ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget distinguisher
    rw [if_neg horientation] at hle ⊢
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    ring

/-- One-shot error for every scalar coordinate is exactly half of one minus the KSK-first
decision advantage. -/
theorem coordinateGame_failureProbability
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    (Pr[= false |
      coordinateGame ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (testerOfCheck
          (fun _ => orientation ringErrorSampler keySwitchErrorSampler
            tgswGadget keySwitchGadget distinguisher)
          (toCandidateCheck distinguisher)) coordinate]).toReal =
      (1 - keySwitchDecisionAdvantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher) / 2 := by
  rw [coordinateGame_testerOfCheck_failureProbability,
    candidateCheckGap_eq_keySwitchDecisionAdvantage ringErrorSampler
      keySwitchErrorSampler hError tgswGadget keySwitchGadget distinguisher coordinate]

/-- Coordinatewise KSK-first guess/check assembles into a whole scalar-key solver. -/
theorem one_sub_sum_keySwitchDecisionError_le_scalarSuccess
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    1 - ∑ _coordinate : Fin lweDimension,
        ENNReal.ofReal ((1 - keySwitchDecisionAdvantage ringErrorSampler
          keySwitchErrorSampler tgswGadget keySwitchGadget distinguisher) / 2) ≤
      Pr[= true |
        PairedRecovery.scalarGame ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget
          (assemble (testerOfCheck
            (fun _ => orientation ringErrorSampler keySwitchErrorSampler
              tgswGadget keySwitchGadget distinguisher)
            (toCandidateCheck distinguisher)))] := by
  apply one_sub_sum_gapError_le_scalarSuccess ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget
    (fun _ => orientation ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget distinguisher)
    (toCandidateCheck distinguisher)
    (fun _ => keySwitchDecisionAdvantage ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget distinguisher)
  intro coordinate
  exact le_of_eq (candidateCheckGap_eq_keySwitchDecisionAdvantage ringErrorSampler
    keySwitchErrorSampler hError tgswGadget keySwitchGadget distinguisher coordinate).symm

/-- With centered-binomial KSK noise and a separated decoding level, the same lower bound applies
to recovery of both native TFHE keys: the existing KSK completion theorem reconstructs the ring
key without any additional probability loss. -/
theorem one_sub_sum_keySwitchDecisionError_le_pairedSearchSuccess_centeredBinomial
    {q degree ringRank tgswLevels lweDimension keySwitchLevels keySwitchEta : ℕ}
    [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level))
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    1 - ∑ _coordinate : Fin lweDimension,
        ENNReal.ofReal ((1 - keySwitchDecisionAdvantage ringErrorSampler
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget distinguisher) / 2) ≤
      Search.successProbability ringErrorSampler
        (CenteredBinomial.scalarSampler q keySwitchEta) tgswGadget keySwitchGadget
        (PairedRecovery.completeScalarSolver keySwitchGadget level
          (assemble (testerOfCheck
            (fun _ => orientation ringErrorSampler
              (CenteredBinomial.scalarSampler q keySwitchEta)
              tgswGadget keySwitchGadget distinguisher)
            (toCandidateCheck distinguisher)))) := by
  rw [PairedRecovery.successProbability_completeScalarSolver_eq
    ringErrorSampler tgswGadget keySwitchGadget level _ hmargin]
  apply one_sub_sum_keySwitchDecisionError_le_scalarSuccess
    ringErrorSampler (CenteredBinomial.scalarSampler q keySwitchEta)
    (by simp [CenteredBinomial.scalarSampler])
    tgswGadget keySwitchGadget distinguisher

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.KeySwitchFirstCandidateView
