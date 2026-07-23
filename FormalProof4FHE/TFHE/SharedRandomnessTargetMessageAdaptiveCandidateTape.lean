/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveRelativeKeyShift
import FormalProof4FHE.TFHE.KeySwitchCandidateRandomization

set_option autoImplicit false

/-!
# Exact Candidate Randomization of the Direct Adaptive Target-Key Tape

This file supplies the assumption-free binary guess-and-check algebra for the direct FHE CircLWE
view.  A candidate for one extracted target-key bit is used to randomize the corresponding row of
every query-tape challenge.

* The correct candidate reproduces the complete real `(tape, BRK, extension)` distribution.
* The wrong candidate replaces the complete tape by an independent uniform tape while retaining
  the real evaluation material.

The remaining shifted evaluator can therefore be analyzed only after these two exact endpoints
have been established; no circular or RLWE assumption is used here.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE

noncomputable section

open FormalProof4FHE.TFHE.Native.KeySwitchCandidateRandomization

/-- Add fresh candidate randomness to one extracted target-key coordinate throughout the complete
query tape and retain the evaluation material unchanged. -/
def randomizeTargetTapeCandidate
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1)))
    (candidate : Bool)
    (view : View q (degree + 1) 1 suffixRank levels queryCount) :
    ProbComp (View q (degree + 1) 1 suffixRank levels queryCount) := do
  let shift ← $ᵗ (Fin queryCount → ZMod q)
  return (randomizeBatch coordinate candidate shift view.1, view.2)

/-- Fixed-secret endpoint with a uniform tape and the unchanged real evaluation material. -/
def sampleUniformTapeMaterialView
    (q degree suffixRank levels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1)) :
    ProbComp (View q (degree + 1) 1 suffixRank levels queryCount) :=
  FormalProof4FHE.TFHE.SamplerReplacement.independentPair
    ($ᵗ (Challenge q (degree + 1) 1 suffixRank queryCount))
    (sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
      bootstrapErrorSampler extensionErrorSampler gadget secret)
    Prod.mk

/-- Sampling an independent second component commutes with fresh probabilistic transformation of
the first component. -/
theorem evalDist_randomizeFirst_independentPair
    {A B C A' : Type}
    (first : ProbComp A) (second : ProbComp B)
    (randomness : ProbComp C) (transform : C → A → A') :
    evalDist
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
            first second Prod.mk >>=
          fun pair ↦ randomness >>= fun randomValue ↦
            pure (transform randomValue pair.1, pair.2)) =
      evalDist
        (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
          (first >>= fun value ↦ randomness >>= fun randomValue ↦
            pure (transform randomValue value))
          second Prod.mk) := by
  unfold FormalProof4FHE.TFHE.SamplerReplacement.independentPair
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  refine evalDist_bind_congr' first fun value ↦ ?_
  exact OracleComp.DeferredSampling.evalDist_bind_comm second randomness
    (fun secondValue randomValue ↦
      pure (transform randomValue value, secondValue))

/-- For a fixed nested key, the true target-key bit reproduces the complete real view exactly. -/
theorem randomizeTargetTapeCandidate_correct_evalDist
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1))
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    evalDist
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget secret >>=
          randomizeTargetTapeCandidate coordinate
            (targetMessages secret.1 secret.2 coordinate)) =
      evalDist
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
          bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget secret) := by
  let tape := sampleTargetTape q (degree + 1) 1 suffixRank queryCount
    inputErrorSampler secret
  let material := sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
    bootstrapErrorSampler extensionErrorSampler gadget secret
  let randomizedTape :=
    KeySwitchCandidateRandomization.randomizeEncryption (samples := queryCount)
      inputErrorSampler
      (targetMessages secret.1 secret.2) coordinate
      (targetMessages secret.1 secret.2 coordinate)
      (0 : Fin queryCount → ZMod q)
  have hview :
      evalDist
          (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
              bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget secret >>=
            randomizeTargetTapeCandidate coordinate
              (targetMessages secret.1 secret.2 coordinate)) =
        evalDist
          (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
            randomizedTape material Prod.mk) := by
    have hreal := sampleRealView_eq_independentPair q (degree + 1) 1 suffixRank
      levels queryCount bootstrapErrorSampler extensionErrorSampler
      inputErrorSampler gadget secret
    rw [evalDist_bind, congrArg evalDist hreal, ← evalDist_bind]
    unfold randomizeTargetTapeCandidate
    simpa only [randomizedTape, tape, material,
      sampleTargetTape,
      KeySwitchCandidateRandomization.randomizeEncryption] using
      (evalDist_randomizeFirst_independentPair tape material
        ($ᵗ (Fin queryCount → ZMod q))
        (fun shift ciphertext ↦ randomizeBatch coordinate
          (targetMessages secret.1 secret.2 coordinate) shift ciphertext))
  have htape : evalDist randomizedTape = evalDist tape := by
    simpa only [randomizedTape, tape, sampleTargetTape] using
      (KeySwitchCandidateRandomization.randomizeEncryption_correct_evalDist
        inputErrorSampler (targetMessages secret.1 secret.2) coordinate 0)
  rw [hview]
  have hindependent :
      evalDist
          (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
            randomizedTape material Prod.mk) =
        evalDist
          (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
            tape material Prod.mk) := by
    unfold FormalProof4FHE.TFHE.SamplerReplacement.independentPair
    rw [evalDist_bind, htape, ← evalDist_bind]
  rw [hindependent]
  exact congrArg evalDist
    (sampleRealView_eq_independentPair q (degree + 1) 1 suffixRank levels
      queryCount bootstrapErrorSampler extensionErrorSampler inputErrorSampler
      gadget secret).symm

/-- For a fixed nested key, every wrong candidate replaces the complete target-key tape by an
independent uniform tape exactly.  The error sampler only needs to be failure-free. -/
theorem randomizeTargetTapeCandidate_wrong_evalDist
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (secret : Secret 1 suffixRank (degree + 1))
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1)))
    (candidate : Bool) (hcandidate : candidate ≠ targetMessages secret.1 secret.2 coordinate) :
    evalDist
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget secret >>=
          randomizeTargetTapeCandidate coordinate candidate) =
      evalDist
        (sampleUniformTapeMaterialView q degree suffixRank levels queryCount
          bootstrapErrorSampler extensionErrorSampler gadget secret) := by
  let tape := sampleTargetTape q (degree + 1) 1 suffixRank queryCount
    inputErrorSampler secret
  let material := sampleEvaluationMaterial q (degree + 1) 1 suffixRank levels
    bootstrapErrorSampler extensionErrorSampler gadget secret
  let randomizedTape :=
    KeySwitchCandidateRandomization.randomizeEncryption (samples := queryCount)
      inputErrorSampler (targetMessages secret.1 secret.2) coordinate candidate
      (0 : Fin queryCount → ZMod q)
  have hview :
      evalDist
          (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
              bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget secret >>=
            randomizeTargetTapeCandidate coordinate candidate) =
        evalDist
          (FormalProof4FHE.TFHE.SamplerReplacement.independentPair
            randomizedTape material Prod.mk) := by
    have hreal := sampleRealView_eq_independentPair q (degree + 1) 1 suffixRank
      levels queryCount bootstrapErrorSampler extensionErrorSampler
      inputErrorSampler gadget secret
    rw [evalDist_bind, congrArg evalDist hreal, ← evalDist_bind]
    unfold randomizeTargetTapeCandidate
    simpa only [randomizedTape, tape, material,
      sampleTargetTape,
      KeySwitchCandidateRandomization.randomizeEncryption] using
      (evalDist_randomizeFirst_independentPair tape material
        ($ᵗ (Fin queryCount → ZMod q))
        (fun shift ciphertext ↦ randomizeBatch coordinate candidate shift ciphertext))
  have htape : evalDist randomizedTape =
      evalDist ($ᵗ (Challenge q (degree + 1) 1 suffixRank queryCount)) := by
    simpa only [randomizedTape] using
      (KeySwitchCandidateRandomization.randomizeEncryption_wrong_evalDist
        inputErrorSampler hInputError (targetMessages secret.1 secret.2)
        coordinate candidate hcandidate 0)
  rw [hview]
  unfold sampleUniformTapeMaterialView
  unfold FormalProof4FHE.TFHE.SamplerReplacement.independentPair
  rw [evalDist_bind, htape, ← evalDist_bind]

/-- Public source for testing one extracted target-key coordinate. -/
def targetCoordinateSource
    (q degree suffixRank levels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    ProbComp
      (Bool × View q (degree + 1) 1 suffixRank levels queryCount) := do
  let secret ← sampleNestedSecret 1 suffixRank (degree + 1)
  let view ← sampleRealView q (degree + 1) 1 suffixRank levels queryCount
    bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget secret
  return (targetMessages secret.1 secret.2 coordinate, view)

/-- Averaged direct real public view, without exposing the sampled nested key. -/
def sampleFreshRealPublicView
    (q degree suffixRank levels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin levels → RLWE.Rq q (degree + 1)) :
    ProbComp (View q (degree + 1) 1 suffixRank levels queryCount) := do
  let secret ← sampleNestedSecret 1 suffixRank (degree + 1)
  sampleRealView q (degree + 1) 1 suffixRank levels queryCount
    bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget secret

/-- Averaged direct uniform-tape public view with real evaluation material. -/
def sampleFreshUniformTapePublicView
    (q degree suffixRank levels queryCount : ℕ) [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (gadget : Fin levels → RLWE.Rq q (degree + 1)) :
    ProbComp (View q (degree + 1) 1 suffixRank levels queryCount) := do
  let secret ← sampleNestedSecret 1 suffixRank (degree + 1)
  sampleUniformTapeMaterialView q degree suffixRank levels queryCount
    bootstrapErrorSampler extensionErrorSampler gadget secret

/-- Averaged over the hidden coordinate source, the correct candidate is exactly the fresh real
public view. -/
theorem targetCoordinateSource_correct_evalDist
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    evalDist (do
        let hiddenAndView ← targetCoordinateSource q degree suffixRank levels queryCount
          bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget coordinate
        randomizeTargetTapeCandidate coordinate hiddenAndView.1 hiddenAndView.2) =
      evalDist
        (sampleFreshRealPublicView q degree suffixRank levels queryCount
          bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget) := by
  unfold targetCoordinateSource sampleFreshRealPublicView
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' (sampleNestedSecret 1 suffixRank (degree + 1)) fun secret ↦ ?_
  exact randomizeTargetTapeCandidate_correct_evalDist bootstrapErrorSampler
    extensionErrorSampler inputErrorSampler gadget secret coordinate

/-- Averaged over the hidden coordinate source, the opposite candidate is exactly the fresh
uniform-tape public view. -/
theorem targetCoordinateSource_wrong_evalDist
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    (bootstrapErrorSampler extensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    evalDist (do
        let hiddenAndView ← targetCoordinateSource q degree suffixRank levels queryCount
          bootstrapErrorSampler extensionErrorSampler inputErrorSampler gadget coordinate
        randomizeTargetTapeCandidate coordinate (!hiddenAndView.1) hiddenAndView.2) =
      evalDist
        (sampleFreshUniformTapePublicView q degree suffixRank levels queryCount
          bootstrapErrorSampler extensionErrorSampler gadget) := by
  unfold targetCoordinateSource sampleFreshUniformTapePublicView
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' (sampleNestedSecret 1 suffixRank (degree + 1)) fun secret ↦ ?_
  exact randomizeTargetTapeCandidate_wrong_evalDist bootstrapErrorSampler
    extensionErrorSampler inputErrorSampler hInputError gadget secret coordinate
    (!(targetMessages secret.1 secret.2 coordinate)) (by simp)

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE
