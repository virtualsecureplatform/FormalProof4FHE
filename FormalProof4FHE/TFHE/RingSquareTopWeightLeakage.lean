/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInput
import FormalProof4FHE.TFHE.RingSquareTopWeightSampleExtraction

/-!
# Highest Two-Adic `RGSW_S(-S)` as RLWE with Structured Secret Leakage

The highest two-adic square message is coefficient-linear but not ring-linear.  A direct public
ring-mask translation therefore cannot absorb it.  This file gives a different exact joint
reformulation: reveal the complete top-square message as auxiliary information, subtract it from
the ciphertext body, and retain the original common negacyclic masks and narrow errors.

The resulting challenge is ordinary rank-one binary-secret RLWE with two rows, augmented by the
structured leakage `L(S) = 2^k S^2` in the upper row and zero in the lower row.  Adding the leaked
message back maps the real leakage-RLWE game to the complete coefficient-affine top-row game and
preserves the uniform endpoint.  Thus native top-row circular security is exactly a
leakage-resilient RLWE statement; no circular ciphertext remains in this endpoint.

This is not yet a reduction from ordinary RLWE without leakage.  Its purpose is to isolate the
next joint theorem while preserving the shared ring-mask law that independent scalar extraction
cannot reproduce.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightLeakage

open FormalProof4FHE.TFHE
open FormalProof4FHE.TFHE.Native
open FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE
open FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE
open FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightCoefficientAffine

noncomputable section

/-- The coefficient transcript carrier shared by the top-row and ordinary RLWE games. -/
abbrev Transcript (exponent degree : ℕ) :=
  CoefficientStructuredLWE.Transcript
    (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1)

/-- The complete coefficient-vector message added to the two stripped top rows. -/
abbrev Leakage (exponent degree : ℕ) :=
  CoefficientStructuredLWE.Output
    (2 ^ (exponent + 1)) (degree + 1) (TGSW.rowCount 1 1)

/-- The highest-weight upper square message together with its lower zero row. -/
noncomputable def topLeakage (exponent degree : ℕ)
    (ringSecret : RingBinarySecret 1 (degree + 1)) : Leakage exponent degree :=
  fun row ↦
    topRGSWOperators exponent degree row
      (CoefficientStructuredLWE.binaryCoefficients
        (2 ^ (exponent + 1)) (ringSecret 0))

/-- Add a known message vector to every body row of a coefficient transcript. -/
def addLeakage {q degree sampleCount : ℕ}
    (leakage : CoefficientStructuredLWE.Output q degree sampleCount)
    (transcript : CoefficientStructuredLWE.Transcript q degree 1 sampleCount) :
    CoefficientStructuredLWE.Transcript q degree 1 sampleCount :=
  (transcript.1, transcript.2 + leakage)

/-- Remove a known message vector from every body row. -/
def subLeakage {q degree sampleCount : ℕ}
    (leakage : CoefficientStructuredLWE.Output q degree sampleCount)
    (transcript : CoefficientStructuredLWE.Transcript q degree 1 sampleCount) :
    CoefficientStructuredLWE.Transcript q degree 1 sampleCount :=
  (transcript.1, transcript.2 - leakage)

@[simp]
theorem subLeakage_addLeakage {q degree sampleCount : ℕ}
    (leakage : CoefficientStructuredLWE.Output q degree sampleCount)
    (transcript : CoefficientStructuredLWE.Transcript q degree 1 sampleCount) :
    subLeakage leakage (addLeakage leakage transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  simp [addLeakage, subLeakage]

@[simp]
theorem addLeakage_subLeakage {q degree sampleCount : ℕ}
    (leakage : CoefficientStructuredLWE.Output q degree sampleCount)
    (transcript : CoefficientStructuredLWE.Transcript q degree 1 sampleCount) :
    addLeakage leakage (subLeakage leakage transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  simp [addLeakage, subLeakage]

/-- Body translation by fixed leakage is a permutation of the complete transcript carrier. -/
theorem addLeakage_bijective {q degree sampleCount : ℕ}
    (leakage : CoefficientStructuredLWE.Output q degree sampleCount) :
    Function.Bijective
      (addLeakage leakage :
        CoefficientStructuredLWE.Transcript q degree 1 sampleCount →
          CoefficientStructuredLWE.Transcript q degree 1 sampleCount) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨subLeakage leakage, subLeakage_addLeakage leakage,
      addLeakage_subLeakage leakage⟩

/-- Ordinary binary-secret coefficient RLWE underlying the top-row leakage formulation. -/
noncomputable def ordinaryProblem
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  exact CoefficientStructuredLWE.problem
    (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1) errorSampler

/-- The coefficient-affine top-row noiseless output is exactly ordinary RLWE plus the leaked
top-square message. -/
theorem top_noiseless_eq_ordinary_add_leakage
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (ringSecret : RingBinarySecret 1 (degree + 1))
    (challenge : CoefficientStructuredLWE.Challenge
      (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1)) :
    (topRGSWCoefficientProblem exponent degree errorSampler).noiseless
        ringSecret challenge =
      (ordinaryProblem exponent degree errorSampler).noiseless ringSecret challenge +
        topLeakage exponent degree ringSecret := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [show (ordinaryProblem exponent degree errorSampler).noiseless ringSecret challenge =
      CoefficientStructuredLWE.negacyclicVecMul ringSecret challenge by
    exact CoefficientStructuredLWE.problem_noiseless_eq_negacyclicVecMul
      (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1)
        errorSampler ringSecret challenge]
  unfold topRGSWCoefficientProblem topLeakage
  dsimp only
  funext row output
  simp [CoefficientAffineCircularRLWE.coefficientAffineNoiseless,
    CoefficientStructuredLWE.negacyclicVecMul]

/-- Ordinary fixed-secret RLWE transcript sampler. -/
noncomputable def fixedSecretOrdinarySampler
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (ringSecret : RingBinarySecret 1 (degree + 1)) :
    ProbComp (Transcript exponent degree) := do
  let challenge ← (ordinaryProblem exponent degree errorSampler).sampleChallenge
  let error ← (ordinaryProblem exponent degree errorSampler).sampleError
  return (challenge,
    (ordinaryProblem exponent degree errorSampler).noiseless ringSecret challenge + error)

/-- Ordinary binary-secret RLWE with the complete top-square message exposed as auxiliary
leakage.  The real and zero fields coincide because this endpoint contains no circular
ciphertext. -/
noncomputable def leakageProblem
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    LWE.AuxiliaryInput.Problem
      (RingBinarySecret 1 (degree + 1))
      (Transcript exponent degree)
      (Leakage exponent degree) where
  sampleSecret := sampleRingSecret 1 (degree + 1)
  sampleReal := fixedSecretOrdinarySampler exponent degree errorSampler
  sampleZero := fixedSecretOrdinarySampler exponent degree errorSampler
  sampleUniform := $ᵗ (Transcript exponent degree)
  sampleAuxiliary := fun ringSecret ↦ pure (topLeakage exponent degree ringSecret)

/-- A top-row adversary uses the leaked message only to restore the original circular body. -/
def leakageContinuation
    {exponent degree : ℕ}
    {errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))}
    (adversary : LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent degree errorSampler)) :
    LWE.AuxiliaryInput.Continuation
      (RingBinarySecret 1 (degree + 1))
      (Transcript exponent degree)
      (Leakage exponent degree) :=
  fun _ transcript leakage ↦ adversary (addLeakage leakage transcript)

/-- The leakage-RLWE real game restores exactly the complete coefficient-affine top-row real
game. -/
theorem leakageRealGame_evalDist_eq_topGame0
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (adversary : LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent degree errorSampler)) :
    evalDist (LWE.AuxiliaryInput.realGame
        (leakageProblem exponent degree errorSampler)
        (leakageContinuation adversary)) =
      evalDist (LearningWithErrors.game0
        (topRGSWCoefficientProblem exponent degree errorSampler) adversary) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  let Top := topRGSWCoefficientProblem exponent degree errorSampler
  let Ordinary := ordinaryProblem exponent degree errorSampler
  let Secrets := sampleRingSecret 1 (degree + 1)
  let Challenges := Ordinary.sampleChallenge
  let Errors := Ordinary.sampleError
  let finish := fun
      (challenge : CoefficientStructuredLWE.Challenge
        (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1))
      (ringSecret : RingBinarySecret 1 (degree + 1))
      (error : CoefficientStructuredLWE.Output
        (2 ^ (exponent + 1)) (degree + 1) (TGSW.rowCount 1 1)) ↦
    adversary (challenge,
      (Ordinary.noiseless ringSecret challenge +
        topLeakage exponent degree ringSecret) + error)
  have hLeakage :
      LWE.AuxiliaryInput.realGame
          (leakageProblem exponent degree errorSampler)
          (leakageContinuation adversary) =
        (Secrets >>= fun ringSecret ↦
          Challenges >>= fun challenge ↦ Errors >>= finish challenge ringSecret) := by
    simp [LWE.AuxiliaryInput.realGame, leakageProblem,
      fixedSecretOrdinarySampler, leakageContinuation, addLeakage,
      Secrets, Challenges, Errors, Ordinary, finish, bind_assoc,
      add_comm, add_left_comm]
  have hChallenge : Top.sampleChallenge = Challenges := by rfl
  have hSecret : Top.sampleSecret = Secrets := by rfl
  have hError : Top.sampleError = Errors := by rfl
  have hTop :
      LearningWithErrors.game0 Top adversary =
        (Challenges >>= fun challenge ↦
          Secrets >>= fun ringSecret ↦ Errors >>= finish challenge ringSecret) := by
    unfold LearningWithErrors.game0 LearningWithErrors.distr
    rw [hChallenge, hSecret, hError]
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro challenge
    apply bind_congr
    intro ringSecret
    apply bind_congr
    intro error
    rw [top_noiseless_eq_ordinary_add_leakage]
  rw [hLeakage, hTop]
  exact (evalDist_bind_bind_swap Challenges Secrets
    (fun challenge ringSecret ↦ Errors >>= finish challenge ringSecret)).symm

/-- The coefficient-affine top problem's ideal transcript is the canonical uniform transcript
sampler. -/
theorem topUniformDistr_evalDist_eq_uniformSample
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    evalDist (LearningWithErrors.uniformDistr
        (topRGSWCoefficientProblem exponent degree errorSampler)) =
      evalDist ($ᵗ (Transcript exponent degree)) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  rw [← TopWeightSecurity.map_topRGSWRingUniformDistr_eq_coefficientUniformDistr]
  rw [TopWeightSecurity.topRGSWRingUniformDistr_eq_uniformSample]
  simpa [map_eq_bind_pure_comp] using
    (evalDist_map_bijective_uniform_cross
      (α := RLWE.ModuleSample (2 ^ (exponent + 1)) (degree + 1) 1
          (TGSW.rowCount 1 1) ×
        RLWE.ModuleOutput (2 ^ (exponent + 1)) (degree + 1)
          (TGSW.rowCount 1 1))
      (β := Transcript exponent degree)
      (CoefficientStructuredLWE.transcriptEquiv
        (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1))
      (CoefficientStructuredLWE.transcriptEquiv
        (2 ^ (exponent + 1)) (degree + 1) 1
          (TGSW.rowCount 1 1)).bijective)

/-- The leakage-RLWE ideal game restores exactly the complete coefficient-affine top-row ideal
game.  Secret-dependent addition of the leaked message preserves the uniform transcript. -/
theorem leakageUniformGame_evalDist_eq_topGame1
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (adversary : LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent degree errorSampler)) :
    evalDist (LWE.AuxiliaryInput.uniformGame
        (leakageProblem exponent degree errorSampler)
        (leakageContinuation adversary)) =
      evalDist (LearningWithErrors.game1
        (topRGSWCoefficientProblem exponent degree errorSampler) adversary) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  let Secrets := sampleRingSecret 1 (degree + 1)
  let Uniform : ProbComp (Transcript exponent degree) :=
    $ᵗ (Transcript exponent degree)
  let Ideal := Uniform >>= adversary
  have hfixed (ringSecret : RingBinarySecret 1 (degree + 1)) :
      evalDist (Uniform >>= fun transcript ↦
          adversary (addLeakage (topLeakage exponent degree ringSecret) transcript)) =
        evalDist Ideal := by
    have htranslated :
        evalDist
            (addLeakage (topLeakage exponent degree ringSecret) <$> Uniform) =
          evalDist Uniform := by
      exact evalDist_map_bijective_uniform_cross
        (α := Transcript exponent degree)
        (β := Transcript exponent degree)
        (addLeakage (topLeakage exponent degree ringSecret))
        (addLeakage_bijective (topLeakage exponent degree ringSecret))
    rw [show (Uniform >>= fun transcript ↦
          adversary (addLeakage (topLeakage exponent degree ringSecret) transcript)) =
        ((addLeakage (topLeakage exponent degree ringSecret) <$> Uniform) >>=
          adversary) by simp]
    rw [evalDist_bind, htranslated, ← evalDist_bind]
  have hAuxiliary :
      evalDist (LWE.AuxiliaryInput.uniformGame
          (leakageProblem exponent degree errorSampler)
          (leakageContinuation adversary)) = evalDist Ideal := by
    have hsecrets : Pr[⊥ | Secrets] = 0 := by
      simp [Secrets]
    calc
      _ = evalDist (Secrets >>= fun ringSecret ↦
          Uniform >>= fun transcript ↦
            adversary
              (addLeakage (topLeakage exponent degree ringSecret) transcript)) := by
        rfl
      _ = evalDist (Secrets >>= fun _ringSecret ↦ Ideal) := by
        apply evalDist_bind_congr'
        exact hfixed
      _ = evalDist Ideal :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          Secrets hsecrets Ideal
  rw [hAuxiliary]
  rw [LearningWithErrors.game1]
  exact (FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (topUniformDistr_evalDist_eq_uniformSample exponent degree errorSampler)
    adversary).symm

/-- The complete coefficient-affine top-row advantage is exactly ordinary binary-secret RLWE
with the structured top-square value exposed as auxiliary leakage. -/
theorem topCoefficientAdvantage_eq_leakageRLWE
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (adversary : LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent degree errorSampler)) :
    LearningWithErrors.advantage
        (topRGSWCoefficientProblem exponent degree errorSampler) adversary =
      LWE.AuxiliaryInput.circularLweAdvantage
        (leakageProblem exponent degree errorSampler)
        (leakageContinuation adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold LWE.AuxiliaryInput.circularLweAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (leakageRealGame_evalDist_eq_topGame0
        exponent degree errorSampler adversary) true,
    evalDist_ext_iff.mp
      (leakageUniformGame_evalDist_eq_topGame1
        exponent degree errorSampler adversary) true]

/-- The genuine unstripped highest-weight `RGSW_S(-S)` circular term is exactly the named
leakage-resilient RLWE advantage. -/
theorem nativeCircularLweAdvantage_eq_leakageRLWE
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (distinguisher : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1) :
    Native.RingSquareRGSW.circularLweAdvantage
        (2 ^ (exponent + 1)) (degree + 1) 1 errorSampler
        (topGadget exponent degree) distinguisher =
      LWE.AuxiliaryInput.circularLweAdvantage
        (leakageProblem exponent degree errorSampler)
        (leakageContinuation (errorSampler := errorSampler)
          (TopWeightSecurity.coefficientAdversary (errorSampler := errorSampler)
            (Native.RingSquareRGSW.restoreDistinguisher
              (topGadget exponent degree) distinguisher))) := by
  rw [TopWeightSecurity.circularLweAdvantage_eq_coefficientAdvantage,
    topCoefficientAdvantage_eq_leakageRLWE]

/-- The genuine top-weight KDM advantage is bounded by one leakage-resilient ordinary-RLWE term
and the ordinary two-row zero-message RLWE term.  Both use the original narrow error sampler. -/
theorem kdmAdvantage_le_leakageRLWE_add_ordinaryRLWE
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (distinguisher : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1) :
    Native.RingSquareRGSW.kdmAdvantage
        (2 ^ (exponent + 1)) (degree + 1) 1 errorSampler
        (topGadget exponent degree) distinguisher ≤
      LWE.AuxiliaryInput.circularLweAdvantage
          (leakageProblem exponent degree errorSampler)
          (leakageContinuation (errorSampler := errorSampler)
            (TopWeightSecurity.coefficientAdversary (errorSampler := errorSampler)
              (Native.RingSquareRGSW.restoreDistinguisher
                (topGadget exponent degree) distinguisher))) +
        LearningWithErrors.advantage
          (CoefficientStructuredLWE.ringProblem
            (2 ^ (exponent + 1)) (degree + 1) 1
            (TGSW.rowCount 1 1) errorSampler)
          (TopWeightSecurity.zeroRLWEAdversary distinguisher) := by
  simpa only [topCoefficientAdvantage_eq_leakageRLWE] using
    TopWeightSecurity.kdmAdvantage_le_coefficientAffine_add_ordinaryRLWE
      exponent degree errorSampler distinguisher

/-- Concrete leakage-resilient RLWE hardness for the exact top-square auxiliary value. -/
def LeakageRLWEHardAgainst
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (allowed : LWE.AuxiliaryInput.Continuation
      (RingBinarySecret 1 (degree + 1))
      (Transcript exponent degree) (Leakage exponent degree) → Prop)
    (bound : ℝ) : Prop :=
  LWE.AuxiliaryInput.CircularLWEHardAgainst
    (leakageProblem exponent degree errorSampler) allowed bound

/-- **Highest two-adic native KDM security from leakage-resilient RLWE.**  Hardness of ordinary
binary-secret RLWE with `2^k S^2` exposed, together with ordinary two-row binary-secret RLWE,
implies security of the genuine one-level `RGSW_S(-S)` ciphertext.  No error is changed. -/
theorem kdmHardAgainst_of_leakageRLWE_and_binarySecretRLWE
    (exponent degree : ℕ)
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (nativeAllowed : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1 → Prop)
    (leakageAllowed : LWE.AuxiliaryInput.Continuation
      (RingBinarySecret 1 (degree + 1))
      (Transcript exponent degree) (Leakage exponent degree) → Prop)
    (ordinaryAllowed : LearningWithErrors.Adversary
      (CoefficientStructuredLWE.ringProblem
        (2 ^ (exponent + 1)) (degree + 1) 1
        (TGSW.rowCount 1 1) errorSampler) → Prop)
    (leakageBound ordinaryBound : ℝ)
    (hLeakageClosed : ∀ distinguisher, nativeAllowed distinguisher →
      leakageAllowed
        (leakageContinuation (errorSampler := errorSampler)
          (TopWeightSecurity.coefficientAdversary (errorSampler := errorSampler)
            (Native.RingSquareRGSW.restoreDistinguisher
              (topGadget exponent degree) distinguisher))))
    (hOrdinaryClosed : ∀ distinguisher, nativeAllowed distinguisher →
      ordinaryAllowed (TopWeightSecurity.zeroRLWEAdversary distinguisher))
    (hLeakage : LeakageRLWEHardAgainst exponent degree errorSampler
      leakageAllowed leakageBound)
    (hOrdinary : TopWeightSecurity.BinarySecretRLWEHardAgainst
      exponent degree errorSampler ordinaryAllowed ordinaryBound) :
    Native.RingSquareRGSW.KDMHardAgainst
      (2 ^ (exponent + 1)) (degree + 1) 1 errorSampler
      (topGadget exponent degree) nativeAllowed
      (leakageBound + ordinaryBound) := by
  intro distinguisher hallowed
  exact (kdmAdvantage_le_leakageRLWE_add_ordinaryRLWE
    exponent degree errorSampler distinguisher).trans
      (add_le_add
        (hLeakage _ (hLeakageClosed distinguisher hallowed))
        (hOrdinary _ (hOrdinaryClosed distinguisher hallowed)))

/-- Centered-binomial specialization of the leakage-resilient theorem.  The leakage-RLWE,
ordinary-RLWE, and native KDM games all use the same width `eta`. -/
theorem centeredBinomial_kdmHardAgainst_of_leakageRLWE_and_binarySecretRLWE
    (exponent degree eta : ℕ)
    (nativeAllowed : Native.RingSquareRGSW.Distinguisher
      (2 ^ (exponent + 1)) (degree + 1) 1 → Prop)
    (leakageAllowed : LWE.AuxiliaryInput.Continuation
      (RingBinarySecret 1 (degree + 1))
      (Transcript exponent degree) (Leakage exponent degree) → Prop)
    (ordinaryAllowed : LearningWithErrors.Adversary
      (CoefficientStructuredLWE.ringProblem
        (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1)
        (RLWE.CenteredBinomial.sampler
          (2 ^ (exponent + 1)) (degree + 1) eta)) → Prop)
    (leakageBound ordinaryBound : ℝ)
    (hLeakageClosed : ∀ distinguisher, nativeAllowed distinguisher →
      leakageAllowed
        (leakageContinuation
          (errorSampler := RLWE.CenteredBinomial.sampler
            (2 ^ (exponent + 1)) (degree + 1) eta)
          (TopWeightSecurity.coefficientAdversary
            (errorSampler := RLWE.CenteredBinomial.sampler
              (2 ^ (exponent + 1)) (degree + 1) eta)
            (Native.RingSquareRGSW.restoreDistinguisher
              (topGadget exponent degree) distinguisher))))
    (hOrdinaryClosed : ∀ distinguisher, nativeAllowed distinguisher →
      ordinaryAllowed (TopWeightSecurity.zeroRLWEAdversary distinguisher))
    (hLeakage : LeakageRLWEHardAgainst exponent degree
      (RLWE.CenteredBinomial.sampler
        (2 ^ (exponent + 1)) (degree + 1) eta)
      leakageAllowed leakageBound)
    (hOrdinary : TopWeightSecurity.BinarySecretRLWEHardAgainst
      exponent degree
      (RLWE.CenteredBinomial.sampler
        (2 ^ (exponent + 1)) (degree + 1) eta)
      ordinaryAllowed ordinaryBound) :
    Native.RingSquareRGSW.KDMHardAgainst
      (2 ^ (exponent + 1)) (degree + 1) 1
      (RLWE.CenteredBinomial.sampler
        (2 ^ (exponent + 1)) (degree + 1) eta)
      (topGadget exponent degree) nativeAllowed
      (leakageBound + ordinaryBound) := by
  exact kdmHardAgainst_of_leakageRLWE_and_binarySecretRLWE
    exponent degree
    (RLWE.CenteredBinomial.sampler
      (2 ^ (exponent + 1)) (degree + 1) eta)
    nativeAllowed leakageAllowed ordinaryAllowed leakageBound ordinaryBound
    hLeakageClosed hOrdinaryClosed hLeakage hOrdinary

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightLeakage
