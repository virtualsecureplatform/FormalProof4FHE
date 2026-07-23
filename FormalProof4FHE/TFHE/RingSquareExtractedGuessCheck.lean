/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.KeySwitchCandidateRandomization
import FormalProof4FHE.TFHE.RingSquareSecretRandomization
import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveReduction

/-!
# Coefficient Guess and Check for `RGSW_S(-S)` via Sample Extraction

The direct rank-one ring candidate test can handle at most a two-element unit-separated secret
space, and the direct coefficient-pad action is impossible.  Sample extraction bypasses both
obstructions without changing the error distribution.  One positive-degree rank-one RLWE row
maps to one ordinary scalar-LWE row under the complete coefficient vector of the ring secret;
the public challenge map is an equivalence and the scalar error is the constant coefficient of
the ring error.

Once the ordinary scalar rows are exposed, the standard binary coordinate transform applies:
add a fresh vector to one selected challenge row and add the candidate bit times that vector to
the bodies.  The correct candidate preserves the real scalar-LWE law exactly; the wrong bit has
difference `+1` or `-1` and makes the complete scalar transcript exactly uniform.  The genuine
`RGSW_S(-S)` auxiliary ciphertext is retained throughout.

This closes the coefficient guess/check algebra for all coefficients of a binary rank-one ring
secret.  It is a search-to-decision layer, not yet a proof that the resulting circular search
problem follows from ordinary RLWE: a search solver still receives the genuine circular RGSW
auxiliary object.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.ExtractedGuessCheck

open FormalProof4FHE.TFHE
open FormalProof4FHE.TFHE.Native.KeySwitchCandidateRandomization
open FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveReduction

noncomputable section

/-- Positive-degree production-independent ring carrier used by sample extraction. -/
abbrev Ring (q degree : ℕ) := RLWE.Rq q (degree + 1)

/-- Binary rank-one ring secret. -/
abbrev BinaryRingSecret (degree : ℕ) := RingBinarySecret 1 (degree + 1)

/-- Dimension of the complete coefficient-extracted rank-one secret. -/
abbrev scalarDimension (degree : ℕ) := 1 * (degree + 1)

/-- Scalar-LWE test batch obtained from rank-one ring rows by sample extraction. -/
abbrev ExtractedTestBatch (q degree samples : ℕ) :=
  TLWE.BatchCiphertext (ZMod q) (scalarDimension degree) samples

/-- Complete restricted circular view with a genuine RGSW auxiliary and coefficient-extracted
ordinary test rows. -/
abbrev ExtractedCircularView (q degree levels samples : ℕ) :=
  TGSW.Ciphertext (Ring q degree) 1 levels ×
    ExtractedTestBatch q degree samples

/-- Real fixed-binary-secret view: genuine `RGSW_S(-S)` plus ordinary scalar-LWE rows under
all coefficients of the same ring secret. -/
def fixedSecretRealViewSampler
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (secret : BinaryRingSecret degree) (gadget : Fin levels → Ring q degree) :
    ProbComp (ExtractedCircularView q degree levels samples) := do
  let auxiliary ← TGSW.encrypt 1 levels auxiliaryErrorSampler
    (embedRingSecret q secret) gadget (-(embedRingSecret q secret 0))
  let testRows ← TLWE.batchEncrypt (scalarDimension degree) samples
    (extractedErrorSampler testRingErrorSampler)
    (embedBinarySecret (keyExtract secret)) 0
  return (auxiliary, testRows)

/-- Uniform-test fixed-secret branch retaining the genuine circular auxiliary. -/
def fixedSecretUniformViewSampler
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler : ProbComp (Ring q degree))
    (secret : BinaryRingSecret degree) (gadget : Fin levels → Ring q degree) :
    ProbComp (ExtractedCircularView q degree levels samples) := do
  let auxiliary ← TGSW.encrypt 1 levels auxiliaryErrorSampler
    (embedRingSecret q secret) gadget (-(embedRingSecret q secret 0))
  let testRows ← $ᵗ ExtractedTestBatch q degree samples
  return (auxiliary, testRows)

/-- Candidate transform on a supplied complete view: retain the RGSW auxiliary and randomize
one selected coefficient row of the scalar-LWE test batch. -/
def randomizeView
    {q degree levels samples : ℕ} [NeZero q]
    (coordinate : Fin (scalarDimension degree)) (candidate : Bool)
    (view : ExtractedCircularView q degree levels samples) :
    ProbComp (ExtractedCircularView q degree levels samples) := do
  let shift ← $ᵗ (Fin samples → ZMod q)
  return (view.1, randomizeBatch coordinate candidate shift view.2)

/-- Operational candidate experiment on a freshly sampled real fixed-secret view. -/
def fixedSecretCandidateViewSampler
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (secret : BinaryRingSecret degree) (gadget : Fin levels → Ring q degree)
    (coordinate : Fin (scalarDimension degree)) (candidate : Bool) :
    ProbComp (ExtractedCircularView q degree levels samples) := do
  let view ← fixedSecretRealViewSampler q degree levels samples
    auxiliaryErrorSampler testRingErrorSampler secret gadget
  randomizeView coordinate candidate view

/-- The operational candidate experiment separates into an independent RGSW sampler and the
standard scalar-LWE coordinate-randomization experiment. -/
theorem fixedSecretCandidateViewSampler_normalForm
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (secret : BinaryRingSecret degree) (gadget : Fin levels → Ring q degree)
    (coordinate : Fin (scalarDimension degree)) (candidate : Bool) :
    evalDist (fixedSecretCandidateViewSampler q degree levels samples
      auxiliaryErrorSampler testRingErrorSampler secret gadget coordinate candidate) =
      evalDist (TGSW.encrypt 1 levels auxiliaryErrorSampler
          (embedRingSecret q secret) gadget (-(embedRingSecret q secret 0)) >>= fun auxiliary ↦
        randomizeEncryption (extractedErrorSampler testRingErrorSampler)
            (keyExtract secret) coordinate candidate 0 >>= fun testRows ↦
          pure (auxiliary, testRows)) := by
  simp [fixedSecretCandidateViewSampler, fixedSecretRealViewSampler,
    randomizeView, randomizeEncryption, monad_norm]

/-- Mapping a never-failing ring-error sampler to its constant coefficient remains
never-failing. -/
theorem probFailure_extractedErrorSampler_eq_zero
    {q degree : ℕ}
    (testRingErrorSampler : ProbComp (Ring q degree))
    (herror : Pr[⊥ | testRingErrorSampler] = 0) :
    Pr[⊥ | extractedErrorSampler testRingErrorSampler] = 0 := by
  simpa only [extractedErrorSampler, probFailure_map] using herror

/-! ## Exact bridge from rank-one RLWE test rows -/

/-- Coordinate description of sample extraction on a complete rank-one batch. -/
@[simp]
theorem extractTape_pair
    {q degree samples : ℕ}
    (challenge : Matrix (Fin 1) (Fin samples) (Ring q degree))
    (output : Fin samples → Ring q degree) :
    extractTape (challenge, output) =
      (extractedChallengeEquiv q degree 1 samples challenge,
        extractErrors output) := by
  rfl

/-- Sample-extracting a fresh rank-one RLWE batch under a binary ring secret gives exactly the
ordinary scalar-LWE batch used above, with no loss and with the constant-coefficient image of
the same ring-error sampler. -/
theorem extractTape_batchEncrypt_evalDist
    (q degree samples : ℕ) [NeZero q]
    (testRingErrorSampler : ProbComp (Ring q degree))
    (secret : BinaryRingSecret degree) :
    evalDist (extractTape <$>
      TLWE.batchEncrypt 1 samples testRingErrorSampler
        (embedRingSecret q secret) 0) =
      evalDist (TLWE.batchEncrypt (scalarDimension degree) samples
        (extractedErrorSampler testRingErrorSampler)
        (embedBinarySecret (keyExtract secret)) 0) := by
  let ringChallenges : ProbComp
      (Matrix (Fin 1) (Fin samples) (Ring q degree)) :=
    $ᵗ Matrix (Fin 1) (Fin samples) (Ring q degree)
  let scalarChallenges : ProbComp
      (Matrix (Fin (scalarDimension degree)) (Fin samples) (ZMod q)) :=
    $ᵗ Matrix (Fin (scalarDimension degree)) (Fin samples) (ZMod q)
  let ringErrors := ProbComp.sampleIID samples testRingErrorSampler
  let scalarErrors :=
    ProbComp.sampleIID samples (extractedErrorSampler testRingErrorSampler)
  let finish := fun
      (challenge : Matrix (Fin (scalarDimension degree)) (Fin samples) (ZMod q))
      (error : Fin samples → ZMod q) ↦
    (pure (TLWE.batchAssemble (embedBinarySecret (keyExtract secret))
      challenge 0 error) : ProbComp (ExtractedTestBatch q degree samples))
  have hchallenge :
      evalDist (extractedChallengeEquiv q degree 1 samples <$> ringChallenges) =
        evalDist scalarChallenges := by
    simpa only [ringChallenges, scalarChallenges, scalarDimension] using
      (extractedChallengeEquiv_uniform_evalDist q degree 1 samples)
  have herror : evalDist (extractErrors <$> ringErrors) = evalDist scalarErrors := by
    simpa only [ringErrors, scalarErrors] using
      (extractErrors_sampleIID_evalDist (samples := samples) testRingErrorSampler)
  calc
    evalDist (extractTape <$>
        TLWE.batchEncrypt 1 samples testRingErrorSampler
          (embedRingSecret q secret) 0) =
      evalDist (ringChallenges >>= fun challenge ↦
        ringErrors >>= fun error ↦
          finish (extractedChallengeEquiv q degree 1 samples challenge)
            (extractErrors error)) := by
        rw [show TLWE.batchEncrypt 1 samples testRingErrorSampler
            (embedRingSecret q secret) 0 =
          (ringChallenges >>= fun challenge ↦
            ringErrors >>= fun error ↦
              pure (TLWE.batchAssemble (embedRingSecret q secret)
                challenge 0 error)) by
            simp [TLWE.batchEncrypt, ringChallenges, ringErrors, monad_norm]]
        simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc,
          pure_bind]
        refine evalDist_bind_congr' ringChallenges fun challenge ↦ ?_
        refine evalDist_bind_congr' ringErrors fun error ↦ ?_
        simpa only [finish] using congrArg evalDist (congrArg pure
          (extractTape_batchAssemble_zero secret challenge error))
    _ = evalDist ((extractedChallengeEquiv q degree 1 samples <$>
          ringChallenges) >>= fun challenge ↦
        (extractErrors <$> ringErrors) >>= fun error ↦ finish challenge error) := by
      simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (scalarChallenges >>= fun challenge ↦
        (extractErrors <$> ringErrors) >>= fun error ↦ finish challenge error) := by
      rw [evalDist_bind, hchallenge, ← evalDist_bind]
    _ = evalDist (scalarChallenges >>= fun challenge ↦
        scalarErrors >>= fun error ↦ finish challenge error) := by
      refine evalDist_bind_congr' scalarChallenges fun challenge ↦ ?_
      rw [evalDist_bind, herror, ← evalDist_bind]
    _ = evalDist (TLWE.batchEncrypt (scalarDimension degree) samples
        (extractedErrorSampler testRingErrorSampler)
        (embedBinarySecret (keyExtract secret)) 0) := by
      simp [TLWE.batchEncrypt, scalarChallenges, scalarErrors, finish, monad_norm]

/-- Sample extraction maps a fully uniform rank-one ring transcript to a fully uniform scalar
transcript.  Although it discards nonconstant body coefficients, those discarded coordinates
form an independent uniform fiber. -/
theorem extractTape_uniform_evalDist
    (q degree samples : ℕ) [NeZero q] :
    evalDist (extractTape <$>
      ($ᵗ TLWE.BatchCiphertext (Ring q degree) 1 samples)) =
      evalDist ($ᵗ ExtractedTestBatch q degree samples) := by
  let ringChallenges : ProbComp
      (Matrix (Fin 1) (Fin samples) (Ring q degree)) :=
    $ᵗ Matrix (Fin 1) (Fin samples) (Ring q degree)
  let ringOutputs : ProbComp (Fin samples → Ring q degree) :=
    $ᵗ (Fin samples → Ring q degree)
  let scalarChallenges : ProbComp
      (Matrix (Fin (scalarDimension degree)) (Fin samples) (ZMod q)) :=
    $ᵗ Matrix (Fin (scalarDimension degree)) (Fin samples) (ZMod q)
  let scalarOutputs : ProbComp (Fin samples → ZMod q) :=
    $ᵗ (Fin samples → ZMod q)
  have hchallenge :
      evalDist (extractedChallengeEquiv q degree 1 samples <$> ringChallenges) =
        evalDist scalarChallenges := by
    simpa only [ringChallenges, scalarChallenges, scalarDimension] using
      (extractedChallengeEquiv_uniform_evalDist q degree 1 samples)
  have houtput : evalDist (extractErrors <$> ringOutputs) =
      evalDist scalarOutputs := by
    simpa only [ringOutputs, scalarOutputs] using
      (extractErrors_uniform_evalDist q degree samples)
  have ringProduct :
      ($ᵗ TLWE.BatchCiphertext (Ring q degree) 1 samples :
        ProbComp (TLWE.BatchCiphertext (Ring q degree) 1 samples)) =
      Prod.mk <$> ringChallenges <*> ringOutputs := rfl
  have scalarProduct :
      ($ᵗ ExtractedTestBatch q degree samples :
        ProbComp (ExtractedTestBatch q degree samples)) =
      Prod.mk <$> scalarChallenges <*> scalarOutputs := rfl
  rw [ringProduct, scalarProduct]
  simp only [seq_eq_bind_map, map_eq_bind_pure_comp, Function.comp_apply,
    bind_assoc, pure_bind]
  calc
    evalDist (ringChallenges >>= fun challenge ↦
        ringOutputs >>= fun output ↦
          pure (extractTape (challenge, output))) =
      evalDist ((extractedChallengeEquiv q degree 1 samples <$>
          ringChallenges) >>= fun challenge ↦
        (extractErrors <$> ringOutputs) >>= fun output ↦
          pure (challenge, output)) := by
        simp [extractTape_pair, map_eq_bind_pure_comp, bind_assoc, monad_norm]
    _ = evalDist (scalarChallenges >>= fun challenge ↦
        (extractErrors <$> ringOutputs) >>= fun output ↦
          pure (challenge, output)) := by
      rw [evalDist_bind, hchallenge, ← evalDist_bind]
    _ = evalDist (scalarChallenges >>= fun challenge ↦
        scalarOutputs >>= fun output ↦ pure (challenge, output)) := by
      refine evalDist_bind_congr' scalarChallenges fun challenge ↦ ?_
      rw [evalDist_bind, houtput, ← evalDist_bind]
    _ = _ := rfl

/-! ## Complete paired-view extraction -/

/-- Rank-one ring test rows before sample extraction. -/
abbrev RingTestBatch (q degree samples : ℕ) :=
  TLWE.BatchCiphertext (Ring q degree) 1 samples

/-- Genuine circular RGSW auxiliary paired with rank-one ring test rows. -/
abbrev RingTestCircularView (q degree levels samples : ℕ) :=
  TGSW.Ciphertext (Ring q degree) 1 levels × RingTestBatch q degree samples

/-- Deterministically sample-extract only the rank-one test component of the paired view. -/
def extractRingTestView
    {q degree levels samples : ℕ} :
    RingTestCircularView q degree levels samples →
      ExtractedCircularView q degree levels samples :=
  fun view ↦ (view.1, extractTape view.2)

/-- Genuine `RGSW_S(-S)` paired with fresh rank-one zero-message RLWE rows under the same
binary ring secret. -/
def fixedSecretRingRealViewSampler
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (secret : BinaryRingSecret degree) (gadget : Fin levels → Ring q degree) :
    ProbComp (RingTestCircularView q degree levels samples) := do
  let auxiliary ← TGSW.encrypt 1 levels auxiliaryErrorSampler
    (embedRingSecret q secret) gadget (-(embedRingSecret q secret 0))
  let testRows ← TLWE.batchEncrypt 1 samples testRingErrorSampler
    (embedRingSecret q secret) 0
  return (auxiliary, testRows)

/-- The same genuine circular auxiliary paired with uniform rank-one ring test rows. -/
def fixedSecretRingUniformViewSampler
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler : ProbComp (Ring q degree))
    (secret : BinaryRingSecret degree) (gadget : Fin levels → Ring q degree) :
    ProbComp (RingTestCircularView q degree levels samples) := do
  let auxiliary ← TGSW.encrypt 1 levels auxiliaryErrorSampler
    (embedRingSecret q secret) gadget (-(embedRingSecret q secret 0))
  let testRows ← $ᵗ RingTestBatch q degree samples
  return (auxiliary, testRows)

/-- Deterministic sample extraction maps the complete genuine-RGSW/real-RLWE view exactly to
the scalar-test real view used by coefficient guess/check. -/
theorem extractRingTestView_fixedSecretRingReal_evalDist
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (secret : BinaryRingSecret degree) (gadget : Fin levels → Ring q degree) :
    evalDist (extractRingTestView <$>
      fixedSecretRingRealViewSampler q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler secret gadget) =
      evalDist (fixedSecretRealViewSampler q degree levels samples auxiliaryErrorSampler
        testRingErrorSampler secret gadget) := by
  unfold fixedSecretRingRealViewSampler fixedSecretRealViewSampler
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
    extractRingTestView]
  refine evalDist_bind_congr'
    (TGSW.encrypt 1 levels auxiliaryErrorSampler (embedRingSecret q secret) gadget
      (-(embedRingSecret q secret 0))) fun auxiliary ↦ ?_
  have h := extractTape_batchEncrypt_evalDist q degree samples testRingErrorSampler secret
  simpa only [evalDist_map, evalDist_bind, evalDist_pure, map_eq_bind_pure_comp,
    Function.comp_apply, Function.comp_def, bind_assoc, pure_bind] using congrArg
      (fun distribution ↦ (fun testRows ↦ (auxiliary, testRows)) <$> distribution) h

/-- Deterministic sample extraction maps the paired uniform ring transcript exactly to the
uniform scalar-test endpoint while retaining the same circular auxiliary. -/
theorem extractRingTestView_fixedSecretRingUniform_evalDist
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler : ProbComp (Ring q degree))
    (secret : BinaryRingSecret degree) (gadget : Fin levels → Ring q degree) :
    evalDist (extractRingTestView <$>
      fixedSecretRingUniformViewSampler q degree levels samples auxiliaryErrorSampler
        secret gadget) =
      evalDist (fixedSecretUniformViewSampler q degree levels samples auxiliaryErrorSampler
        secret gadget) := by
  unfold fixedSecretRingUniformViewSampler fixedSecretUniformViewSampler
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
    extractRingTestView]
  refine evalDist_bind_congr'
    (TGSW.encrypt 1 levels auxiliaryErrorSampler (embedRingSecret q secret) gadget
      (-(embedRingSecret q secret 0))) fun auxiliary ↦ ?_
  have h := extractTape_uniform_evalDist q degree samples
  simpa only [evalDist_map, evalDist_bind, evalDist_pure, map_eq_bind_pure_comp,
    Function.comp_apply, Function.comp_def, bind_assoc, pure_bind] using congrArg
      (fun distribution ↦ (fun testRows ↦ (auxiliary, testRows)) <$> distribution) h

/-- **Correct coefficient candidate.**  Submitting the hidden bit at any extracted coordinate
leaves the complete genuine-RGSW/real-scalar-LWE view unchanged exactly. -/
theorem fixedSecretCandidateViewSampler_correct_evalDist
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (secret : BinaryRingSecret degree) (gadget : Fin levels → Ring q degree)
    (coordinate : Fin (scalarDimension degree)) :
    evalDist (fixedSecretCandidateViewSampler q degree levels samples
      auxiliaryErrorSampler testRingErrorSampler secret gadget coordinate
        (keyExtract secret coordinate)) =
      evalDist (fixedSecretRealViewSampler q degree levels samples
        auxiliaryErrorSampler testRingErrorSampler secret gadget) := by
  rw [fixedSecretCandidateViewSampler_normalForm]
  unfold fixedSecretRealViewSampler
  refine evalDist_bind_congr'
    (TGSW.encrypt 1 levels auxiliaryErrorSampler
      (embedRingSecret q secret) gadget (-(embedRingSecret q secret 0)))
    fun auxiliary ↦ ?_
  rw [evalDist_bind,
    randomizeEncryption_correct_evalDist
      (extractedErrorSampler testRingErrorSampler) (keyExtract secret) coordinate 0,
    ← evalDist_bind]

/-- **Wrong coefficient candidate.**  Submitting the opposite bit replaces the complete
scalar-LWE test batch by an independent uniform transcript while retaining the genuine
`RGSW_S(-S)` auxiliary object. -/
theorem fixedSecretCandidateViewSampler_wrong_evalDist
    (q degree levels samples : ℕ) [NeZero q]
    (auxiliaryErrorSampler testRingErrorSampler : ProbComp (Ring q degree))
    (htestError : Pr[⊥ | testRingErrorSampler] = 0)
    (secret : BinaryRingSecret degree) (gadget : Fin levels → Ring q degree)
    (coordinate : Fin (scalarDimension degree)) :
    evalDist (fixedSecretCandidateViewSampler q degree levels samples
      auxiliaryErrorSampler testRingErrorSampler secret gadget coordinate
        (!(keyExtract secret coordinate))) =
      evalDist (fixedSecretUniformViewSampler q degree levels samples
        auxiliaryErrorSampler secret gadget) := by
  rw [fixedSecretCandidateViewSampler_normalForm]
  unfold fixedSecretUniformViewSampler
  refine evalDist_bind_congr'
    (TGSW.encrypt 1 levels auxiliaryErrorSampler
      (embedRingSecret q secret) gadget (-(embedRingSecret q secret 0)))
    fun auxiliary ↦ ?_
  rw [evalDist_bind,
    randomizeEncryption_wrong_evalDist
      (extractedErrorSampler testRingErrorSampler)
      (probFailure_extractedErrorSampler_eq_zero testRingErrorSampler htestError)
      (keyExtract secret) coordinate (!(keyExtract secret coordinate)) (by simp) 0,
    ← evalDist_bind]

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.ExtractedGuessCheck
