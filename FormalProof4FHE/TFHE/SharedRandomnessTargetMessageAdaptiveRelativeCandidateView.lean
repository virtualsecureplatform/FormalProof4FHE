/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveUniformTapeRandomization
import FormalProof4FHE.Probability.BinaryGuessCheck

set_option autoImplicit false

/-!
# Pointwise Relative Candidate Views for Direct Adaptive TFHE CircLWE

Candidate tape randomization and fresh-secret relative/anchor randomization are now composed.
For every fixed hidden nested key and every extracted target-key coordinate:

* the correct candidate is close to the fresh wide real public view; and
* the wrong candidate is close to the fresh wide uniform-tape public view.

Both bounds use the same explicit evaluator budget.  This is the pointwise property needed by the
PKC guess-and-check argument; it avoids assuming that an average decision gap is present for every
fixed secret.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE

noncomputable section

open FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision

namespace RelativeEvaluationMaterialEvaluator

/-- Apply coordinate-candidate tape randomization, sample a complete relative/anchor mask, and
run the public shifted evaluator. -/
def evaluateCandidateView
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1)))
    (candidate : Bool)
    (view : View q (degree + 1) 1 suffixRank levels queryCount) :
    ProbComp (View q (degree + 1) 1 suffixRank levels queryCount) := do
  let candidateView ← randomizeTargetTapeCandidate coordinate candidate view
  let mask ← $ᵗ (RelativeNestedMask suffixRank degree × Bool)
  evaluator.evaluateRelativeThenGlobal mask candidateView

/-- For a correct candidate, the complete pointwise pipeline is the public-view marginal of the
checked real-branch fresh-secret randomizer. -/
theorem evaluateCandidateView_correct_evalDist
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (secret : Secret 1 suffixRank (degree + 1))
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    evalDist
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
            gadget secret >>=
          evaluator.evaluateCandidateView coordinate
            (targetMessages secret.1 secret.2 coordinate)) =
      evalDist
        (Prod.snd <$>
          (evaluator.toRelativeThenGlobalViewRandomization
            (queryCount := queryCount) inputErrorSampler hextensionSymmetric).randomizedView
              secret) := by
  let realView := sampleRealView q (degree + 1) 1 suffixRank levels queryCount
    narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget secret
  let masks : ProbComp (RelativeNestedMask suffixRank degree × Bool) :=
    $ᵗ (RelativeNestedMask suffixRank degree × Bool)
  let correctCandidate := targetMessages secret.1 secret.2 coordinate
  have hcorrect :
      evalDist (realView >>= randomizeTargetTapeCandidate coordinate correctCandidate) =
        evalDist realView := by
    exact randomizeTargetTapeCandidate_correct_evalDist
      narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
      gadget secret coordinate
  calc
    _ = evalDist (masks >>= fun mask ↦
        (realView >>= randomizeTargetTapeCandidate coordinate correctCandidate) >>=
          evaluator.evaluateRelativeThenGlobal mask) := by
      unfold evaluateCandidateView
      simpa only [realView, masks, correctCandidate, bind_assoc] using
        (OracleComp.DeferredSampling.evalDist_bind_comm
          (realView >>= randomizeTargetTapeCandidate coordinate correctCandidate)
          masks (fun candidateView mask ↦
            evaluator.evaluateRelativeThenGlobal mask candidateView))
    _ = evalDist (masks >>= fun mask ↦
        realView >>= evaluator.evaluateRelativeThenGlobal mask) := by
      refine evalDist_bind_congr' masks fun mask ↦ ?_
      rw [evalDist_bind, hcorrect, ← evalDist_bind]
    _ = _ := by
      simp [ViewRandomization.randomizedView,
        toRelativeThenGlobalViewRandomization,
        realView, masks, map_eq_bind_pure_comp, bind_assoc, monad_norm]

/-- For a wrong candidate, the complete pointwise pipeline is the public-view marginal of the
checked uniform-tape fresh-secret randomizer. -/
theorem evaluateCandidateView_wrong_evalDist
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (secret : Secret 1 suffixRank (degree + 1))
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1)))
    (candidate : Bool)
    (hcandidate : candidate ≠ targetMessages secret.1 secret.2 coordinate) :
    evalDist
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
            gadget secret >>=
          evaluator.evaluateCandidateView coordinate candidate) =
      evalDist
        (Prod.snd <$>
          (evaluator.toUniformTapeViewRandomization
            (queryCount := queryCount) hextensionSymmetric).randomizedView secret) := by
  let realView := sampleRealView q (degree + 1) 1 suffixRank levels queryCount
    narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget secret
  let uniformView := sampleUniformTapeMaterialView q degree suffixRank levels queryCount
    narrowBootstrapErrorSampler narrowExtensionErrorSampler gadget secret
  let masks : ProbComp (RelativeNestedMask suffixRank degree × Bool) :=
    $ᵗ (RelativeNestedMask suffixRank degree × Bool)
  have hwrong :
      evalDist (realView >>= randomizeTargetTapeCandidate coordinate candidate) =
        evalDist uniformView := by
    exact randomizeTargetTapeCandidate_wrong_evalDist
      narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
      hInputError gadget secret coordinate candidate hcandidate
  calc
    _ = evalDist (masks >>= fun mask ↦
        (realView >>= randomizeTargetTapeCandidate coordinate candidate) >>=
          evaluator.evaluateRelativeThenGlobal mask) := by
      unfold evaluateCandidateView
      simpa only [realView, masks, bind_assoc] using
        (OracleComp.DeferredSampling.evalDist_bind_comm
          (realView >>= randomizeTargetTapeCandidate coordinate candidate)
          masks (fun candidateView mask ↦
            evaluator.evaluateRelativeThenGlobal mask candidateView))
    _ = evalDist (masks >>= fun mask ↦
        uniformView >>= evaluator.evaluateRelativeThenGlobal mask) := by
      refine evalDist_bind_congr' masks fun mask ↦ ?_
      rw [evalDist_bind, hwrong, ← evalDist_bind]
    _ = _ := by
      simp [ViewRandomization.randomizedView, toUniformTapeViewRandomization,
        uniformView, masks,
        map_eq_bind_pure_comp, bind_assoc, monad_norm]

/-- The public-view marginal of the real randomizer's fresh target is exactly the averaged wide
real decision view. -/
theorem freshWideRealView_snd_evalDist
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler) :
    evalDist
        (Prod.snd <$>
          (evaluator.toRelativeThenGlobalViewRandomization
            (queryCount := queryCount) inputErrorSampler hextensionSymmetric).freshWideView) =
      evalDist
        (sampleFreshRealPublicView q degree suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget) := by
  simp [ViewRandomization.freshWideView, toRelativeThenGlobalViewRandomization,
    sampleFreshRealPublicView, map_eq_bind_pure_comp, bind_assoc, monad_norm]

/-- The public-view marginal of the uniform randomizer's fresh target is exactly the averaged wide
uniform-tape decision view. -/
theorem freshWideUniformView_snd_evalDist
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler) :
    evalDist
        (Prod.snd <$>
          (evaluator.toUniformTapeViewRandomization
            (queryCount := queryCount) hextensionSymmetric).freshWideView) =
      evalDist
        (sampleFreshUniformTapePublicView q degree suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler gadget) := by
  simp [ViewRandomization.freshWideView, toUniformTapeViewRandomization,
    sampleFreshUniformTapePublicView, map_eq_bind_pure_comp, bind_assoc, monad_norm]

/-- Pointwise correct-candidate output is within the compiled evaluator error of the fresh wide
real public view. -/
theorem evaluateCandidateView_correct_tvDist_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (secret : Secret 1 suffixRank (degree + 1))
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    tvDist
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
            gadget secret >>=
          evaluator.evaluateCandidateView coordinate
            (targetMessages secret.1 secret.2 coordinate))
        (sampleFreshRealPublicView q degree suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget) ≤
      evaluator.error + globalComplementViewError
        (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler := by
  let compiler := evaluator.toRelativeThenGlobalViewRandomization
    (queryCount := queryCount) inputErrorSampler hextensionSymmetric
  have hmap := tvDist_map_le (m := ProbComp) Prod.snd
    (compiler.randomizedView secret) compiler.freshWideView
  have hcompiler := compiler.randomizedView_tvDist_freshWideView_le secret
  unfold tvDist at hmap hcompiler ⊢
  rw [evaluateCandidateView_correct_evalDist evaluator inputErrorSampler
    hextensionSymmetric secret coordinate]
  rw [← freshWideRealView_snd_evalDist evaluator inputErrorSampler hextensionSymmetric]
  simpa [compiler] using hmap.trans hcompiler

/-- Pointwise wrong-candidate output is within the same evaluator error of the fresh wide
uniform-tape public view. -/
theorem evaluateCandidateView_wrong_tvDist_le
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (secret : Secret 1 suffixRank (degree + 1))
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1)))
    (candidate : Bool)
    (hcandidate : candidate ≠ targetMessages secret.1 secret.2 coordinate) :
    tvDist
        (sampleRealView q (degree + 1) 1 suffixRank levels queryCount
            narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler
            gadget secret >>=
          evaluator.evaluateCandidateView coordinate candidate)
        (sampleFreshUniformTapePublicView q degree suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler gadget) ≤
      evaluator.error + globalComplementViewError
        (suffixRank := suffixRank) (levels := levels) wideBootstrapErrorSampler := by
  let compiler := evaluator.toUniformTapeViewRandomization
    (queryCount := queryCount) hextensionSymmetric
  have hmap := tvDist_map_le (m := ProbComp) Prod.snd
    (compiler.randomizedView secret) compiler.freshWideView
  have hcompiler := compiler.randomizedView_tvDist_freshWideView_le secret
  unfold tvDist at hmap hcompiler ⊢
  rw [evaluateCandidateView_wrong_evalDist evaluator inputErrorSampler hInputError
    hextensionSymmetric secret coordinate candidate hcandidate]
  rw [← freshWideUniformView_snd_evalDist evaluator hextensionSymmetric]
  simpa [compiler] using hmap.trans hcompiler

end RelativeEvaluationMaterialEvaluator

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE
