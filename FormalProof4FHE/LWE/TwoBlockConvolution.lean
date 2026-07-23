/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.TwoBlock

/-!
# Convolution Reduction for Heterogeneous Two-Block LWE

`LWE.TwoBlock` keeps two distinct error samplers explicit.  This file gives the exact reduction to
ordinary batch LWE when the second error distribution is obtained by adding an independent
widening error to the first distribution.

Starting with `firstSamples + secondSamples` ordinary LWE rows using `firstErrorSampler`, the
reduction splits the transcript and adds fresh widening error only to the second output block.  In
the real branch, the scalar convolution premise lifts to every second-block coordinate.  In the
uniform branch, translation by the widening vector is a permutation; totality of the widening
sampler prevents loss of probability mass in `ProbComp`'s subprobability semantics.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.TwoBlock

/-- Add an independent widening vector to the output of the second LWE block. -/
def addSecondNoise {R : Type} [Add R]
    {dimension firstSamples secondSamples : ℕ}
    (extra : Fin secondSamples → R)
    (transcript : Transcript R dimension firstSamples secondSamples) :
    Transcript R dimension firstSamples secondSamples :=
  (transcript.1, (transcript.2.1, transcript.2.2 + extra))

/-- Undo `addSecondNoise`. -/
def removeSecondNoise {R : Type} [Sub R]
    {dimension firstSamples secondSamples : ℕ}
    (extra : Fin secondSamples → R)
    (transcript : Transcript R dimension firstSamples secondSamples) :
    Transcript R dimension firstSamples secondSamples :=
  (transcript.1, (transcript.2.1, transcript.2.2 - extra))

@[simp]
theorem removeSecondNoise_addSecondNoise {R : Type} [AddGroup R]
    {dimension firstSamples secondSamples : ℕ}
    (extra : Fin secondSamples → R)
    (transcript : Transcript R dimension firstSamples secondSamples) :
    removeSecondNoise extra (addSecondNoise extra transcript) = transcript := by
  rcases transcript with ⟨challenge, firstOutput, secondOutput⟩
  simp [addSecondNoise, removeSecondNoise]

@[simp]
theorem addSecondNoise_removeSecondNoise {R : Type} [AddGroup R]
    {dimension firstSamples secondSamples : ℕ}
    (extra : Fin secondSamples → R)
    (transcript : Transcript R dimension firstSamples secondSamples) :
    addSecondNoise extra (removeSecondNoise extra transcript) = transcript := by
  rcases transcript with ⟨challenge, firstOutput, secondOutput⟩
  simp [addSecondNoise, removeSecondNoise]

/-- For each fixed widening vector, adding it to the second output block is a permutation. -/
theorem addSecondNoise_bijective {R : Type} [AddGroup R]
    {dimension firstSamples secondSamples : ℕ}
    (extra : Fin secondSamples → R) :
    Function.Bijective
      (addSecondNoise (dimension := dimension) (firstSamples := firstSamples) extra) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨removeSecondNoise extra,
      removeSecondNoise_addSecondNoise extra,
      addSecondNoise_removeSecondNoise extra⟩

/-- Splitting a combined transcript and widening its second block is a permutation for each fixed
widening vector. -/
theorem addSecondNoise_splitTranscript_bijective {R : Type} [AddGroup R]
    {dimension firstSamples secondSamples : ℕ}
    (extra : Fin secondSamples → R) :
    Function.Bijective
      (fun transcript : BatchTranscript R dimension (firstSamples + secondSamples) ↦
        addSecondNoise extra (splitTranscript transcript)) :=
  (addSecondNoise_bijective (dimension := dimension) (firstSamples := firstSamples) extra).comp
    splitTranscript_bijective

/-- Pair two IID first-block error vectors and widen only the second one. -/
def secondWidenedErrorSampler {R : Type} [Add R]
    (firstSamples secondSamples : ℕ)
    (firstErrorSampler extraErrorSampler : ProbComp R) :
    ProbComp (Output R firstSamples secondSamples) := do
  let firstError ← ProbComp.sampleIID firstSamples firstErrorSampler
  let secondError ← ProbComp.sampleIID secondSamples firstErrorSampler
  let extraError ← ProbComp.sampleIID secondSamples extraErrorSampler
  return (firstError, secondError + extraError)

/-- Scalar convolution lifts to the unequal vector pair while leaving the first block unchanged. -/
theorem secondWidenedErrorSampler_evalDist_eq {R : Type} [AddCommMonoid R]
    (firstSamples secondSamples : ℕ)
    (firstErrorSampler secondErrorSampler extraErrorSampler : ProbComp R)
    (hConvolution : FormalProof4FHE.SharedRandomness.ScalarErrorConvolution
      secondErrorSampler firstErrorSampler extraErrorSampler) :
    𝒟[secondWidenedErrorSampler firstSamples secondSamples
        firstErrorSampler extraErrorSampler] =
      𝒟[do
        let firstError ← ProbComp.sampleIID firstSamples firstErrorSampler
        let secondError ← ProbComp.sampleIID secondSamples secondErrorSampler
        return (firstError, secondError)] := by
  let firstErrors := ProbComp.sampleIID firstSamples firstErrorSampler
  let widenedSecond : ProbComp (Fin secondSamples → R) := do
    let secondError ← ProbComp.sampleIID secondSamples firstErrorSampler
    let extraError ← ProbComp.sampleIID secondSamples extraErrorSampler
    return secondError + extraError
  let targetSecond := ProbComp.sampleIID secondSamples secondErrorSampler
  have hSecond : 𝒟[widenedSecond] = 𝒟[targetSecond] := by
    exact FormalProof4FHE.SharedRandomness.vectorErrorConvolution_of_scalar
      secondSamples secondErrorSampler firstErrorSampler extraErrorSampler hConvolution
  calc
    _ = 𝒟[firstErrors >>= fun firstError ↦
        widenedSecond >>= fun secondError ↦ pure (firstError, secondError)] := by
      simp [secondWidenedErrorSampler, firstErrors, widenedSecond, monad_norm]
    _ = 𝒟[firstErrors >>= fun firstError ↦
        targetSecond >>= fun secondError ↦ pure (firstError, secondError)] := by
      refine evalDist_bind_congr' firstErrors fun firstError ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hSecond _
    _ = _ := by
      simp [firstErrors, targetSecond, monad_norm]

/-- Add widening noise to the second block of a split ordinary transcript before invoking the
heterogeneous distinguisher. -/
def convolutionReduction {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    {dimension firstSamples secondSamples : ℕ}
    {secretSampler : ProbComp Secret} {embed : Secret → Fin dimension → R}
    {firstErrorSampler secondErrorSampler extraErrorSampler : ProbComp R}
    (adversary : LearningWithErrors.Adversary
      (heterogeneousProblem dimension firstSamples secondSamples secretSampler embed
        firstErrorSampler secondErrorSampler)) :
    LearningWithErrors.Adversary
      (embeddedBatchProblem dimension (firstSamples + secondSamples)
        secretSampler embed firstErrorSampler) :=
  fun transcript ↦ do
    let extra ← ProbComp.sampleIID secondSamples extraErrorSampler
    adversary (addSecondNoise extra (splitTranscript transcript))

/-- The real heterogeneous distribution is obtained exactly by splitting same-noise ordinary LWE
and widening its second error block. -/
theorem convolution_real_evalDist {R Secret : Type}
    [CommSemiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (firstErrorSampler secondErrorSampler extraErrorSampler : ProbComp R)
    (hConvolution : FormalProof4FHE.SharedRandomness.ScalarErrorConvolution
      secondErrorSampler firstErrorSampler extraErrorSampler) :
    𝒟[LearningWithErrors.distr
          (embeddedBatchProblem dimension (firstSamples + secondSamples)
            secretSampler embed firstErrorSampler) >>=
        fun transcript ↦ do
          let extra ← ProbComp.sampleIID secondSamples extraErrorSampler
          pure (addSecondNoise extra (splitTranscript transcript))] =
      𝒟[LearningWithErrors.distr
        (heterogeneousProblem dimension firstSamples secondSamples secretSampler embed
          firstErrorSampler secondErrorSampler)] := by
  let splitReal : ProbComp (Transcript R dimension firstSamples secondSamples) :=
    LearningWithErrors.distr
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed firstErrorSampler) >>=
      fun transcript ↦ pure (splitTranscript transcript)
  let sameNoiseReal : ProbComp (Transcript R dimension firstSamples secondSamples) :=
    LearningWithErrors.distr
      (problem dimension firstSamples secondSamples secretSampler embed firstErrorSampler)
  let widen : Transcript R dimension firstSamples secondSamples →
      ProbComp (Transcript R dimension firstSamples secondSamples) :=
    fun transcript ↦ do
      let extra ← ProbComp.sampleIID secondSamples extraErrorSampler
      pure (addSecondNoise extra transcript)
  have hSplit : 𝒟[splitReal] = 𝒟[sameNoiseReal] := by
    exact split_real_evalDist dimension firstSamples secondSamples secretSampler embed
      firstErrorSampler
  calc
    _ = 𝒟[splitReal >>= widen] := by
      simp [splitReal, widen, bind_assoc, monad_norm]
    _ = 𝒟[sameNoiseReal >>= widen] :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hSplit widen
    _ = _ := by
      let challenges : ProbComp (Challenge R dimension firstSamples secondSamples) :=
        $ᵗ (Challenge R dimension firstSamples secondSamples)
      let widenedErrors := secondWidenedErrorSampler firstSamples secondSamples
        firstErrorSampler extraErrorSampler
      let targetErrors : ProbComp (Output R firstSamples secondSamples) := do
        let firstError ← ProbComp.sampleIID firstSamples firstErrorSampler
        let secondError ← ProbComp.sampleIID secondSamples secondErrorSampler
        return (firstError, secondError)
      have hErrors : 𝒟[widenedErrors] = 𝒟[targetErrors] := by
        exact secondWidenedErrorSampler_evalDist_eq firstSamples secondSamples
          firstErrorSampler secondErrorSampler extraErrorSampler hConvolution
      have left_eq : sameNoiseReal >>= widen =
          (challenges >>= fun challenge ↦
            secretSampler >>= fun secret ↦
            widenedErrors >>= fun errors ↦
            pure (realTranscript embed challenge secret errors)) := by
        simp [sameNoiseReal, widen, challenges, widenedErrors,
          secondWidenedErrorSampler, LearningWithErrors.distr, problem,
          heterogeneousProblem, addSecondNoise, realTranscript, add_assoc, bind_assoc,
          monad_norm]
      have right_eq :
          LearningWithErrors.distr
              (heterogeneousProblem dimension firstSamples secondSamples secretSampler embed
                firstErrorSampler secondErrorSampler) =
            (challenges >>= fun challenge ↦
              secretSampler >>= fun secret ↦
              targetErrors >>= fun errors ↦
              pure (realTranscript embed challenge secret errors)) := by
        simp [LearningWithErrors.distr, heterogeneousProblem, challenges, targetErrors,
          realTranscript, monad_norm]
      rw [left_eq, right_eq]
      refine evalDist_bind_congr' challenges fun challenge ↦ ?_
      refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hErrors _

/-- Widening the second block of a split uniform transcript leaves the transcript uniform. -/
theorem convolution_uniform_evalDist {R Secret : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (firstErrorSampler secondErrorSampler extraErrorSampler : ProbComp R)
    (hExtra : Pr[⊥ | extraErrorSampler] = 0) :
    𝒟[LearningWithErrors.uniformDistr
          (embeddedBatchProblem dimension (firstSamples + secondSamples)
            secretSampler embed firstErrorSampler) >>=
        fun transcript ↦ do
          let extra ← ProbComp.sampleIID secondSamples extraErrorSampler
          pure (addSecondNoise extra (splitTranscript transcript))] =
      𝒟[LearningWithErrors.uniformDistr
        (heterogeneousProblem dimension firstSamples secondSamples secretSampler embed
          firstErrorSampler secondErrorSampler)] := by
  rw [batchUniformDistr_eq_uniformSample,
    heterogeneousUniformDistr_eq_uniformSample]
  let combined := BatchTranscript R dimension (firstSamples + secondSamples)
  let target := Transcript R dimension firstSamples secondSamples
  let extras := ProbComp.sampleIID secondSamples extraErrorSampler
  have hExtras : Pr[⊥ | extras] = 0 :=
    FormalProof4FHE.SharedRandomness.probFailure_sampleIID_eq_zero
      secondSamples extraErrorSampler hExtra
  change 𝒟[(($ᵗ combined) >>= fun transcript ↦
      extras >>= fun extra ↦
      pure (addSecondNoise extra (splitTranscript transcript)))] =
    𝒟[$ᵗ target]
  calc
    _ = 𝒟[extras >>= fun extra ↦
        ($ᵗ combined) >>= fun transcript ↦
        pure (addSecondNoise extra (splitTranscript transcript))] :=
      evalDist_bind_bind_swap ($ᵗ combined) extras _
    _ = 𝒟[extras >>= fun _ ↦ ($ᵗ target)] := by
      refine evalDist_bind_congr' extras fun extra ↦ ?_
      simpa [combined, target, map_eq_bind_pure_comp, monad_norm] using
        (evalDist_map_bijective_uniform_cross
          (α := BatchTranscript R dimension (firstSamples + secondSamples))
          (β := Transcript R dimension firstSamples secondSamples)
          (fun transcript ↦ addSecondNoise extra (splitTranscript transcript))
          (addSecondNoise_splitTranscript_bijective
            (dimension := dimension) (firstSamples := firstSamples) extra))
    _ = _ :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        extras hExtras _

/-- Exact real-game equality for the convolution reduction. -/
theorem convolution_game0_evalDist_eq {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (firstErrorSampler secondErrorSampler extraErrorSampler : ProbComp R)
    (hConvolution : FormalProof4FHE.SharedRandomness.ScalarErrorConvolution
      secondErrorSampler firstErrorSampler extraErrorSampler)
    (adversary : LearningWithErrors.Adversary
      (heterogeneousProblem dimension firstSamples secondSamples secretSampler embed
        firstErrorSampler secondErrorSampler)) :
    𝒟[LearningWithErrors.game0
        (heterogeneousProblem dimension firstSamples secondSamples secretSampler embed
          firstErrorSampler secondErrorSampler) adversary] =
      𝒟[LearningWithErrors.game0
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed firstErrorSampler)
        (convolutionReduction (extraErrorSampler := extraErrorSampler) adversary)] := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  simp only [convolutionReduction]
  rw [show (LearningWithErrors.distr
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed firstErrorSampler) >>=
      fun transcript ↦ ProbComp.sampleIID secondSamples extraErrorSampler >>= fun extra ↦
        adversary (addSecondNoise extra (splitTranscript transcript))) =
    ((LearningWithErrors.distr
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed firstErrorSampler) >>=
      fun transcript ↦ do
        let extra ← ProbComp.sampleIID secondSamples extraErrorSampler
        pure (addSecondNoise extra (splitTranscript transcript))) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    convolution_real_evalDist dimension firstSamples secondSamples secretSampler embed
      firstErrorSampler secondErrorSampler extraErrorSampler hConvolution]

/-- Exact uniform-game equality for the convolution reduction. -/
theorem convolution_game1_evalDist_eq {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (firstErrorSampler secondErrorSampler extraErrorSampler : ProbComp R)
    (hExtra : Pr[⊥ | extraErrorSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (heterogeneousProblem dimension firstSamples secondSamples secretSampler embed
        firstErrorSampler secondErrorSampler)) :
    𝒟[LearningWithErrors.game1
        (heterogeneousProblem dimension firstSamples secondSamples secretSampler embed
          firstErrorSampler secondErrorSampler) adversary] =
      𝒟[LearningWithErrors.game1
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed firstErrorSampler)
        (convolutionReduction (extraErrorSampler := extraErrorSampler) adversary)] := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [convolutionReduction]
  rw [show (LearningWithErrors.uniformDistr
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed firstErrorSampler) >>=
      fun transcript ↦ ProbComp.sampleIID secondSamples extraErrorSampler >>= fun extra ↦
        adversary (addSecondNoise extra (splitTranscript transcript))) =
    ((LearningWithErrors.uniformDistr
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed firstErrorSampler) >>=
      fun transcript ↦ do
        let extra ← ProbComp.sampleIID secondSamples extraErrorSampler
        pure (addSecondNoise extra (splitTranscript transcript))) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    convolution_uniform_evalDist dimension firstSamples secondSamples secretSampler embed
      firstErrorSampler secondErrorSampler extraErrorSampler hExtra]

/-- **Heterogeneous-to-ordinary exact reduction.** If the second scalar error is the convolution
of the first error with a total independent widening sampler, unequal two-block LWE has exactly the
advantage of one ordinary batch-LWE adversary using the first error sampler. -/
theorem heterogeneous_advantage_eq_batch_of_convolution {R Secret : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (firstErrorSampler secondErrorSampler extraErrorSampler : ProbComp R)
    (hConvolution : FormalProof4FHE.SharedRandomness.ScalarErrorConvolution
      secondErrorSampler firstErrorSampler extraErrorSampler)
    (hExtra : Pr[⊥ | extraErrorSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (heterogeneousProblem dimension firstSamples secondSamples secretSampler embed
        firstErrorSampler secondErrorSampler)) :
    LearningWithErrors.advantage
        (heterogeneousProblem dimension firstSamples secondSamples secretSampler embed
          firstErrorSampler secondErrorSampler) adversary =
      LearningWithErrors.advantage
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed firstErrorSampler)
        (convolutionReduction (extraErrorSampler := extraErrorSampler) adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (convolution_game0_evalDist_eq dimension firstSamples secondSamples secretSampler embed
        firstErrorSampler secondErrorSampler extraErrorSampler hConvolution adversary) true,
    evalDist_ext_iff.mp
      (convolution_game1_evalDist_eq dimension firstSamples secondSamples secretSampler embed
        firstErrorSampler secondErrorSampler extraErrorSampler hExtra adversary) true]

end FormalProof4FHE.LWE.TwoBlock
