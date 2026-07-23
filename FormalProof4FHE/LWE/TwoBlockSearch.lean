/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.SearchEquiv
import FormalProof4FHE.LWE.TwoBlock

/-!
# Search-LWE Equivalence for an Unequal Two-Block Split

When both blocks use the same scalar error sampler, an unequal two-block search-LWE transcript is
only a public split of one ordinary combined batch.  This file proves exact search-experiment
equality, retaining the sampled secret through the final recovery check.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.TwoBlock

/-- Split one combined challenge matrix into the two challenge blocks. -/
def challengeSplitEquiv (R : Type) (dimension firstSamples secondSamples : ℕ) :
    Matrix (Fin dimension) (Fin (firstSamples + secondSamples)) R ≃
      Challenge R dimension firstSamples secondSamples where
  toFun := splitBatchColumns
  invFun := appendBatchColumns
  left_inv := appendBatchColumns_splitBatchColumns
  right_inv := splitBatchColumns_appendBatchColumns

/-- Split one combined output vector into the two output blocks. -/
def outputSplitEquiv (R : Type) (firstSamples secondSamples : ℕ) :
    (Fin (firstSamples + secondSamples) → R) ≃
      Output R firstSamples secondSamples where
  toFun := splitBatchOutput
  invFun := appendBatchOutput
  left_inv := appendBatchOutput_splitBatchOutput
  right_inv := splitBatchOutput_appendBatchOutput

/-- Preprocess one ordinary combined-batch transcript for a two-block search adversary. -/
def searchReduction {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    {dimension firstSamples secondSamples : ℕ}
    {secretSampler : ProbComp Secret} {embed : Secret → Fin dimension → R}
    {errorSampler : ProbComp R}
    (adversary : LearningWithErrors.SearchAdversary
      (problem dimension firstSamples secondSamples secretSampler embed errorSampler)) :
    LearningWithErrors.SearchAdversary
      (embeddedBatchProblem dimension (firstSamples + secondSamples)
        secretSampler embed errorSampler) :=
  FormalProof4FHE.LWE.SearchEquiv.reduction
    (challengeSplitEquiv R dimension firstSamples secondSamples)
    (outputSplitEquiv R firstSamples secondSamples) adversary

/-- Splitting commutes with real LWE transcript assembly. -/
theorem outputSplitEquiv_assemble {R Secret : Type} [Semiring R]
    {dimension firstSamples secondSamples : ℕ}
    (embed : Secret → Fin dimension → R)
    (secret : Secret)
    (challenge : Matrix (Fin dimension) (Fin (firstSamples + secondSamples)) R)
    (error : Fin (firstSamples + secondSamples) → R) :
    outputSplitEquiv R firstSamples secondSamples
        (vecMul (embed secret) challenge + error) =
      (vecMul (embed secret)
          (challengeSplitEquiv R dimension firstSamples secondSamples challenge).1,
        vecMul (embed secret)
          (challengeSplitEquiv R dimension firstSamples secondSamples challenge).2) +
        outputSplitEquiv R firstSamples secondSamples error := by
  apply Prod.ext
  · funext sample
    rfl
  · funext sample
    rfl

/-- An equal-noise two-block search-LWE experiment is exactly the corresponding ordinary
`firstSamples + secondSamples` batch search-LWE experiment. -/
theorem searchExperiment_evalDist_eq_batch {R Secret : Type}
    [Semiring R] [Fintype R] [DecidableEq R] [SampleableType R]
    [DecidableEq Secret]
    (dimension firstSamples secondSamples : ℕ)
    (secretSampler : ProbComp Secret) (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.SearchAdversary
      (problem dimension firstSamples secondSamples secretSampler embed errorSampler)) :
    evalDist (LearningWithErrors.searchExperiment
        (embeddedBatchProblem dimension (firstSamples + secondSamples)
          secretSampler embed errorSampler)
        (searchReduction adversary)) =
      evalDist (LearningWithErrors.searchExperiment
        (problem dimension firstSamples secondSamples secretSampler embed errorSampler)
        adversary) := by
  let source := embeddedBatchProblem dimension (firstSamples + secondSamples)
    secretSampler embed errorSampler
  let target := problem dimension firstSamples secondSamples
    secretSampler embed errorSampler
  let challengeEquiv := challengeSplitEquiv R dimension firstSamples secondSamples
  let outputEquiv := outputSplitEquiv R firstSamples secondSamples
  apply FormalProof4FHE.LWE.SearchEquiv.searchExperiment_evalDist_eq
    source target challengeEquiv outputEquiv
  · exact evalDist_map_bijective_uniform_cross
      (α := Matrix (Fin dimension) (Fin (firstSamples + secondSamples)) R)
      (β := Challenge R dimension firstSamples secondSamples)
      challengeEquiv challengeEquiv.bijective
  · rfl
  · change evalDist (splitBatchOutput <$>
        ProbComp.sampleIID (firstSamples + secondSamples) errorSampler) = _
    exact splitBatchOutput_sampleIID_evalDist firstSamples secondSamples errorSampler
  · intro secret challenge error
    simpa only [source, target, challengeEquiv, outputEquiv, embeddedBatchProblem,
      problem, heterogeneousProblem] using
      (outputSplitEquiv_assemble embed secret challenge error)

end FormalProof4FHE.LWE.TwoBlock
