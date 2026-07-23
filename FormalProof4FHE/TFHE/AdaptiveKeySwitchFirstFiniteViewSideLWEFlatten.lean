/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.SearchEquiv
import FormalProof4FHE.LWE.TwoBlockSearch
import FormalProof4FHE.TFHE.AdaptiveKeySwitchFirstFiniteViewSideLWE

/-!
# Flattening the Uniform-BRK Side Problem to Conventional Two-Block Search LWE

The structured side problem stores one KSK block and one input-tape block per augmented view.
This module concatenates every KSK block into one matrix and every input block into a second
matrix.  Both blocks share the same scalar binary secret.  The transformation is an exact public
equivalence, and the proof is carried out directly for the search experiment so the final secret
check remains coupled to the original hidden key.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView

open Native

variable
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount rounds : ℕ} [NeZero q]

/-! ## Generic parallel two-block equivalences -/

/-- Split both combined challenge matrices into `blocks` parallel two-block challenges. -/
def parallelTwoBlockChallengeEquiv (R : Type)
    (dimension blocks firstSamples secondSamples : ℕ) :
    FormalProof4FHE.LWE.TwoBlock.Challenge R dimension
        (blocks * firstSamples) (blocks * secondSamples) ≃
      (Fin blocks → FormalProof4FHE.LWE.TwoBlock.Challenge R dimension
        firstSamples secondSamples) :=
  ((FormalProof4FHE.LWE.ParallelBatch.challengeEquiv
      R dimension blocks firstSamples).prodCongr
    (FormalProof4FHE.LWE.ParallelBatch.challengeEquiv
      R dimension blocks secondSamples)).trans
    (Equiv.arrowProdEquivProdArrow (Fin blocks)
      (fun _ ↦ Matrix (Fin dimension) (Fin firstSamples) R)
      (fun _ ↦ Matrix (Fin dimension) (Fin secondSamples) R)).symm

/-- Split both combined output vectors into `blocks` parallel two-block outputs. -/
def parallelTwoBlockOutputEquiv (R : Type)
    (blocks firstSamples secondSamples : ℕ) :
    FormalProof4FHE.LWE.TwoBlock.Output R
        (blocks * firstSamples) (blocks * secondSamples) ≃
      (Fin blocks → FormalProof4FHE.LWE.TwoBlock.Output R
        firstSamples secondSamples) :=
  ((FormalProof4FHE.LWE.ParallelBatch.outputEquiv
      R blocks firstSamples).prodCongr
    (FormalProof4FHE.LWE.ParallelBatch.outputEquiv
      R blocks secondSamples)).trans
    (Equiv.arrowProdEquivProdArrow (Fin blocks)
      (fun _ ↦ Fin firstSamples → R)
      (fun _ ↦ Fin secondSamples → R)).symm

/-- Split a complete conventional two-block transcript viewwise. -/
def parallelTwoBlockTranscriptEquiv (R : Type)
    (dimension blocks firstSamples secondSamples : ℕ) :
    FormalProof4FHE.LWE.TwoBlock.Transcript R dimension
        (blocks * firstSamples) (blocks * secondSamples) ≃
      ((Fin blocks → FormalProof4FHE.LWE.TwoBlock.Challenge R dimension
          firstSamples secondSamples) ×
        (Fin blocks → FormalProof4FHE.LWE.TwoBlock.Output R
          firstSamples secondSamples)) :=
  (parallelTwoBlockChallengeEquiv R dimension blocks firstSamples secondSamples).prodCongr
    (parallelTwoBlockOutputEquiv R blocks firstSamples secondSamples)

/-! ## Conventional flattened scalar-LWE problem -/

/-- One conventional heterogeneous two-block scalar-LWE instance containing every augmented
view: the first matrix contains all KSK rows and the second contains all zero-message input rows. -/
noncomputable def flatSideLweProblem
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)) :
    LearningWithErrors.Problem
      (FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
        (sideViewCount lweDimension rounds *
          sideKeySwitchSamples ringRank degree keySwitchLevels)
        (sideViewCount lweDimension rounds * queryCount))
      (BinarySecret lweDimension)
      (FormalProof4FHE.LWE.TwoBlock.Output (ZMod q)
        (sideViewCount lweDimension rounds *
          sideKeySwitchSamples ringRank degree keySwitchLevels)
        (sideViewCount lweDimension rounds * queryCount)) :=
  FormalProof4FHE.LWE.TwoBlock.heterogeneousProblem
    lweDimension
    (sideViewCount lweDimension rounds *
      sideKeySwitchSamples ringRank degree keySwitchLevels)
    (sideViewCount lweDimension rounds * queryCount)
    (sampleLweSecret lweDimension) embedBinarySecret
    keySwitchErrorSampler inputErrorSampler

/-- Preprocess a conventional combined two-block transcript for the structured side reduction. -/
noncomputable def flatSideLweSearchReduction
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    LearningWithErrors.SearchAdversary
      (flatSideLweProblem (rounds := rounds) (ringRank := ringRank)
        (degree := degree) (keySwitchLevels := keySwitchLevels)
        (lweDimension := lweDimension) (queryCount := queryCount)
        keySwitchErrorSampler inputErrorSampler) :=
  FormalProof4FHE.LWE.SearchEquiv.reduction
    (parallelTwoBlockChallengeEquiv (ZMod q) lweDimension
      (sideViewCount lweDimension rounds)
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount)
    (parallelTwoBlockOutputEquiv (ZMod q)
      (sideViewCount lweDimension rounds)
      (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount)
    (sideLweSearchReductionFor keySwitchErrorSampler inputErrorSampler
      keySwitchGadget solver)

/-! ## Sampler and real-transcript alignment -/

/-- Splitting two uniformly sampled combined matrices gives exactly the structured independent
challenge array. -/
theorem flatSideLwe_challenge_evalDist
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)) :
    evalDist
        (parallelTwoBlockChallengeEquiv (ZMod q) lweDimension
            (sideViewCount lweDimension rounds)
            (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount <$>
          (flatSideLweProblem (rounds := rounds) (ringRank := ringRank)
            (degree := degree) (keySwitchLevels := keySwitchLevels)
            (lweDimension := lweDimension) (queryCount := queryCount)
            keySwitchErrorSampler inputErrorSampler).sampleChallenge) =
      evalDist
        (sideLweProblem (q := q) (ringRank := ringRank) (degree := degree)
          (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
          (queryCount := queryCount) (rounds := rounds)
          keySwitchErrorSampler inputErrorSampler).sampleChallenge := by
  let sourceChallenge := FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
    (sideViewCount lweDimension rounds *
      sideKeySwitchSamples ringRank degree keySwitchLevels)
    (sideViewCount lweDimension rounds * queryCount)
  let targetChallenge := SideLWEChallenge q lweDimension ringRank degree
    keySwitchLevels queryCount rounds
  let equiv := parallelTwoBlockChallengeEquiv (ZMod q) lweDimension
    (sideViewCount lweDimension rounds)
    (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount
  have hmap :
      evalDist (equiv <$> ($ᵗ sourceChallenge)) =
        evalDist ($ᵗ targetChallenge) :=
    evalDist_map_bijective_uniform_cross
      (α := sourceChallenge) (β := targetChallenge) equiv equiv.bijective
  have hiid :
      evalDist (Fin.mOfFn (sideViewCount lweDimension rounds) fun _ ↦
        $ᵗ (FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
          (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount)) =
        evalDist ($ᵗ targetChallenge) := by
    simpa only [ProbComp.sampleIID, targetChallenge] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
          (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount)
        (sideViewCount lweDimension rounds))
  calc
    _ = evalDist ($ᵗ targetChallenge) := by
      simpa only [flatSideLweProblem,
        FormalProof4FHE.LWE.TwoBlock.heterogeneousProblem, sourceChallenge, equiv] using hmap
    _ = _ := by
      rw [← hiid]
      rfl

/-- Splitting both combined IID error vectors gives exactly the structured independent
heterogeneous error array. -/
theorem flatSideLwe_error_evalDist
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)) :
    evalDist
        (parallelTwoBlockOutputEquiv (ZMod q)
            (sideViewCount lweDimension rounds)
            (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount <$>
          (flatSideLweProblem (rounds := rounds) (ringRank := ringRank)
            (degree := degree) (keySwitchLevels := keySwitchLevels)
            (lweDimension := lweDimension) (queryCount := queryCount)
            keySwitchErrorSampler inputErrorSampler).sampleError) =
      evalDist
        (sideLweProblem (q := q) (ringRank := ringRank) (degree := degree)
          (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
          (queryCount := queryCount) (rounds := rounds)
          keySwitchErrorSampler inputErrorSampler).sampleError := by
  let blocks := sideViewCount lweDimension rounds
  let firstSamples := sideKeySwitchSamples ringRank degree keySwitchLevels
  let flatFirst := ProbComp.sampleIID (blocks * firstSamples) keySwitchErrorSampler
  let flatSecond := ProbComp.sampleIID (blocks * queryCount) inputErrorSampler
  let mappedFirst := FormalProof4FHE.LWE.ParallelBatch.outputEquiv
    (ZMod q) blocks firstSamples <$> flatFirst
  let mappedSecond := FormalProof4FHE.LWE.ParallelBatch.outputEquiv
    (ZMod q) blocks queryCount <$> flatSecond
  let targetFirst := Fin.mOfFn blocks fun _ ↦
    ProbComp.sampleIID firstSamples keySwitchErrorSampler
  let targetSecond := Fin.mOfFn blocks fun _ ↦
    ProbComp.sampleIID queryCount inputErrorSampler
  let zipEquiv := (Equiv.arrowProdEquivProdArrow (Fin blocks)
    (fun _ ↦ Fin firstSamples → ZMod q)
    (fun _ ↦ Fin queryCount → ZMod q)).symm
  have hFirst : evalDist mappedFirst = evalDist targetFirst := by
    simpa only [mappedFirst, flatFirst, targetFirst] using
      (FormalProof4FHE.LWE.ParallelBatch.outputEquiv_sampleIID_evalDist
        (R := ZMod q) blocks firstSamples keySwitchErrorSampler)
  have hSecond : evalDist mappedSecond = evalDist targetSecond := by
    simpa only [mappedSecond, flatSecond, targetSecond] using
      (FormalProof4FHE.LWE.ParallelBatch.outputEquiv_sampleIID_evalDist
        (R := ZMod q) blocks queryCount inputErrorSampler)
  have hzip :
      evalDist (targetFirst >>= fun firstValues ↦
        targetSecond >>= fun secondValues ↦
        pure (zipEquiv (firstValues, secondValues))) =
      evalDist (Fin.mOfFn blocks fun _ ↦ do
        let firstError ← ProbComp.sampleIID firstSamples keySwitchErrorSampler
        let secondError ← ProbComp.sampleIID queryCount inputErrorSampler
        pure (firstError, secondError)) := by
    simpa [targetFirst, targetSecond, zipEquiv, bind_assoc, monad_norm] using
      (FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_zip blocks
        (fun _ ↦ ProbComp.sampleIID firstSamples keySwitchErrorSampler)
        (fun _ ↦ ProbComp.sampleIID queryCount inputErrorSampler))
  calc
    _ = evalDist (mappedFirst >>= fun firstValues ↦
          mappedSecond >>= fun secondValues ↦
          pure (zipEquiv (firstValues, secondValues))) := by
      simp [flatSideLweProblem,
        FormalProof4FHE.LWE.TwoBlock.heterogeneousProblem,
        parallelTwoBlockOutputEquiv, flatFirst, flatSecond, mappedFirst, mappedSecond,
        zipEquiv, blocks, firstSamples, bind_assoc, monad_norm]
    _ = evalDist (targetFirst >>= fun firstValues ↦
          mappedSecond >>= fun secondValues ↦
          pure (zipEquiv (firstValues, secondValues))) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hFirst _
    _ = evalDist (targetFirst >>= fun firstValues ↦
          targetSecond >>= fun secondValues ↦
          pure (zipEquiv (firstValues, secondValues))) := by
      refine evalDist_bind_congr' targetFirst fun firstValues ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hSecond _
    _ = evalDist (Fin.mOfFn blocks fun _ ↦ do
          let firstError ← ProbComp.sampleIID firstSamples keySwitchErrorSampler
          let secondError ← ProbComp.sampleIID queryCount inputErrorSampler
          pure (firstError, secondError)) := hzip
    _ = _ := by
      rfl

/-- Parallel splitting commutes pointwise with the noiseless products and error addition in the
two-block real transcript. -/
theorem flatSideLwe_assemble_equiv
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (secret : BinarySecret lweDimension)
    (challenge : FormalProof4FHE.LWE.TwoBlock.Challenge (ZMod q) lweDimension
      (sideViewCount lweDimension rounds *
        sideKeySwitchSamples ringRank degree keySwitchLevels)
      (sideViewCount lweDimension rounds * queryCount))
    (error : FormalProof4FHE.LWE.TwoBlock.Output (ZMod q)
      (sideViewCount lweDimension rounds *
        sideKeySwitchSamples ringRank degree keySwitchLevels)
      (sideViewCount lweDimension rounds * queryCount)) :
    parallelTwoBlockOutputEquiv (ZMod q)
        (sideViewCount lweDimension rounds)
        (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount
        ((flatSideLweProblem (rounds := rounds) (ringRank := ringRank)
          (degree := degree) (keySwitchLevels := keySwitchLevels)
          (lweDimension := lweDimension) (queryCount := queryCount)
          keySwitchErrorSampler inputErrorSampler).noiseless secret challenge + error) =
      (fun view ↦
        (vecMul (embedBinarySecret secret)
            ((parallelTwoBlockChallengeEquiv (ZMod q) lweDimension
              (sideViewCount lweDimension rounds)
              (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount challenge)
              view).1,
          vecMul (embedBinarySecret secret)
            ((parallelTwoBlockChallengeEquiv (ZMod q) lweDimension
              (sideViewCount lweDimension rounds)
              (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount challenge)
              view).2) +
          (parallelTwoBlockOutputEquiv (ZMod q)
            (sideViewCount lweDimension rounds)
            (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount error) view) := by
  funext view
  apply Prod.ext
  · funext sample
    rfl
  · funext sample
    rfl

/-! ## Exact conventional search-LWE endpoint -/

/-- Search success is unchanged when all structured per-view rows are concatenated into one
conventional heterogeneous two-block LWE transcript. -/
theorem sideLweSearchExperiment_evalDist_eq_flat
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    evalDist (LearningWithErrors.searchExperiment
        (sideLweProblem (q := q) (ringRank := ringRank) (degree := degree)
          (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
          (queryCount := queryCount) (rounds := rounds)
          keySwitchErrorSampler inputErrorSampler)
        (sideLweSearchReductionFor keySwitchErrorSampler inputErrorSampler
          keySwitchGadget solver)) =
      evalDist (LearningWithErrors.searchExperiment
        (flatSideLweProblem (rounds := rounds) (ringRank := ringRank)
          (degree := degree) (keySwitchLevels := keySwitchLevels)
          (lweDimension := lweDimension) (queryCount := queryCount)
          keySwitchErrorSampler inputErrorSampler)
        (flatSideLweSearchReduction keySwitchErrorSampler inputErrorSampler
          keySwitchGadget solver)) := by
  let source := flatSideLweProblem (rounds := rounds) (ringRank := ringRank)
    (degree := degree) (keySwitchLevels := keySwitchLevels)
    (lweDimension := lweDimension) (queryCount := queryCount)
    keySwitchErrorSampler inputErrorSampler
  let target := sideLweProblem (q := q) (ringRank := ringRank) (degree := degree)
    (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
    (queryCount := queryCount) (rounds := rounds)
    keySwitchErrorSampler inputErrorSampler
  let challengeEquiv := parallelTwoBlockChallengeEquiv (ZMod q) lweDimension
    (sideViewCount lweDimension rounds)
    (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount
  let outputEquiv := parallelTwoBlockOutputEquiv (ZMod q)
    (sideViewCount lweDimension rounds)
    (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount
  have h := FormalProof4FHE.LWE.SearchEquiv.searchExperiment_evalDist_eq
    source target challengeEquiv outputEquiv
    (flatSideLwe_challenge_evalDist keySwitchErrorSampler inputErrorSampler)
    (by rfl)
    (flatSideLwe_error_evalDist keySwitchErrorSampler inputErrorSampler)
    (by
      intro secret challenge error
      change parallelTwoBlockOutputEquiv (ZMod q)
          (sideViewCount lweDimension rounds)
          (sideKeySwitchSamples ringRank degree keySwitchLevels) queryCount
          (source.noiseless secret challenge + error) = _
      rw [← FormalProof4FHE.LWE.ParallelBatch.pointwiseAdd_eq_add]
      simpa only [source, target, challengeEquiv, outputEquiv, sideLweProblem] using
        (flatSideLwe_assemble_equiv keySwitchErrorSampler inputErrorSampler
          secret challenge error))
    (sideLweSearchReductionFor keySwitchErrorSampler inputErrorSampler
      keySwitchGadget solver)
  simpa only [source, target, challengeEquiv, outputEquiv,
    flatSideLweSearchReduction] using h.symm

/-- Exact success-probability form of the structured-to-conventional compilation. -/
theorem sideLweSearch_successProbability_eq_flat
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    Pr[= true | LearningWithErrors.searchExperiment
        (sideLweProblem (q := q) (ringRank := ringRank) (degree := degree)
          (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
          (queryCount := queryCount) (rounds := rounds)
          keySwitchErrorSampler inputErrorSampler)
        (sideLweSearchReductionFor keySwitchErrorSampler inputErrorSampler
          keySwitchGadget solver)] =
      Pr[= true | LearningWithErrors.searchExperiment
        (flatSideLweProblem (rounds := rounds) (ringRank := ringRank)
          (degree := degree) (keySwitchLevels := keySwitchLevels)
          (lweDimension := lweDimension) (queryCount := queryCount)
          keySwitchErrorSampler inputErrorSampler)
        (flatSideLweSearchReduction keySwitchErrorSampler inputErrorSampler
          keySwitchGadget solver)] :=
  evalDist_ext_iff.mp
    (sideLweSearchExperiment_evalDist_eq_flat keySwitchErrorSampler inputErrorSampler
      keySwitchGadget rounds solver) true

/-- The auxiliary uniform-BRK endpoint is exactly one conventional two-block scalar search-LWE
success probability. -/
theorem uniformBootstrapSideSearch_successProbability_eq_flatSearchLwe
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    LWE.AuxiliaryInput.Search.successProbability
        (uniformBootstrapSideSearchProblem keySwitchErrorSampler inputErrorSampler
          keySwitchGadget rounds)
        (toUniformBootstrapSideSolver solver) =
      Pr[= true | LearningWithErrors.searchExperiment
        (flatSideLweProblem (rounds := rounds) (ringRank := ringRank)
          (degree := degree) (keySwitchLevels := keySwitchLevels)
          (lweDimension := lweDimension) (queryCount := queryCount)
          keySwitchErrorSampler inputErrorSampler)
        (flatSideLweSearchReduction keySwitchErrorSampler inputErrorSampler
          keySwitchGadget solver)] := by
  rw [uniformBootstrapSideSearch_successProbability_eq_structuredSearchLwe,
    sideLweSearch_successProbability_eq_flat]

/-- **Finite TFHE BRK/search-LWE separation.** Real augmented scalar-key recovery is bounded by
the same-secret multi-view BRK circular term plus a single conventional two-block scalar
search-LWE experiment.  Its first block has `views * KSKRows` columns and its second has
`views * queryCount` columns. -/
theorem successProbability_le_bootstrapBatchCircular_add_flatSearchLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds solver ≤
      ENNReal.ofReal
          (bootstrapBatchCircularAdvantage ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget rounds solver) +
        Pr[= true | LearningWithErrors.searchExperiment
          (flatSideLweProblem (rounds := rounds) (ringRank := ringRank)
            (degree := degree) (keySwitchLevels := keySwitchLevels)
            (lweDimension := lweDimension) (queryCount := queryCount)
            keySwitchErrorSampler inputErrorSampler)
          (flatSideLweSearchReduction keySwitchErrorSampler inputErrorSampler
            keySwitchGadget solver)] := by
  simpa only [uniformBootstrapSideSearch_successProbability_eq_flatSearchLwe] using
    (successProbability_le_bootstrapBatchCircular_add_sideSearch
      ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
      keySwitchGadget rounds solver)

/-! ## Equal-noise ordinary-batch corollary -/

/-- When KSK and input rows use the same error sampler, concatenate the two blocks once more into
one ordinary matrix-LWE batch. -/
noncomputable def ordinarySideLweProblem
    (errorSampler : ProbComp (ZMod q)) :
    LearningWithErrors.Problem
      (Matrix (Fin lweDimension)
        (Fin ((sideViewCount lweDimension rounds *
            sideKeySwitchSamples ringRank degree keySwitchLevels) +
          sideViewCount lweDimension rounds * queryCount)) (ZMod q))
      (BinarySecret lweDimension)
      (Fin ((sideViewCount lweDimension rounds *
          sideKeySwitchSamples ringRank degree keySwitchLevels) +
        sideViewCount lweDimension rounds * queryCount) → ZMod q) :=
  FormalProof4FHE.LWE.embeddedBatchProblem lweDimension
    ((sideViewCount lweDimension rounds *
        sideKeySwitchSamples ringRank degree keySwitchLevels) +
      sideViewCount lweDimension rounds * queryCount)
    (sampleLweSecret lweDimension) embedBinarySecret errorSampler

/-- Ordinary-batch search reduction for the equal-noise side problem. -/
noncomputable def ordinarySideLweSearchReduction
    (errorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    LearningWithErrors.SearchAdversary
      (ordinarySideLweProblem (rounds := rounds) (ringRank := ringRank)
        (degree := degree) (keySwitchLevels := keySwitchLevels)
        (lweDimension := lweDimension) (queryCount := queryCount) errorSampler) :=
  FormalProof4FHE.LWE.TwoBlock.searchReduction
    (flatSideLweSearchReduction errorSampler errorSampler keySwitchGadget solver)

/-- The equal-noise conventional two-block endpoint is exactly one ordinary combined-batch
search-LWE experiment. -/
theorem flatSideLweSearchExperiment_evalDist_eq_ordinary
    (errorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    evalDist (LearningWithErrors.searchExperiment
        (flatSideLweProblem (rounds := rounds) (ringRank := ringRank)
          (degree := degree) (keySwitchLevels := keySwitchLevels)
          (lweDimension := lweDimension) (queryCount := queryCount)
          errorSampler errorSampler)
        (flatSideLweSearchReduction errorSampler errorSampler
          keySwitchGadget solver)) =
      evalDist (LearningWithErrors.searchExperiment
        (ordinarySideLweProblem (rounds := rounds) (ringRank := ringRank)
          (degree := degree) (keySwitchLevels := keySwitchLevels)
          (lweDimension := lweDimension) (queryCount := queryCount) errorSampler)
        (ordinarySideLweSearchReduction errorSampler keySwitchGadget solver)) := by
  simpa only [flatSideLweProblem, ordinarySideLweProblem,
    ordinarySideLweSearchReduction, FormalProof4FHE.LWE.TwoBlock.problem] using
    (FormalProof4FHE.LWE.TwoBlock.searchExperiment_evalDist_eq_batch
      (R := ZMod q) lweDimension
      (sideViewCount lweDimension rounds *
        sideKeySwitchSamples ringRank degree keySwitchLevels)
      (sideViewCount lweDimension rounds * queryCount)
      (sampleLweSecret lweDimension) embedBinarySecret errorSampler
      (flatSideLweSearchReduction errorSampler errorSampler
        keySwitchGadget solver)).symm

/-- Equal-noise finite TFHE bound with a single ordinary scalar search-LWE batch. -/
theorem successProbability_le_bootstrapBatchCircular_add_ordinarySearchLwe
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (scalarErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (solver : Solver q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount rounds) :
    successProbability ringErrorSampler scalarErrorSampler scalarErrorSampler
        tgswGadget keySwitchGadget rounds solver ≤
      ENNReal.ofReal
          (bootstrapBatchCircularAdvantage ringErrorSampler scalarErrorSampler
            scalarErrorSampler tgswGadget keySwitchGadget rounds solver) +
        Pr[= true | LearningWithErrors.searchExperiment
          (ordinarySideLweProblem (rounds := rounds) (ringRank := ringRank)
            (degree := degree) (keySwitchLevels := keySwitchLevels)
            (lweDimension := lweDimension) (queryCount := queryCount)
            scalarErrorSampler)
          (ordinarySideLweSearchReduction scalarErrorSampler
            keySwitchGadget solver)] := by
  have h := successProbability_le_bootstrapBatchCircular_add_flatSearchLwe
    ringErrorSampler scalarErrorSampler scalarErrorSampler tgswGadget
    keySwitchGadget rounds solver
  rw [show Pr[= true | LearningWithErrors.searchExperiment
          (flatSideLweProblem (rounds := rounds) (ringRank := ringRank)
            (degree := degree) (keySwitchLevels := keySwitchLevels)
            (lweDimension := lweDimension) (queryCount := queryCount)
            scalarErrorSampler scalarErrorSampler)
          (flatSideLweSearchReduction scalarErrorSampler scalarErrorSampler
            keySwitchGadget solver)] =
        Pr[= true | LearningWithErrors.searchExperiment
          (ordinarySideLweProblem (rounds := rounds) (ringRank := ringRank)
            (degree := degree) (keySwitchLevels := keySwitchLevels)
            (lweDimension := lweDimension) (queryCount := queryCount)
            scalarErrorSampler)
          (ordinarySideLweSearchReduction scalarErrorSampler
            keySwitchGadget solver)] from
      evalDist_ext_iff.mp
        (flatSideLweSearchExperiment_evalDist_eq_ordinary scalarErrorSampler
          keySwitchGadget rounds solver) true] at h
  exact h

end FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView
