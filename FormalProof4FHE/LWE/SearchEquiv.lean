/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.SharedRandomness.Reduction
import FormalProof4FHE.LWE.SampleRestriction

/-!
# Distribution-Preserving Equivalences for Search LWE

A public reshaping of an LWE challenge and output is sound for search only when the experiment
continues to check the adversary's answer against the same hidden secret.  This module provides
that exact transport theorem.  It is deliberately stated for search experiments rather than
deduced from decisional-game equality.
-/

open OracleComp

namespace FormalProof4FHE.LWE.SearchEquiv

variable {SourceChallenge TargetChallenge Secret SourceOutput TargetOutput : Type}

/-- Precompose a target search adversary with public challenge/output equivalences. -/
def reduction
    (challengeEquiv : SourceChallenge ≃ TargetChallenge)
    (outputEquiv : SourceOutput ≃ TargetOutput)
    {source : LearningWithErrors.Problem SourceChallenge Secret SourceOutput}
    {target : LearningWithErrors.Problem TargetChallenge Secret TargetOutput}
    (adversary : LearningWithErrors.SearchAdversary target) :
    LearningWithErrors.SearchAdversary source :=
  fun transcript ↦ adversary
    (challengeEquiv transcript.1, outputEquiv transcript.2)

/-- Search experiments are exactly preserved by distributionally matching public equivalences
that commute with real transcript assembly.  The secret sampler is matched separately and the
same sampled secret remains in scope for the final equality test. -/
theorem searchExperiment_evalDist_eq
    [Add SourceOutput] [Add TargetOutput] [DecidableEq Secret]
    (source : LearningWithErrors.Problem SourceChallenge Secret SourceOutput)
    (target : LearningWithErrors.Problem TargetChallenge Secret TargetOutput)
    (challengeEquiv : SourceChallenge ≃ TargetChallenge)
    (outputEquiv : SourceOutput ≃ TargetOutput)
    (hChallenge :
      evalDist (challengeEquiv <$> source.sampleChallenge) =
        evalDist target.sampleChallenge)
    (hSecret : evalDist source.sampleSecret = evalDist target.sampleSecret)
    (hError :
      evalDist (outputEquiv <$> source.sampleError) =
        evalDist target.sampleError)
    (hAssemble : ∀ secret challenge error,
      outputEquiv (source.noiseless secret challenge + error) =
        target.noiseless secret (challengeEquiv challenge) + outputEquiv error)
    (adversary : LearningWithErrors.SearchAdversary target) :
    evalDist (LearningWithErrors.searchExperiment source
        (reduction challengeEquiv outputEquiv adversary)) =
      evalDist (LearningWithErrors.searchExperiment target adversary) := by
  let mappedChallenges := challengeEquiv <$> source.sampleChallenge
  let mappedErrors := outputEquiv <$> source.sampleError
  let finish := fun (challenge : TargetChallenge) (secret : Secret)
      (error : TargetOutput) ↦ do
    let recovered ← adversary
      (challenge, target.noiseless secret challenge + error)
    return decide (recovered = secret)
  have source_eq :
      LearningWithErrors.searchExperiment source
          (reduction challengeEquiv outputEquiv adversary) =
        (mappedChallenges >>= fun challenge ↦
          source.sampleSecret >>= fun secret ↦
          mappedErrors >>= fun error ↦
          finish challenge secret error) := by
    simp [LearningWithErrors.searchExperiment, reduction, mappedChallenges,
      mappedErrors, finish, hAssemble, bind_assoc, monad_norm]
  have target_eq :
      LearningWithErrors.searchExperiment target adversary =
        (target.sampleChallenge >>= fun challenge ↦
          target.sampleSecret >>= fun secret ↦
          target.sampleError >>= fun error ↦
          finish challenge secret error) := by
    simp [LearningWithErrors.searchExperiment, finish, monad_norm]
  rw [source_eq, target_eq]
  calc
    _ = evalDist (target.sampleChallenge >>= fun challenge ↦
          source.sampleSecret >>= fun secret ↦
          mappedErrors >>= fun error ↦
          finish challenge secret error) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hChallenge _
    _ = evalDist (target.sampleChallenge >>= fun challenge ↦
          target.sampleSecret >>= fun secret ↦
          mappedErrors >>= fun error ↦
          finish challenge secret error) := by
      refine evalDist_bind_congr' target.sampleChallenge fun challenge ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hSecret _
    _ = _ := by
      refine evalDist_bind_congr' target.sampleChallenge fun challenge ↦ ?_
      refine evalDist_bind_congr' target.sampleSecret fun secret ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hError _

end FormalProof4FHE.LWE.SearchEquiv
