/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.SubspaceLWE.Basic

/-!
# Security of the Shared-Randomness Subspace Instance

This file transports the complete shared-randomness reduction through the specialization theorem.
The result is stated directly as a generalized-subspace advantage equality against ordinary LWE
with `m + m` samples.
-/

open OracleComp

namespace FormalProof4FHE.GeneralizedSubspaceLWE

/-- The nested shared-randomness generalized-subspace instance reduces exactly to ordinary LWE
with `m + m` samples. -/
theorem shared_zmod_advantage_eq_batch {q : ℕ} [NeZero q]
    (n k m : ℕ)
    (smallErrorSampler largeErrorSampler extraErrorSampler : ProbComp (ZMod q))
    (hConvolution : FormalProof4FHE.SharedRandomness.ScalarErrorConvolution
      smallErrorSampler largeErrorSampler extraErrorSampler)
    (hExtraError : Pr[⊥ | extraErrorSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (problem m (sharedSpec n k
        ($ᵗ (Fin n → ZMod q)) ($ᵗ (Fin k → ZMod q))
        smallErrorSampler largeErrorSampler))) :
    LearningWithErrors.advantage
        (problem m (sharedSpec n k
          ($ᵗ (Fin n → ZMod q)) ($ᵗ (Fin k → ZMod q))
          smallErrorSampler largeErrorSampler)) adversary =
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.zmodBatchProblem n (m + m) q largeErrorSampler)
        (FormalProof4FHE.SharedRandomness.ordinaryReduction
          (secretSampler := ($ᵗ (Fin n → ZMod q)))
          (errorSampler := largeErrorSampler)
          (FormalProof4FHE.SharedRandomness.reduction
            ($ᵗ (Fin k → ZMod q)) extraErrorSampler adversary)) := by
  rw [← shared_problem_eq_generalized n k m
    ($ᵗ (Fin n → ZMod q)) ($ᵗ (Fin k → ZMod q))
    smallErrorSampler largeErrorSampler]
  exact FormalProof4FHE.SharedRandomness.zmod_advantage_eq_batch n k m
    smallErrorSampler largeErrorSampler extraErrorSampler
    hConvolution hExtraError adversary

/-- Hardness transfers immediately from ordinary LWE to the shared-randomness generalized
subspace instance. -/
theorem shared_zmod_advantage_le {q : ℕ} [NeZero q]
    (n k m : ℕ)
    (smallErrorSampler largeErrorSampler extraErrorSampler : ProbComp (ZMod q))
    (hConvolution : FormalProof4FHE.SharedRandomness.ScalarErrorConvolution
      smallErrorSampler largeErrorSampler extraErrorSampler)
    (hExtraError : Pr[⊥ | extraErrorSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (problem m (sharedSpec n k
        ($ᵗ (Fin n → ZMod q)) ($ᵗ (Fin k → ZMod q))
        smallErrorSampler largeErrorSampler)) )
    (bound : ℝ)
    (hOrdinary : LearningWithErrors.advantage
      (FormalProof4FHE.LWE.zmodBatchProblem n (m + m) q largeErrorSampler)
      (FormalProof4FHE.SharedRandomness.ordinaryReduction
        (secretSampler := ($ᵗ (Fin n → ZMod q)))
        (errorSampler := largeErrorSampler)
        (FormalProof4FHE.SharedRandomness.reduction
          ($ᵗ (Fin k → ZMod q)) extraErrorSampler adversary)) ≤ bound) :
    LearningWithErrors.advantage
      (problem m (sharedSpec n k
        ($ᵗ (Fin n → ZMod q)) ($ᵗ (Fin k → ZMod q))
        smallErrorSampler largeErrorSampler)) adversary ≤ bound := by
  rw [shared_zmod_advantage_eq_batch n k m smallErrorSampler
    largeErrorSampler extraErrorSampler hConvolution hExtraError adversary]
  exact hOrdinary

end FormalProof4FHE.GeneralizedSubspaceLWE
