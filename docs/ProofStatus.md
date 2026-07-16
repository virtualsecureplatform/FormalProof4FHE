# Proof status

| Result | Lean declaration | Status |
|---|---|---|
| Hidden-bit LWE advantage equals real/uniform distance | `FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage` | Implemented |
| Regev IND-CPA from decisional LWE and a leftover-hash masking term | `FormalProof4FHE.Regev.oneTime_abs_signedAdvantage_le_lwe_add_masking` | Implemented |
| Finite leftover hash lemma and binary subset-sum two-universality | `FormalProof4FHE.LeftoverHash.leftover_hash_lemma`, `binarySubsetSum_isTwoUniversal` | Implemented |
| Concrete Regev leftover-hash and one-time security bound | `FormalProof4FHE.Regev.maskingAdvantage_le_explicit`, `oneTime_abs_signedAdvantage_le_lwe_add_leftover` | Implemented |
| Scalar error convolution lifts to IID vectors | `FormalProof4FHE.SharedRandomness.vectorErrorConvolution_of_scalar` | Implemented |
| Shared-randomness LWE hardness, Theorem 6 of ePrint 2023/979 | `FormalProof4FHE.SharedRandomness.zmod_advantage_eq_batch` | Implemented |
| Shared-randomness LWE is a nested generalized-SLWE instance | `FormalProof4FHE.GeneralizedSubspaceLWE.shared_problem_eq_generalized`, `sharedSpec_isNested` | Implemented |
| Generalized presentation reduces to ordinary LWE | `FormalProof4FHE.GeneralizedSubspaceLWE.shared_zmod_advantage_eq_batch` | Implemented |
| Adaptive affine-projection SLWE oracle and uniform-response independence | `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.queryImpl`, `evalDist_queryImpl_uniform_of_admissible` | Implemented |
| Exact finite-field full-rank count and rectangular rank-failure bound | `FormalProof4FHE.FiniteFieldRank.rankFailure_exact`, `rankFailure_le` | Implemented |
| Adaptive first-bad rank-loss bound with an independent transcript tape | `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.adaptiveRankLossWithTape_le_pietrzak` | Implemented, conditional on the fixed-overlap bridge |
| End-to-end adaptive SLWE/LWE security accounting | `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.advantage_le_lwe_add_adaptiveRankLoss` | Implemented, conditional on fixed-overlap and simulator-correctness premises |
| Fixed high-rank overlap reduces to the uniform rectangular rank experiment | `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.FixedRankLossBound` | Open proof obligation |
| Concrete LWE-to-adaptive-SLWE simulator and branch correctness | `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.SimulationCorrect` | Open proof obligation |

"Implemented" means the declaration is checked with warnings treated as errors, which rejects
`sorry`; final axiom information is recorded by `FormalProof4FHETest/AxiomAudit.lean`.

The generalized specialization result covers two static, heterogeneous secret views with
independent matrix batches and view-specific errors. The adaptive affine-projection development is
a separate oracle model and does not alter that exact specialization. Its finite rectangular rank
lemma and adaptive union bound are complete; the fixed-overlap linear-algebra bridge and concrete
simulator correctness are deliberately represented as named premises rather than hidden axioms.
