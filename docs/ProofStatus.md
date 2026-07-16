# Proof status

| Result | Lean declaration | Status |
|---|---|---|
| Hidden-bit LWE advantage equals real/uniform distance | `FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage` | Implemented |
| Regev IND-CPA from decisional LWE and a leftover-hash masking term | `FormalProof4FHE.Regev.oneTime_abs_signedAdvantage_le_lwe_add_masking` | Implemented |
| Finite leftover hash lemma and binary subset-sum two-universality | `FormalProof4FHE.LeftoverHash.leftover_hash_lemma`, `binarySubsetSum_isTwoUniversal` | Implemented |
| Concrete Regev leftover-hash and one-time security bound | `FormalProof4FHE.Regev.maskingAdvantage_le_explicit`, `oneTime_abs_signedAdvantage_le_lwe_add_leftover` | Implemented |
| Block-binary key encoding, at-most-one structure, and exact key-space size | `FormalProof4FHE.BlockBinary.pairedBits_atMostOne`, `bits_injective`, `card_key` | Implemented |
| Block-key subset-sum extractor and tight finite leftover-hash bound | `FormalProof4FHE.BlockBinary.extractorHash_isTwoUniversal`, `extractorHash_leftover_tight` | Implemented; numerator improved from `|R|^d` to `|R|^d - 1` |
| Parallel matrix-mask LWE reduces to one randomized ordinary-LWE adversary | `FormalProof4FHE.BlockBinary.matrixMask_advantage_eq_card_mul_randomRowLWE` | Implemented; exact identity retaining cancellation across rows |
| End-to-end block-binary LWE reduction of ePrint 2023/958 | `FormalProof4FHE.BlockBinary.advantage_le_randomized_ordinaryLWE_add_jointGap_capped`, `advantage_le_randomized_ordinaryLWE_analytic`, `advantage_le_of_ordinaryLWEBounds_analytic`, `advantage_le_of_ordinaryLWEBounds_shiftMoment` | Implemented over finite rings with signed masking-side cancellation, an unsplit exact statistical gap, a proved expected-block noise-absorption bound, tight finite extraction, and final caps at one; only one-dimensional distribution-specific shift/moment estimates remain as analytic inputs |
| Scalar error convolution lifts to IID vectors | `FormalProof4FHE.SharedRandomness.vectorErrorConvolution_of_scalar` | Implemented |
| Shared-randomness LWE hardness, Theorem 6 of ePrint 2023/979 | `FormalProof4FHE.SharedRandomness.zmod_advantage_eq_batch` | Implemented |
| Shared-randomness LWE is a nested generalized-SLWE instance | `FormalProof4FHE.GeneralizedSubspaceLWE.shared_problem_eq_generalized`, `sharedSpec_isNested` | Implemented |
| Generalized presentation reduces to ordinary LWE | `FormalProof4FHE.GeneralizedSubspaceLWE.shared_zmod_advantage_eq_batch` | Implemented |
| Adaptive affine-projection SLWE oracle and uniform-response independence | `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.queryImpl`, `evalDist_queryImpl_uniform_of_admissible` | Implemented |
| Exact finite-field full-rank count and rectangular rank-failure bound | `FormalProof4FHE.FiniteFieldRank.rankFailure_exact`, `rankFailure_le` | Implemented |
| Fixed high-rank overlap reduces to the uniform rectangular rank experiment | `FormalProof4FHE.FiniteFieldRank.rankMulFailure_le_rectangular`, `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.fixedRankLossBound_pietrzak` | Implemented |
| Adaptive first-bad rank-loss bound with an independent transcript tape | `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.adaptiveRankLossWithTape_le_pietrzak` | Implemented |
| Concrete affine-fiber LWE simulator and exact real/uniform full-rank branch laws | `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.goodSimulator`, `evalDist_goodSimulator_real`, `evalDist_goodSimulator_uniform` | Implemented |
| Actual adaptive logged-transcript rank-loss bound | `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.probEvent_honestRankLoss_le_pietrzak`, `probEvent_affineHonestRankLoss_le_pietrzak` | Implemented |
| Bounded online LWE source compiles to ordinary matrix batch LWE | `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.batchReduction`, `evalDist_onlineRealGame_eq_batch_game0`, `evalDist_onlineUniformGame_eq_batch_game1` | Implemented |
| End-to-end adaptive SLWE security from ordinary batch LWE | `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.advantage_le_batchLWE_add_rankLoss`, `advantage_le_of_batchLWE` | Implemented; only the public query bound and ordinary-LWE bound remain as theorem hypotheses |

"Implemented" means the declaration is checked with warnings treated as errors, which rejects
`sorry`; final axiom information is recorded by `FormalProof4FHETest/AxiomAudit.lean`.

The generalized specialization result covers two static, heterogeneous secret views with
independent matrix batches and view-specific errors. The adaptive affine-projection development is
a separate oracle model and does not alter that exact specialization. Its concrete reduction now
closes the formerly named fixed-overlap and simulator-correctness obligations and exposes the
resulting ordinary batch-LWE adversary directly.

The block-binary development checks the finite computational reduction without adopting the
lattice estimator's heuristic attack costs as a theorem. Its strongest theorem uses one signed
matrix distinguisher and one randomized row reduction, so it does not separately absolute-value the
two masking sides or the individual row gaps. It also exposes the unsplit distance
`jointStatisticalGap`, which may be smaller than the sum of noise absorption and extraction.

The split analytic route no longer assumes a bound on the full `noiseAbsorptionGap`. It proves that
gap is at most `min(1, m * kℓ / (ℓ+1) * δ_scalar)`: TV translation costs add under successive
shifts, IID products cost at most the sum of coordinate costs, and each flattened bit of a uniform
block key is selected with probability exactly `1/(ℓ+1)`. Here `δ_scalar` is the exact narrow-error
average of the one-dimensional wide-error translation TV. The shift-moment corollary bounds it by
a supplied scalar shift slope times a supplied first-moment bound. Specializing those final scalar
inputs to a concrete discrete-Gaussian/modulus implementation remains distribution-specific.
