# Proof status

| Result | Lean declaration | Status |
|---|---|---|
| Hidden-bit LWE advantage equals real/uniform distance | `FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage` | Implemented |
| Regev IND-CPA from decisional LWE and a leftover-hash masking term | `FormalProof4FHE.Regev.oneTime_abs_signedAdvantage_le_lwe_add_masking` | Implemented |
| Finite leftover hash lemma and binary subset-sum two-universality | `FormalProof4FHE.LeftoverHash.leftover_hash_lemma`, `binarySubsetSum_isTwoUniversal` | Implemented |
| Concrete Regev leftover-hash and one-time security bound | `FormalProof4FHE.Regev.maskingAdvantage_le_explicit`, `oneTime_abs_signedAdvantage_le_lwe_add_leftover` | Implemented |
| Block-binary key encoding, exact key space, and exact active-block law | `FormalProof4FHE.BlockBinary.pairedBits_atMostOne`, `bits_injective`, `card_key`, `card_keys_with_activeBlockCount`, `probEvent_activeBlockCount_uniform_key` | Implemented; `Pr[H=h] = choose(k,h)ℓ^h/(ℓ+1)^k` |
| Block-key subset-sum extractor and tight finite leftover-hash bound | `FormalProof4FHE.BlockBinary.extractorHash_isTwoUniversal`, `extractorHash_leftover_tight` | Implemented; numerator improved from `|R|^d` to `|R|^d - 1` |
| Parallel matrix-mask LWE reduces to one randomized ordinary-LWE adversary | `FormalProof4FHE.BlockBinary.matrixMask_advantage_eq_card_mul_randomRowLWE` | Implemented; exact identity retaining cancellation across rows |
| End-to-end block-binary LWE reduction of ePrint 2023/958 | `FormalProof4FHE.BlockBinary.advantage_le_randomized_ordinaryLWE_add_jointGap_capped`, `advantage_le_randomized_ordinaryLWE_nonlinear`, `advantage_le_of_ordinaryLWEBounds_nonlinear` | Implemented over finite rings with signed masking-side cancellation, an unsplit exact statistical gap, assumption-free nonlinear noise absorption, tight finite extraction, and final caps at one |
| Ideal mod-`q` discrete Gaussian and convolution/cancellation comparison | `FormalProof4FHE.ModularGaussian.torusDistribution`, `shiftDistance_distribution_le_valMinAbs`, `convolutionDistance_le_conditionalShiftCost` | Implemented as infinite-support `PMF`s with integer standard deviation `αq`; no identification with a finite executable sampler |
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

The strongest split analytic route no longer assumes any bound on `noiseAbsorptionGap`. It proves
that gap is at most `nonlinearNoiseAbsorptionCost`, the exact finite expectation of a multiplicative
product bound over the actual key and narrow-error matrix. Each per-sample TV is evaluated after the
selected narrow errors have been summed, so additive cancellation is retained. The product remains
on the probability scale, and the formal dominance theorem
`nonlinearNoiseAbsorptionCost_le_min_expected_blocks` proves it is never worse than
`min(1, m * kℓ / (ℓ+1) * δ_scalar)`. The older shift-moment result is only an optional coarser
corollary.

`nonlinearNoiseAbsorptionCost` is an upper bound, not an asserted equality with
`noiseAbsorptionGap`: conditioning on the shared context, deterministic postprocessing, and the
universal independent-product overlap inequality can each be strict for a particular distribution.
The exact quantities remain `noiseAbsorptionGap` and, most sharply for the combined statistical
hop, `jointStatisticalGap`. Likewise, the smaller PMF `convolutionDistance` is applicable when the
summed shift is hidden; it is not substituted into the transcript reduction, where the public
challenge can carry information about the narrow-error matrix.

The paper itself uses a continuous Gaussian on the real torus. The concrete module instead gives
an exact ideal *discrete* specialization suitable for a `ZMod q` model: sample the centered integer
Gaussian with standard deviation `αq`, then reduce modulo `q`. This matches the direct standard-
deviation convention of the TFHE parameter entries in `lattice-estimator`; heuristic attack costs
from the estimator are not treated as proof assumptions. Because ideal discrete Gaussians have
infinite support while `ProbComp` computations have finite support, the formalization does not make
a false exact-sampler identification. The finite reduction is instantiated by the actual executable
sampler; `ModularGaussian` separately specifies the ideal PMF and its exact shift/convolution costs.

The remaining hypotheses in `advantage_le_of_ordinaryLWEBounds_nonlinear` are precisely bounds on
the two ordinary-LWE adversaries. They are cryptographic hardness premises, not statistical or
Gaussian lemmas, and cannot be removed by an information-theoretic reduction.
