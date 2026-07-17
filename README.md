# FormalProof4FHE

Lean 4 formalizations of security reductions used by lattice-based fully homomorphic encryption.
The repository currently contains a decisional-LWE interface, a concrete Regev one-time IND-CPA
reduction, the block-binary secret reduction of ePrint 2023/958, the shared-randomness LWE hardness
reduction of ePrint 2023/979, and a checked embedding of shared-randomness LWE into a generalized
heterogeneous two-subspace game. It also contains the adaptive affine-projection oracle and
rank-loss accounting needed for the broader Subspace-LWE hardness theorem. The optimized
shared-randomness IKSK is proved to introduce no security assumption beyond the conventional
full-size IKSK between independent keys; BRKs are explicitly outside that comparison.

## Build

Initialize the pinned proof-framework dependency and build the Singularity image:

```bash
git submodule update --init vendor/VCVio
scripts/container-build
scripts/check
```

The generated `build/formalproof4fhe.sif` is intentionally not tracked. Lean, Lake, and all proof
checks run inside the container; no host Lean installation is required.

## Main checked results

- `FormalProof4FHE.Regev.oneTime_abs_signedAdvantage_le_lwe_add_leftover` proves one-time Regev
  security from decisional LWE with the concrete term `sqrt(q^(n+1) / 2^m) / 2`; the finite
  leftover hash lemma and binary subset-sum two-universality are checked in
  `FormalProof4FHE.Probability.LeftoverHash`.
- `FormalProof4FHE.BlockBinary.advantage_le_randomized_ordinaryLWE_add_jointGap_capped` is the
  sharp reduction-specific block-binary-secret LWE theorem over a finite ring. It folds both
  matrix-masking sides and every row transition into one randomized narrow-LWE adversary, retaining
  cancellation, and keeps noise absorption plus extraction as one exact TV distance `Δ_joint`.
  For `k` blocks of length `ℓ`, the bound is
  `min(1, 2kℓ · Adv_narrow(B±) + Δ_joint + Adv_wide)`.
  `advantage_le_of_ordinaryLWEBounds_tight` gives the convenient uniform corollary
  `min(1, 2kℓ · ε_narrow + ε_noise + sqrt((|R|^d - 1) / (ℓ+1)^k) / 2 + ε_wide)`.
  The sharper split theorem `advantage_le_randomized_ordinaryLWE_nonlinear` uses the exact finite
  expectation of `1 - ∏ⱼ(1 - dⱼ)`, where each `dⱼ` is the translation TV of the complete summed
  narrow-error shift in sample `j`. It has no caller-supplied shift, moment, or tail hypothesis and
  is formally no worse than the older bound
  `ε_noise ≤ min(1, m·kℓ/(ℓ+1) · δ_scalar)`.
  `card_keys_with_activeBlockCount` and `probEvent_activeBlockCount_uniform_key` prove the exact
  active-block law `Pr[H=h] = choose(k,h)ℓ^h/(ℓ+1)^k`; `extractorHash_leftover_tight` checks the
  finite extraction constant.
- `FormalProof4FHE.ModularGaussian.torusDistribution` defines the ideal mod-`q` discrete Gaussian
  exactly as `D_ℤ,αq mod q`. `shiftDistance_distribution_le_valMinAbs` proves modular data
  processing through the centered integer lift, and
  `convolutionDistance_le_conditionalShiftCost` proves that mixing the summed error before TV can
  only improve on revealing the shift. These are infinite-support mathematical `PMF`s. They are
  deliberately not identified with an executable `ProbComp`: an implementation has finite support
  and must be analyzed as the actual sampler used by the finite reduction.
- `FormalProof4FHE.FiniteFieldRank.rankFailure_le` proves that a uniform
  `(d + δ) × d` finite-field matrix loses column rank with probability at most
  `2 / |F|^(δ+1)`. `rankMulFailure_le_rectangular` proves the fixed high-rank
  overlap bridge used in Pietrzak's reduction.
- `FormalProof4FHE.SharedRandomness.zmod_advantage_eq_batch` implements Theorem 6 of ePrint
  2023/979 as an exact reduction to ordinary LWE with `m + m` samples. The scalar error-
  convolution premise is proved to lift to IID vectors.
- `FormalProof4FHE.SharedRandomness.KeySwitching.sharedIKSK_advantage_eq_fullIndependent`
  proves the no-new-assumption result for shrinking/shared-randomness IKSKs. A full-size IKSK for
  independent input and output keys encrypts gadget messages for `unusedPrefix || suffix`; its
  public suffix projection has exactly the shared IKSK distribution, which publishes only the
  suffix messages under the retained key. Both real and uniform branches, and hence advantages,
  are equal with no hybrid or IKSK-size factor.
  `sharedIKSK_hardAgainst_of_fullIndependent` states the corresponding bound-preserving transfer
  for arbitrary adversary classes closed under the explicit projection reduction; this is the
  formal no-new-security-assumption statement. `affineIKSK_advantage_eq_lwe` independently gives
  an exact whole-batch reduction to LWE under the retained key, while
  `sampleRestriction_advantage_eq` proves exact monotonicity in the number of LWE samples.
  `twoPairProjection_advantage_eq` applies two independently sampled, possibly heterogeneous IKSK
  projections jointly without a factor-two loss. The theorem does not include or make a claim
  about BRK security.
- `FormalProof4FHE.SharedRandomness.KeySwitching.blockBinarySharedIKSK_advantage_le_of_ordinaryLWEBounds_nonlinear`
  composes that lossless IKSK layer with the checked nonlinear block-binary reduction. Thus, for
  the ePrint 2023/958 retained key, the only cryptographic premises remain the same ordinary-LWE
  bounds already exposed by the block-binary theorem.
- `FormalProof4FHE.GeneralizedSubspaceLWE.shared_problem_eq_generalized` and
  `sharedSpec_isNested` identify shared-randomness LWE with a nested generalized-subspace
  instance.
- `FormalProof4FHE.GeneralizedSubspaceLWE.shared_zmod_advantage_eq_batch` states the resulting
  ordinary-LWE reduction directly in the generalized-subspace presentation.
- `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.advantage_le_batchLWE_add_rankLoss` gives an
  explicit reduction from adaptive affine-projection Subspace LWE to ordinary matrix batch LWE:
  the SLWE advantage is at most the advantage of `batchReduction` plus
  `2 * (Q * (2 / |F|^(δ+1))).toReal`. The affine-fiber simulator, its real and uniform branch
  laws, the adaptive logged-transcript rank bound, and the bounded online-to-batch compilation are
  all checked. Its only operational hypothesis is the adversary's public `Q`-query bound;
  `advantage_le_of_batchLWE` packages the result against a supplied ordinary-LWE bound.

## Trust and proof status

Finished theorem files must build with warnings treated as errors, so any use of `sorry` fails the
check. `FormalProof4FHETest/AxiomAudit.lean`
records the axioms used by the public security theorems. See `docs/ProofStatus.md` for the mapping
between paper statements and Lean declarations.
