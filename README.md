# FormalProof4FHE

Lean 4 formalizations of security reductions used by lattice-based fully homomorphic encryption.
The repository currently contains a decisional-LWE interface, a concrete Regev one-time IND-CPA
reduction, the block-binary secret reduction of ePrint 2023/958, the shared-randomness LWE hardness
reduction of ePrint 2023/979, and a checked embedding of shared-randomness LWE into a generalized
heterogeneous two-subspace game. It also contains the adaptive affine-projection oracle and
rank-loss accounting needed for the broader Subspace-LWE hardness theorem.

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
  `card_key`, `pairedBits_atMostOne`, and `extractorHash_leftover_tight` check the exact key space,
  block structure, and finite leftover-hash constant. The paper-specific Gaussian
  noise-absorption estimate remains the explicit finite `tvDist` premise `ε_noise`.
- `FormalProof4FHE.FiniteFieldRank.rankFailure_le` proves that a uniform
  `(d + δ) × d` finite-field matrix loses column rank with probability at most
  `2 / |F|^(δ+1)`. `rankMulFailure_le_rectangular` proves the fixed high-rank
  overlap bridge used in Pietrzak's reduction.
- `FormalProof4FHE.SharedRandomness.zmod_advantage_eq_batch` implements Theorem 6 of ePrint
  2023/979 as an exact reduction to ordinary LWE with `m + m` samples. The scalar error-
  convolution premise is proved to lift to IID vectors.
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
