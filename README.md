# FormalProof4FHE

Lean 4 formalizations of security reductions used by lattice-based fully homomorphic encryption.
The repository currently contains a decisional-LWE interface, a conditional Regev one-time
IND-CPA reduction, the shared-randomness LWE hardness reduction of ePrint 2023/979, and a checked
embedding of shared-randomness LWE into a generalized heterogeneous two-subspace game.

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

- `FormalProof4FHE.Regev.oneTime_abs_signedAdvantage_le_lwe_add_masking` separates Regev security
  into decisional LWE and the remaining statistical masking term.
- `FormalProof4FHE.SharedRandomness.zmod_advantage_eq_batch` implements Theorem 6 of ePrint
  2023/979 as an exact reduction to ordinary LWE with `m + m` samples. The scalar error-
  convolution premise is proved to lift to IID vectors.
- `FormalProof4FHE.GeneralizedSubspaceLWE.shared_problem_eq_generalized` and
  `sharedSpec_isNested` identify shared-randomness LWE with a nested generalized-subspace
  instance.
- `FormalProof4FHE.GeneralizedSubspaceLWE.shared_zmod_advantage_eq_batch` states the resulting
  ordinary-LWE reduction directly in the generalized-subspace presentation.

## Trust and proof status

Finished theorem files must build with warnings treated as errors, so any use of `sorry` fails the
check. `FormalProof4FHETest/AxiomAudit.lean`
records the axioms used by the public security theorems. See `docs/ProofStatus.md` for the mapping
between paper statements and Lean declarations.
