# Proof status

| Result | Lean declaration | Status |
|---|---|---|
| Hidden-bit LWE advantage equals real/uniform distance | `FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage` | Implemented |
| Regev IND-CPA from decisional LWE and a leftover-hash masking term | `FormalProof4FHE.Regev.oneTime_abs_signedAdvantage_le_lwe_add_masking` | Implemented |
| Concrete bound on the Regev leftover-hash masking term | To be assigned | Planned |
| Scalar error convolution lifts to IID vectors | `FormalProof4FHE.SharedRandomness.vectorErrorConvolution_of_scalar` | Implemented |
| Shared-randomness LWE hardness, Theorem 6 of ePrint 2023/979 | `FormalProof4FHE.SharedRandomness.zmod_advantage_eq_batch` | Implemented |
| Shared-randomness LWE is a nested generalized-SLWE instance | `FormalProof4FHE.GeneralizedSubspaceLWE.shared_problem_eq_generalized`, `sharedSpec_isNested` | Implemented |
| Generalized presentation reduces to ordinary LWE | `FormalProof4FHE.GeneralizedSubspaceLWE.shared_zmod_advantage_eq_batch` | Implemented |
| Pietrzak SLWE hardness theorem | To be assigned | Future extension |

"Implemented" means the declaration is checked with warnings treated as errors, which rejects
`sorry`; final axiom information is recorded by `FormalProof4FHETest/AxiomAudit.lean`.

The generalized game currently covers two static, heterogeneous secret views with independent
matrix batches and view-specific errors. The adaptive affine-projection oracle and rank-loss bound
from Pietrzak's SLWE theorem remain a separate future extension; they are not silently assumed by
the specialization result above.
