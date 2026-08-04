# Block-categorical hash-CMUX self-circular TFHE

`FormalProof4FHE.TFHE.Native.BlockCategoricalHashCMUXSelfCircular` formalizes the new
hash-CMUX and projected-mode material in `block_categorical_hash_cmux_self_circular_tfhe.tex`.
The categorical material in Sections 1--18 is reused from `BlockCategoricalSelfCircular`.

## Complete-vector sanitization

`sanitizeBatch` is the literal addition of a raw TLWE batch, a fresh zero encryption, and a
body-only correction. Lean proves

```text
phase(sanitize(raw,R,E0,F)) = phase(raw) + E0 + F.
```

`rerandomizedMaskView_evalDist_eq_independent` proves more than a uniform marginal: after
retaining arbitrary context, a context-dependent raw mask plus an independent uniform mask has
the same joint law as the context paired with a fresh independent uniform mask.

`translatedMaskedBatchView_evalDist_eq_canonical` installs this result in a complete ciphertext
batch. `tvDist_canonicalMaskedBatchView_le_jointError` then applies data processing to the full
joint context/error law. Consequently `tvDist_sanitized_canonical_le` proves the canonicalization
bound

```text
evaluation defect + joint error-law defect.
```

No independence between the evaluator residual and retained public context is assumed.

## Smudging and correctness

`tvDist_conditionalSmudging_le` conditions on a good residual event and charges the bad-event
probability once. Its finite-box and Gaussian specializations retain the pointwise translation
certificate needed by the selected executable sampler.

The finite no-wrap part is fully combinatorial:

- `tvDist_uniformFinset_sameCard` proves that equal-size uniform finite supports have TV equal to
  one minus normalized overlap;
- `card_centeredIntegerInterval_inter_shifted` proves that the overlap of `[-R,R]` and its
  translate has size `(2R+1)-|v|`, with natural subtraction implementing the positive part;
- `centeredIntegerBox_inter_shifted` and `centeredIntegerBox_overlap_fraction_eq` derive the
  Cartesian support intersection and normalized product overlap directly;
- `tvDist_uniformBoxSupport_eq` gives the exact product formula;
- `centeredBoxTranslationDistance_le_l1` and
  `centeredBoxTranslationDistance_le_card_mul` give the L1 and infinity-bound corollaries.

`correctedError_failure_le_residual_bad` proves the actual correctness-event implication: if
correction noise always lies in its advertised box and `B+R<rho`, every decode failure implies a
bad residual. Thus its probability is at most the residual bad-event probability.

There is a boundary correction to the TeX. With the strict condition `B+R<rho`, the valid privacy
bound retains the actual correction radius `R`. Substituting `R=rho-B` makes the denominator
larger and does not preserve an upper bound. `finiteBoxPrivacyClosedBoundary` proves the displayed
`2*(rho-B)+1` denominator only when a closed decoding region or a separate certificate permits
the attained choice `R=rho-B`.

The continuous equal-covariance Gaussian translation inequality is represented by
`GaussianShiftCertificate`; discretization, rounding, and modular wrapping are separate defects.
This is intentional because Mathlib does not currently provide the needed finite wrapped
multivariate Gaussian distribution theorem.

## Wrong candidates and hash loss

`translatedUniformPairView_evalDist_eq_independent` proves that independent uniform fallback
plaintexts make the complete wrong-candidate mask/body carrier exactly uniform jointly with the
retained context. Function types may be used for the mask and body carriers, so this covers the
whole row table at once.

The correct and wrong hash-candidate hybrids charge equality evaluation, CMUX evaluation, and
canonicalization exactly once. `contextualHashLeakageRemoval` is the game-level square-root-tilt
theorem for an arbitrary digest distribution. For a balanced `r`-bit digest, the candidate route
has coefficient

```text
2^r * sqrt(2^(r+1)),
```

and `binaryHashCMUXContextualLoss_sq` proves that its square is exactly `2^(3r+1)`. The final
theorem is `sanitizedSelfCircularSecurity_le`.

The direct projected hidden-mode route reuses the complete-view theorem already proved in
`NativeTRGSWHashLossyCompleteView`. `directProjectedUniformBinaryGap_le` has no additional
candidate-guessing factor, and `directProjectedSanitizedSecurity_le` composes its endpoint
defects.

## Remaining cryptographic boundary

The formal result is for a canonical sanitized view, not automatically the unchanged native
narrow-error view. `target_sub_natural_posSemidef` and
`no_exact_narrow_covariance_after_independent_residual` prove the covariance obstruction.

`HashEqualityEvaluationCertificate` and `SecretMessageSourceCompiler` make the remaining
construction premises explicit. The module does not derive encrypted hash equality or a complete
secret-message BRK from homogeneous ordinary RLWE rows. `nativeNoncePhase_identity` exposes the
missing term `-h*m*S`; for a secret-key message this contains the native quadratic products. A
genuine projected dual mode, a non-black-box native compiler, or the stated contextual source
assumption is still required.
