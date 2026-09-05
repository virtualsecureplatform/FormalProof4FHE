# Consolidated Binary-NTT BGV theorem status

`FormalProof4FHE/RLWE/BinaryNTTBGVConsolidated.lean` is the entry point for
`sketch/binary_ntt_bgv_consolidated.tex`. It separates exact formal results
from the unchanged-scalar CMAS research premise.

## Newly closed in the consolidation layer

- `pairFunctionsEquiv`, `pairedIndexTwoAssembly`, and
  `pairedAdditiveIndexTwoAssembly` construct the concrete split-coordinate
  index-two assembly; `pairedAssembly_real_equation` and
  `pairedAssembly_uniform_evalDist` prove its real equation and exact uniform
  endpoint.
- `scalarAutomorphism_phase` proves the exact affine transport from a
  diagonal-plus-automorphism witness row to the implemented small-secret
  automorphism-key phase.
- `scalarZero_phase` proves the corresponding zero-message transport.
- `affineTransport_bijective` and `affineTransport_uniform_evalDist` prove
  exact preservation of the uniform endpoint.
- `affineTransportBatch_bijective` and
  `affineTransportBatch_uniform_evalDist` lift this to the complete correlated
  row family.
- `exactScalarFrontierReduction` packages the transport as an exact map
  reduction. Its source is deliberately the structured CMAS problem, not
  ordinary Binary-NTT RLWE.
- `orbitCompletionEquiv` and `completeOrbit_uniform_evalDist` prove exact
  Boolean completion of an arbitrary finite orbit.
- `delta_normalizedCoefficient` and
  `abs_delta_boolVector_coefficient` formalize the generic Fourier barrier:
  a response can equal one at its hidden input while every normalized
  character coefficient has magnitude `2^-N`.
- `integerSupport_card_le_energy` and `coefficient_square_le_energy` prove the
  deterministic covariance-to-sparsity core of the narrow-noise affine
  barrier: integral squared energy at most `K` leaves at most `K` nonzero
  coefficient positions and bounds every individual square by `K`.
- `traceDyadicOrders_checked` checks the power-of-two orders of all sixteen
  concrete trace exponents modulo 131072.
- `traceCycleLengths_eq` and `traceCycleCounts_eq` record the corresponding
  concrete orbit-length and orbit-count tables.
- `traceExponents_no_fixed_coordinate` checks that none of those exponents
  fixes a natural NTT coordinate.
- `traceExponents_eq_implementation` connects the consolidation list to the
  existing executable manifest.
- `CompactCoverBGVMixedSource.rnsPrefix19_permuteSlots` proves that the
  selected twenty-to-nineteen-limb prefix map commutes exactly with every
  split-coordinate automorphism.

The definitions `chosenMaskAutomorphismRow`, `chosenMaskZeroRow`, and
`ChosenMaskAutomorphismSecure` name the exact missing computational statement.
No instance of the final security predicate is asserted.

## Imported proved components

The consolidation entry point imports the existing checked developments for:

- Binary-NTT XOR rerandomization, parity extraction, and the isolated
  transposition analysis;
- simultaneous completion and affine compilation for one index-two
  fixed-point-free involution;
- the common-fixed-subring cardinality boundary;
- exact hierarchical public descent, lift, mask uniformity, and recursive
  sample accounting;
- full regular-cover completion, row assembly, joint affine-automorphism
  compilation, quadratic-hint multiplication, automorphism switching, and
  componentwise circuit lifting;
- the concrete scalar BGV trace schedule, exact noise recurrence, mixed-RNS
  sampler, adaptive encryption game, and correctness closure.

## Statements that remain conditional or outside the formal result

1. **Unchanged scalar CMAS.** There is no reduction from ordinary diagonal
   Binary-NTT RLWE to the complete diagonal-plus-permutation source used by
   the sixteen scalar automorphism keys.
2. **Concrete index-two encoder law.** The split-coordinate assembly and its
   exact real/uniform laws are now constructed. The generic factor-two theorem
   still consumes a `SimultaneousEncoderLaws` package tying two disjoint
   assembled source blocks to the automorphism and zero views with the exact
   chosen coefficient-error sampler.
3. **Long-orbit security.** Exact Boolean orbit completion is proved, but it
   is not by itself a computational reduction; the early trace exponents have
   long orbits and very small fixed subrings.
4. **Narrow-noise chosen-mask barrier.** Its diagonal impossibility and
   energy-to-integral-sparsity core are formalized. The remaining analytic
   layer is the conditional covariance identity for mask-dependent
   multipliers and the finite probability/union-bound count.
5. **Generic Fourier barrier.** The delta-function counterexample is now
   formalized, in addition to the existing parity identities and quantitative
   insertion theorems. What remains unavailable is a positive spectral
   structure theorem for RLWE distinguishers.
6. **Native constant extraction.** The split-coordinate trace and its
   schedule are formalized. A quotient-polynomial proof of the Ramanujan-sum
   presentation is not needed by the executable correctness theorem and is
   not claimed by this module.
7. **Staged descent.** The terminal nonlinear refresh at a still-secure bottom
   dimension remains an explicit primitive.
8. **Full regular cover.** The algebraic and exact-uniform compiler is proved.
   The final native-BGV statement remains conditional on a chosen native
   recryption circuit, its strict noise contraction, and the public-key
   masking layer recorded by the regular-cover certificates.
9. **Width-368 compact cover.** No missing-branch transition theorem is
   supplied; full-cover security does not imply compact-cover security.

Thus the strongest currently defensible conclusion is the full regular-cover
existence theorem under its explicit native-correctness and masking premises.
The current two-ring-element scalar implementation remains conditional on
CMAS or on an explicit joint automorphism-key assumption.
