# Native complete-view auxiliary zero-row source

`FormalProof4FHE.TFHE.NativeTRGSWCompleteViewAuxiliarySource` formalizes the finite claims in
`sketch/completeview.md`.

The formal simulator changes only a complete homogeneous BRK row block. It samples an aggregate
mask, forms the known plaintext from the fake prefix and mask, applies native gadget translation,
and forwards the KSK and auxiliary state unchanged. The diagonal theorem accepts an arbitrary
joint source sampler, so correlations among real BRK rows, KSK errors, representation state, and
other auxiliary objects are retained exactly.

The native specialization proves that gadget translation gives the actual body and nonce row
format. It does not substitute the unavailable public-linear nonce expression.

## Uniform-source condition

Exact sign erasure needs more than uniform row marginals. In the uniform source, the replaced row
block must be independent of the jointly sampled KSK/auxiliary side state. The Lean sampler
`independentViewSampler` encodes this condition directly. The KSK and auxiliary state may remain
arbitrarily correlated with each other.

With that condition, every fixed-message native translation has the same law, and therefore the
positive and negative aggregate-mask branches have exactly the same complete output law. If the
uniform rows retain hidden correlations with forwarded side state, this theorem does not apply.

## Quantitative result

For a master key `(P, Z)`, the match-and-square diagonal leakage is `Prod.fst`, not the complete
key. The checked bound is

```text
aggregateGap ≤ sigmaPlus + sigmaMinus
  + sqrt (2 * C_half(P) * completeViewZeroRowSourceBound).
```

The theorem keeps the square-root-tilted fake-prefix sampler as an explicit realizability premise.
The concentration is proved equal to that of the actual prefix marginal even when `P` and `Z` are
correlated. For a uniform binary prefix of length `t` and any nonempty uniform suffix carrier, it
is exactly `2^t`; no suffix factor remains.

The approximate-erasure theorem places the uniform defect inside the second moment:

```text
sqrt (C_half(P) * (2 * sourceAdvantage + uniformGap^2)).
```

The final Fourier composition charges the low-support affine term, aggregate normalization,
positive and negative construction defects, complete-view zero-row source bound, and endpoint
once each.

## Assumption boundary

This module by itself does not reduce the source bound to ordinary RLWE. Its required source is
zero-row RLWE in the presence of the genuine correlated native KSK and auxiliary transcript. The
explicit `conditionalTwoCopySource` definition records the two fresh local views under one latent
master key. The key is not part of the public source transcript. A separate conditional
sign-erasure theorem allows the honest KSK/auxiliary sampler to depend on that latent key while
keeping the uniform row block independent after conditioning.

`NativeTRGSWCVZRReduction` now conditionally discharges that auxiliary-input premise. It constructs
the full-key homogeneous rows and native affine KSK from disjoint samples of a plain known-suffix
prefix-RLWE source, and proves the exact factor-two, approximate, and two-copy reductions. The
remaining premises are an exact or complete-vector-close public side builder and prefix-subspace
RLWE when the binary prefix occupies a proper coefficient subspace. See
`docs/NativeTRGSWCVZRReduction.md`.

The extraction lower-bound theorem also formalizes why adding a token that reveals the prefix is
not a useful way around the loss: if the forwarded KSK then recovers the suffix and real errors lie
in a small typical set, the real/uniform source advantage is at least the real success lower bound
minus the uniform typical-set ratio.

The existing projected-leakage stabilizer theorem remains applicable. For the usual cutoff, an
exact phase-oblivious public-translation simulator must recover the entire prefix, so the `2^t`
factor is optimal within this simulator class. Removing it requires a non-extractive programmable
or dual-mode construction and is not supplied by this module.
