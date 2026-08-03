# CVZR from known-suffix prefix-RLWE

`FormalProof4FHE.TFHE.NativeTRGSWCVZRReduction` formalizes the reduction in
`sketch/CVZR.md`. It discharges the auxiliary-input part of the complete-view zero-row premise
when the native KSK and every forwarded auxiliary object can be built publicly from disjoint
prefix-RLWE source rows and the independently sampled suffix.

## Exact algebra

For a split rank-one key `S = E(P) + O(Z)`, the public map

```text
(a, b) ↦ (a, b + a O(Z))
```

sends a real homogeneous row under `E(P)` to a homogeneous row under `S`, preserving its error
exactly. The map is a permutation for every fixed suffix, so it also preserves an exactly uniform
mask/body pair. The checked whole-block version applies this permutation to the complete BRK row
batch at once; there is no row hybrid or row-count loss.

The same result is proved directly for the coefficient representation used by the explicit
prefix-RLWE source: negacyclic convolution is additive in the embedded secret, and adding the
known-suffix convolution is a bijection on the complete coefficient-form row block. Thus the
ring-level statement does not conceal an unproved representation conversion.

For the KSK block, selecting coefficient `κ` gives

```text
[a E(P)]κ = dot(P, Extκ(a)).
```

The extraction map is a signed permutation of all ring-mask coefficients followed by projection
onto the prefix block. Lean proves that a uniform ring mask therefore produces an exactly uniform
prefix mask. Selecting the same coefficient of the ring body and adding a public suffix message
produces the exact native affine TLWE row. The batched theorem retains the complete vector
`(e_r[κ_r])_r`; it does not infer a joint KSK error law from scalar marginals.

## Source and reduction

The module defines the plain source problem explicitly. Its real branch samples a uniform binary
prefix key, uniform rank-one ring masks, and one caller-supplied joint ring-error vector. Its ideal
branch is an independent uniform mask/body batch. It contains no KSK, BRK, or auxiliary token.

An exact compiler has two public branches:

- the real-row branch transports the BRK block and builds the side state;
- the uniform-row branch replaces the BRK block and invokes the same side builder.

On the real source, the compiler must match the two genuine CVZR endpoints. On the uniform source,
only equality of the two constructed views is required. In particular, the side builder does not
need to output a genuine KSK in that endpoint. The disjoint-block theorem proves this equality for
an arbitrary KSK/auxiliary builder once the uniform BRK block is independent of its source blocks.

For every CVZR distinguisher `D`, the checked reduction constructs one prefix-RLWE distinguisher
`B_D` and proves

```text
Adv_CVZR(D) ≤ 2 Adv_PreRLWE(B_D).
```

In the exact case it also proves the sharper identity

```text
Adv_PreRLWE(B_D) = Adv_CVZR(D) / 2.
```

With complete-view total-variation defects `σ₁`, `σ₀`, and `σU`, the bound is

```text
Adv_CVZR(D) ≤ 2 Adv_PreRLWE(B_D) + σ₁ + σ₀ + σU.
```

The same theorem is instantiated directly for the two-copy complete-view carrier used by the
match-and-square argument. Both local views are compiled in one source game, so no coordinate or
view hybrid is introduced.

The canonical Boolean target pair is also proved to have advantage exactly equal to the existing
`completeViewZeroRowReductionAdvantage`. Consequently the former source-bound premise is replaced
directly by twice one prefix-RLWE advantage. The final checked composition substitutes that bound
into the existing prefix-marginal aggregate theorem rather than leaving a separate identification
step outside Lean.

## Remaining assumption boundary

Two premises remain and are stated rather than hidden:

1. The real-source side builder must reproduce the genuine joint KSK/auxiliary law. For the native
   affine KSK this reduces to equality, or an explicitly charged complete-vector distance, between
   the extracted source-error vector and the implementation KSK error vector. Other auxiliary
   objects must likewise be public affine constructions from disjoint source rows.
2. When `E(P)` occupies a proper coefficient block, the resulting assumption is
   prefix-subspace RLWE. Ordinary full-dimensional RLWE does not automatically imply hardness for
   that restricted secret distribution.

Thus the checked implication is

```text
prefix-subspace RLWE + exact/approximate public side builder
  ⇒ complete-view zero-row hardness,
```

with factor two and the displayed complete-view defects. This reduction relies on the BRK rows
being homogeneous. It does not solve secret-message native TRGSW nonce rows, whose public
elimination introduces prefix/suffix or prefix/prefix products.

## Concrete native CBD instantiation

`FormalProof4FHE.TFHE.NativeTRGSWCVZRConcreteInstantiation` now discharges the first premise above
for the native shared-prefix/suffix cloud key with coefficientwise centered-binomial errors. It
provides the exact disjoint row partition, proves the complete extracted KSK error-vector law,
proves whole-BRK uniform preservation, and identifies the complete source-built cloud-key law
with the literal native zero-BRK/uniform-BRK endpoints. Its final theorem leaves only the explicit
binary prefix-subspace RLWE advantage and the factor-two branch loss. See
`docs/NativeTRGSWCVZRConcreteInstantiation.md`.
