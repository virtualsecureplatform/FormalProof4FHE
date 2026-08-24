# Binary-NTT and quadratic-hint RLWE security reductions

This document records the formalization status of Section 6.1 of Jain, Lin,
Liu, and Saha, *New Techniques for Fast and Shallow FHE Bootstrapping and
Beyond*, IACR ePrint 2026/1730. The supplied reference is
`../refs/2026-1730.pdf`; the initially requested number `2026/1370` was a
transposition.

## Assumptions

The paper introduces three decisional assumptions.

1. Binary-NTT RLWE uses a secret whose NTT coordinates lie in `{0,1}`. In the
   ring this is exactly the identity `s²=s`.
2. Quadratic-hint RLWE samples `u,s` uniformly and publishes
   `v=s²-u*s` together with ordinary RLWE samples under `s`.
3. Small-secret quadratic-hint RLWE uses a small secret in the real branch;
   the random branch retains an independently generated uniform quadratic
   hint.

The finite decision-problem, advantage, exact-map reduction, multiplicative
reduction, and hardness-transfer interfaces are formalized independently of a
particular NTT implementation.

## Checked transformations

### Binary-NTT to a quadratic hint

For an idempotent secret `s`, a unit `d`, and public offset `r`, the paper sets

```text
s' = d*s+r
u' = d+2r
v' = -r²-d*r.
```

The formal proof checks both

```text
s'² = u'*s'+v'
b+a*d⁻¹*r = (a*d⁻¹)*s'+e.
```

### Quadratic hint to an idempotent secret

Given `alpha²=4v+u²`, invertible `alpha`, and an inverse of two, define

```text
beta = (alpha-u)/2
s' = (s+beta)/alpha.
```

The formal proof checks `s'²=s'` and the transformed RLWE sample identity.
The exact Binary-NTT law additionally requires uniformly sampling all square
roots and conditioning on invertibility. That finite NTT-coordinate sampling
claim is deliberately separate from the ring algebra.

### Error-to-small-secret transform

The final error of an `(m+1)`-row QH-RLWE instance becomes the secret of an
`m`-row QH-small-secret instance. Both transformed sample equations and the
real and random quadratic-hint identities are checked.

### Additive secret randomization

Adding a public random shift changes

```text
(u,v,s,b) -> (u+2t, v-u*t-t², s+t, b+a*t).
```

The body and hint identities are checked. Explicit bijections prove:

- `(u,t) -> (u+2t,s+t)` preserves the joint uniform law;
- `(u,z) -> (u+2t,z+t)` preserves a random quadratic hint;
- `(a,b) -> (a,b+a*t)` preserves a uniform RLWE batch.

These establish the distributional ingredients of the corrected same-sample
version of Theorem 19.

### Search-to-decision

The NTT-coordinate secret randomization is represented by XOR. XOR by a fixed
binary vector is proved bijective and maps a uniform binary vector exactly to
a uniform binary vector. In ring notation,

```text
s xor z = s+z-2*s*z
a' = a*(1-2z)
b' = b-a*z,
```

and Lean checks that the new secret remains idempotent, the new mask multiplier
is a unit, and `b'=a'*(s xor z)+e`. The adjacent-hybrid averaging lemma is also
checked. Binary guess/check and majority amplification reuse the repository's
existing finite probability theorems.

## Audit findings

### Theorem 5 has an unaccounted conditioning gap

Figure 1 samples `d` from the units so that division by `d` is possible.
Lemmas 6 and 8 then calculate probabilities as though `d` were uniform over
the entire ring.

The formal algebra gives the invariant

```text
u'-2s' = d*(1-2s).
```

For every idempotent `s`, `(1-2s)²=1`; hence `u'-2s'` is always a unit. The
unconditioned QH distribution contains valid points with nonunit or zero gap,
including `(u',s',v')=(0,0,0)`. Therefore the claimed exact distribution in
Lemmas 6 and 8 is false as written.

A corrected theorem can target QH-RLWE conditioned on an invertible
discriminant root, or charge the statistical distance between that conditioned
law and ordinary QH-RLWE. Under only `q>N`, that distance is not automatically
negligible.

The corrected quantitative theorem is now formalized. In the split NTT model,
write

```text
delta(N,q) = 1-(1-1/q)^N.
```

This is the probability that the discriminant gap has at least one zero NTT
coordinate. Lean proves the elementary bound

```text
delta(N,q) <= N/q.
```

If the real and random conditioned endpoints are each within `delta` of their
unconditioned QH endpoints, the repaired reduction gives

```text
Adv_QH(A) <= Adv_BinNTT(B) + 2*delta.
```

Thus the desired hardness implication is recovered when `N/q` is negligible.
The paper's condition `q>2N` gives only a constant upper bound and is not by
itself sufficient for the asymptotic claim.

### Theorem 19 has a sample-count mismatch

Its statement gives the reduction `m` QH-small-secret samples but asks it to
invoke an adversary expecting `m+1` QH samples. The described additive shift
does not generate an additional valid RLWE sample. The checked transport gives
a stronger zero-loss theorem when both games use the same number of samples;
the published `(m,m+1)` statement needs another argument.

The corrected same-sample hardness theorem is formalized as
`correctedTheorem19_sameSample_hardAgainst`.

### Theorem 20 needs symmetric automorphism-invariant error

Lemma 23 rotates NTT coordinates by applying an odd cyclotomic automorphism.
Its proof uses the fact that this operation permutes coefficient errors and
negates some of them. The error law is unchanged only when the coefficient
distribution is symmetric and IID. This hypothesis is used in the proof but
is absent from the statement of Theorem 20.

The formal interface names this requirement `ErrorAutomorphismInvariant`.
The remaining concrete instantiation must prove it for the selected executable
error sampler and every automorphism used by coordinate recovery.

`CorrectedSearchToDecisionCertificate` now makes this condition a mandatory
field rather than an informal side condition.

## Remaining work

The following are not silently assumed:

1. an executable NTT equivalence between the polynomial quotient and the
   product of finite fields;
2. uniform sampling of all coordinatewise square roots and its conditional
   distribution;
3. the exact probability that a random product-ring element is a unit;
4. an amended Theorem 5 accounting for the conditioning distance;
5. executable signed-permutation invariance for the chosen error sampler;
6. the complete query/runtime accounting connecting the hybrid,
   binary-guess, and majority components.

The ring identities, public bijections, advantage-transfer framework, and
finite loss arithmetic are complete without axioms or admitted statements.
