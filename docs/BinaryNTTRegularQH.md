# Regular quadratic-hint RLWE repair

The unconditioned quadratic-hint distribution in ePrint 2026/1730 contains a
publicly detectable bad set. If an NTT coordinate has `u-2s=0`, the hint
reveals that secret coordinate as `s=u/2`. Its total bad mass is approximately
`N/q`, so it cannot be removed by a tighter analysis of the original
distribution.

The repaired assumption samples only regular quadratic hints.

## Definition

Given a desired secret `s`, sample a uniform unit `d` in the split NTT ring and
set

```text
u = 2s+d
v = s²-u*s.
```

Then

```text
s² = u*s+v
u-2s = d
u²+4v = d².
```

The low-depth multiplication and bootstrapping algorithms only require the
first equation, so the change affects key/hint sampling but not their
homomorphic algebra.

## Repaired reductions

### Binary-NTT to regular QH

For an idempotent Binary-NTT secret `b`, the Figure 1 multiplier `a` and offset
`r` induce

```text
newSecret = a*b+r
newGap = a*(1-2b).
```

Because `(1-2b)²=1`, multiplication by this element permutes the units. Lean
proves that

```text
(a,r) -> (newGap,newSecret)
```

is a bijection of `Rˣ × R`. It also proves the complete public maps including
the divided RLWE masks and the random-branch bodies are bijections. Therefore
the repaired forward reduction has no `N/q` loss.

### Regular QH to Binary-NTT

Every square root of a regular discriminant is automatically a unit. This
removes the abort in Theorem 10.

The repaired sampler now takes any deterministic coordinate square-root
routine, computes one root in every NTT coordinate, and samples one independent
Boolean sign per coordinate. Lean proves that:

- every signed root is nonzero and hence a unit of the product ring;
- the normalized secret is pointwise in `{0,1}`;
- the deterministic routine's arbitrary root choices only XOR a fixed vector
  into the fresh sign vector;
- consequently, the normalized secret distribution is exactly uniform
  Binary-NTT;
- the associated affine mask/body transformation is a bijection and preserves
  the complete uniform random branch.

Thus uniform square-root-sign sampling is discharged. A concrete backend only
needs to instantiate the deterministic coordinate square-root interface, for
example using an appropriate finite-field square-root algorithm.

### Regular QH to regular small-secret QH

For the error-to-secret transformation,

```text
newGap = -anchorMask * oldGap.
```

Thus regularity is preserved whenever the selected anchor mask is a unit. The
paper's constant-probability anchor event remains, but it is unrelated to the
removed `N/q` hint defect. Multiple candidate anchors can reduce the abort
probability if desired.

### Small-secret randomization

Secret shifting preserves the gap literally:

```text
(u+2t)-2(s+t)=u-2s.
```

Hence the corrected equal-sample, zero-loss Theorem 19 remains valid for the
regular assumption.

## Formal status

`FormalProof4FHE.RLWE.BinaryNTTSecurity.Regular` contains:

- the direct regular-hint sampler and equation;
- the exact discriminant and unit-gap identities;
- proof that every regular discriminant root is invertible;
- an executable independent-sign root sampler over split NTT coordinates;
- exact equality of the normalized signed-root law and Binary-NTT;
- the reverse affine batch bijection and uniform-body transport;
- bijective forward coin, mask, and random-body transports;
- preservation under secret shifting and error-to-secret conversion;
- exact probabilistic hardness-transfer interfaces for repaired Theorems 5,
  10, and 19.

No `N/q` term remains in this assumption family. Uniform sign sampling for the
reverse reduction is complete. Concrete instantiation still needs a certified
deterministic square-root routine for the selected NTT prime and efficient
uniform product-ring-unit sampling, normally implemented by independently
sampling nonzero NTT coordinates.
