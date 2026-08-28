# Binary-NTT automorphism common-fixed-subring boundary

`BinaryNTTAutomorphismFixedSubringBoundary.lean` formalizes the technical
boundary encountered when the tower-involution compiler is applied jointly to
several automorphism keys.

## Joint compiler

For a family `sigma_j`, the same public encoder works on every automorphism
and gadget row:

```text
A_(j,i) = (A_tilde_(j,i) - g_(j,i)*sigma_j(H))*H^(-1)
B_(j,i) = B_tilde_(j,i) + A_(j,i)*C + g_(j,i)*sigma_j(C).
```

If the lower-dimensional secret satisfies

```text
sigma_j(T) = T
```

for every `j`, Lean proves the complete real identity

```text
B_(j,i) = A_(j,i)*S + E_(j,i) + g_(j,i)*sigma_j(S),
S = H*T + C.
```

The multi-automorphism transformation has an explicit inverse on the entire
row table. Therefore its full random endpoint is exactly uniform. There is no
row hybrid, statistical loss, or independence assumption between public row
marginals.

## Fixed-secret cardinality

For one fixed-point-free involution with paired NTT coordinates, the fixed
binary vectors are exactly

```text
(t_1,t_1), ..., (t_n,t_n).
```

Lean constructs an equivalence with `n -> Bool` and proves that their support
has cardinality

```text
2^n.
```

Thus the single-involution reduction retains a half-degree Binary-NTT secret.

For an arbitrary transitive permutation family, Lean proves that every common
fixed binary vector is constant. Its common fixed support therefore consists
of exactly two vectors:

```text
(0,...,0) and (1,...,1).
```

The regular action of any finite group on itself is instantiated explicitly
and proved transitive, so its fixed support also has cardinality two.

## Consequence for BGV

The algebraic joint compiler is technically valid, but applying it to a trace
family acting transitively on the relevant NTT coordinates reduces security
to an ordinary RLWE source with only one independent secret bit. This is not a
growing-dimensional Binary-NTT RLWE assumption and cannot justify a secure
parameter family through the current reduction.

This is a limitation of the common-fixed-secret compiler, not an impossibility
theorem for every possible automorphism-key reduction. A complete BGV proof
still needs one of:

- a staged ring-descent construction that preserves a growing source
  dimension at every step;
- a joint automorphism reduction that does not place its source secret in the
  common fixed subring; or
- a constant-coefficient projection circuit that avoids automorphism keys.

## Executable even/odd source transport

The representation-specific even/odd step is already closed by
`EvenSecretReduction.advantage_eq_smallRLWE`. It proves that degree-`2n` RLWE
with an even-embedded secret and the exact product coefficient-error law has
the same advantage as ordinary degree-`n` RLWE with twice the sample count.
This supplies the executable source transport used by the single tower
involution; it is not a remaining cryptographic premise.

## Principal declarations

- `fixedByFamily_eq_of_transitive`
- `transitiveFixedBitsEquiv`
- `card_fixedBits_of_transitive`
- `pairedFixedBitsEquiv`
- `card_pairedFixedBits`
- `regularPermutationFamily_transitive`
- `card_regularFixedBits`
- `familyAutomorphismBatch_real`
- `familyAutomorphismBatch_uniform_evalDist`
- `EvenSecretReduction.advantage_eq_smallRLWE`
