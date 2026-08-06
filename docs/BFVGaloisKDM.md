# BFV/BGV automorphism and Galois evaluation keys

## Evaluation-key law

A Galois or automorphism switching key contains direct RLWE rows of the form

```text
(A_(i,l), A_(i,l) S + g_l sigma_i(S) + E_(i,l)).
```

Here `sigma_i` is a public ring automorphism, `g_l` is a gadget weight, and every row uses the
same secret `S`. The formal specification contains the complete Cartesian batch of automorphisms
and gadget levels. Repetitions and implementation-specific row orderings can instead be supplied
as an arbitrary indexed specification.

The secret and scalar error samplers are parameters. Consequently the game can retain a binary,
full ternary, or fixed-Hamming-weight ternary secret law and the exact implementation error law;
the theorem does not silently replace either distribution.

## Key-switch correctness

For one automorphism, suppose

```text
sigma(c1) = sum_l d_l g_l.
```

After applying `sigma` to a ciphertext and adding the switching-key rows with digits `d_l`, the
new phase under the original secret is exactly

```text
sigma(c0 + c1 S) + sum_l d_l E_l.
```

Thus a Galois switch introduces only the digit-weighted evaluation-key errors. The equality is
proved over an arbitrary commutative ring and does not use a probabilistic or asymptotic
approximation.

## Security decomposition

The checked game compares the complete real Galois-key batch with the same rows carrying message
zero. Passing through their common uniform transcript gives

```text
Adv_Galois-real-vs-zero
  <= Adv_joint-automorphism-KDM-vs-uniform
     + Adv_ordinary-rank-one-batch-RLWE.
```

The zero-message term is definitionally the ordinary rank-one batch-RLWE problem with the same
secret sampler, row count, and error sampler. There is one automorphism-KDM term for the complete
joint batch, not one hybrid term for every automorphism or gadget row.

For the identity automorphism, the first term also reduces exactly to ordinary RLWE by the
existing direct affine-KDM challenge translation. This closes key switching whose source and
target keys are identical up to a public ring multiplier.

## Why a nontrivial Galois action remains

The ordinary rank-one translation could absorb `sigma(S)` only if there were one public ring
element `m` such that

```text
sigma(S) = S m
```

for every allowed secret. If the support contains `1`, evaluating this equation at `1` forces
`m = 1`. Any other supported secret moved by `sigma` then contradicts the equation. The Lean
theorem proves this for an arbitrary commutative ring and arbitrary secret set.

Full coefficientwise binary and centered-ternary polynomial supports contain `1` and monomial
witnesses moved by every nontrivial coefficient permutation or sign automorphism. Therefore the
unit-witness obstruction applies to those laws. A fixed-Hamming-weight support with weight greater
than one does not contain `1`, including the cloned implementation's sampler. For that case the
formalization provides a second criterion: two supported secrets `S,T` suffice whenever

```text
S sigma(T) != T sigma(S).
```

Concrete witnesses still have to be constructed for each implementation automorphism. These
results reject this particular ordinary rank-one RLWE reduction; they are not attacks on the
scheme and do not prove that the Galois-key distribution is distinguishable.

Coefficientwise, `sigma(S)` is an affine function of the secret vector. A scalar affine-KDM or
Subspace-LWE response can therefore model one output coefficient. It does not immediately model
one complete RLWE row: all output coefficients in that row share the same structured ring mask,
whereas separate scalar Subspace-LWE queries sample fresh randomness. A valid reduction must
retain that common-mask coupling.

## Remaining work for the cloned BFV/BGV implementation

Two obligations remain:

1. Construct executable ring equivalences for the implementation's maps `X -> X^k`, prove that
   they agree with its `ApplyAutomorphism` row ordering and signs, and instantiate the fixed-weight
   cross-mismatch witnesses where applicable.
2. Prove the complete joint automorphism-KDM problem hard, possibly through a ring-aware
   subspace/dual-mode argument that preserves the common mask.

This Galois theorem and the centered-binomial scaled-square theorem cover different parts of the
evaluation key. A final bootstrapping theorem must treat their common-secret joint distribution;
standalone bounds cannot be combined by assuming the two public objects are independent.

The Lean development is in `FormalProof4FHE/RLWE/GaloisKDM.lean`.
