# Ring-aware path from ordinary RLWE to Galois KDM

## What “quadratic KDM is stronger” means

Security for every coefficient-polynomial KDM function of degree at most two would include Galois
KDM, because `S -> sigma(S)` is coefficient-linear. The current square theorem is not such a
function-class theorem. It covers the specific ring-convolution function

```text
S -> g S^2.
```

Ring squaring and a coefficient permutation/sign automorphism are different operators. Ordinary
polarization of ring squares produces public multiplication terms `c S`; it does not produce a
general non-circulant automorphism operator. Therefore the present `S^2` theorem does not imply
Galois-key security.

The repository's adaptive Subspace-LWE theorem also does not immediately supply the missing
extension. Its response is one scalar noisy inner product, with fresh public randomness sampled
for every query. One query can represent one coefficient equation, but issuing one query per
coefficient resamples the mask and loses the defining RLWE correlation: every coefficient of one
ring row must come from the same ring element `A`. The simulator is proved from ordinary matrix
LWE over a finite field and does not provide a shared-mask vector response.

## A ring-aware construction that does preserve the mask

For every desired row, start from one primary ordinary-RLWE sample and a public family of
auxiliary ordinary-RLWE samples under the same secret:

```text
(A, B_0)       with B_0 = A S + e,
(C_i, D_i)     with D_i = C_i S + f_i.
```

Apply the public automorphism to every auxiliary sample:

```text
sigma(D_i) = sigma(C_i) sigma(S) + sigma(f_i).
```

If a public factorization algorithm returns coefficients satisfying

```text
sum_i r_i sigma(C_i) = g,
```

then output

```text
(A, B_0 + sum_i r_i sigma(D_i)).
```

The body is exactly

```text
A S + g sigma(S) + e + sum_i r_i sigma(f_i).
```

All target coefficients still share the original primary ring mask `A`. There is no scalar-query
decoupling.

## Security reduction

The source contains only ordinary common-secret RLWE rows. In the uniform source branch, `B_0` is
uniform independently of every auxiliary mask and body. Adding any public function of the
auxiliary transcript to `B_0` is a permutation, so the compiled target is uniform exactly—even
when the factorization algorithm fails.

For IID source errors, the grouped primary/auxiliary problem is proved distributionally equal to
the repository's standard rank-one batch problem with

```text
targetRows * (auxiliaryCount + 1)
```

samples. Consequently the checked end-to-end bound is

```text
Adv_Galois-real-vs-zero
  <= Gap_factorization-and-induced-noise
     + Adv_standard-source-batch-RLWE
     + Adv_zero-message-batch-RLWE.
```

The compiler and reshaping add no loss.

## Meaning of the remaining gap

The gap compares the desired implementation distribution

```text
A S + g sigma(S) + E
```

with the factorized distribution

```text
A S
  + (sum_i r_i sigma(C_i)) sigma(S)
  + e + sum_i r_i sigma(f_i).
```

It therefore contains only:

1. failure to represent `g`; and
2. mismatch between `E` and the induced error `e + sum_i r_i sigma(f_i)`.

This is more informative than assuming automorphism-KDM, but it is not automatically small.

No deterministic factorizer can succeed for every uniformly sampled auxiliary-mask family when
`g` is nonzero: on the all-zero family every linear combination is zero. A proof must permit a
bad-mask event and bound its probability.

Over a field, one nonzero auxiliary mask can be inverted to represent `g`, but the inverse is
typically large or uniformly distributed. Multiplying a narrow RLWE error by it destroys the
desired narrow-error law. More auxiliary masks create many preimages, but finding an efficiently
samplable short preimage is an inhomogeneous ring-SIS problem. A lattice trapdoor would solve that
algorithmic problem but introduces a dual/trapdoor mode; without a trapdoor, short-preimage
sampling is the genuinely hard part.

## Assessment

The ring-aware route is structurally valid and strictly more informative than the reversible
masked-source route:

- it reduces the computational source term to literal ordinary RLWE;
- it preserves complete shared-mask ring rows;
- it identifies one concrete residual rather than renaming Galois KDM.

It does not yet establish a correct narrow-error parameter. The next theorem would need an
efficient high-success factorizer together with an explicit distributional bound showing that its
weighted auxiliary errors remain compatible with the implementation's target error law. That is
a cryptographic short-factorization problem, not routine Lean plumbing.

The formal development is in
`FormalProof4FHE/RLWE/RingAwareGaloisFactorization.lean`.
