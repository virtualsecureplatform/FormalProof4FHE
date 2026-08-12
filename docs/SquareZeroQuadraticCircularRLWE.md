# Square-zero quadratic-circular RLWE

## Result

Let

```text
R_p    = (Z/pZ)[X]/(X^N + 1),
R_p²   = (Z/p²Z)[X]/(X^N + 1).
```

Write `[x]` for the coefficientwise canonical lift from `R_p` to `R_p²`, and write `p[x]`
for the coefficientwise high-digit embedding. Every target element has a unique decomposition

```text
[u] + p[v].
```

The high-digit image is square-zero:

```text
(p[x]) (p[y]) = 0 mod p².
```

For independent base-ring variables, define the target secret and target error by

```text
S   = [H] + p[T],
eta = [U] + p[E],
```

where `U` is uniform in `R_p`. For any fixed family of public gadget weights `g_j`, the checked
target batch is

```text
(A_j, A_j S + g_j S² + eta_j)_j.
```

Its distinguishing advantage from the matching zero-message batch

```text
(A_j, A_j S + eta_j)_j
```

is at most

```text
Adv_base-RLWE(g) + Adv_base-RLWE(0).
```

Both terms are ordinary common-secret RLWE over `R_p`, with secret `T` and error `E`. The theorem
does not assume circular security, quadratic KDM security, a correlated hint source, NTRU, or a
trapdoor.

## Exact compiler

From a real base-RLWE row

```text
(a, c = a T + E),
```

sample independent `r,U` in `R_p` and the low secret digit `H`. Form

```text
L = [a] + p[r],
A = L - 2 g [H],
B = L[H] + [U] + p[c] - g[H]².
```

The identity

```text
(S - [H])² = 0
```

implies exactly

```text
B = A S + g S² + [U] + p[E].
```

There is no approximation or error replacement in this step.

For a uniform base transcript, the compiler is also exactly uniform. For each fixed `H`, the map
from the four independent base-ring digit vectors to the target mask/body pair has an explicit
inverse. Thus uniformity follows from a bijection, not from a statistical estimate.

## Why two ordinary-RLWE terms appear

The first exact reduction compares the quadratic batch to a uniform transcript. Applying the same
reduction with every gadget weight set to zero compares the zero-message batch to that same
uniform transcript. The triangle inequality gives the two-term bound above. The complete batch is
handled at once, so there is no factor equal to the number of rows or gadget levels.

## BFV relinearization

Suppose the quadratic ciphertext coefficient has an exact gadget decomposition

```text
c2 = sum_j d_j g_j.
```

Using the evaluation-key rows above to eliminate `c2` gives phase

```text
c0 + c1 S + c2 S² + sum_j d_j eta_j.
```

The formal theorem retains exactly this weighted error and introduces no additional algebraic
remainder.

This is enough to remove the nonstandard quadratic-circular assumption for a structured
square-modulus leveled construction. It is not, by itself, a proof for an unchanged BFV
implementation.

## Distributional price and correctness boundary

The reduction changes the admissible key and error laws:

- the modulus must have the form `q = p²`;
- the secret has the two-digit form `S=[H]+p[T]`;
- every evaluation-key error has an independent uniform low digit `U`;
- only the high digit `E` follows the base-RLWE error sampler.

Although `U` is uniform modulo `p`, its centered magnitude is on the order of `p`; relative to the
target modulus `p²`, this is on the order of `1/p`. Thus the error can be relatively small when
`p` is large, but it is not a stock CBD or discrete-Gaussian target error. Likewise, the
two-digit secret is not the usual small binary or ternary BFV secret.

Consequently, the remaining work for a concrete BFV parameter set is not a quadratic-KDM proof.
It is scheme design and quantitative correctness:

1. choose encryption and secret distributions compatible with the two-digit secret;
2. bound fresh-encryption, multiplication, and relinearization noise with the uniform low error
   digit;
3. choose `p`, degree, plaintext modulus, gadget base, and depth so decryption succeeds; and
4. estimate ordinary `R_p` RLWE security for the selected `T,E` source law.

Automorphism or Galois evaluation keys are unnecessary for addition-and-multiplication-only
leveled BFV. They become a separate obligation if rotations, packing permutations, or
bootstrapping are added.

## Formalization boundary

The development proves the reduction first over an abstract two-digit square-zero extension and
then instantiates all algebraic laws for the executable negacyclic carriers `Rq p N` and
`Rq (p*p) N`. The concrete bridge proves coefficientwise digit bijectivity, compatibility with
negacyclic multiplication, and vanishing of high-digit products. The security theorem is then
specialized directly to these executable rings. The pointwise absolute and relative coefficient
bounds are checked over the reals. The optional unit-pivot normal form is checked as an explicit
row-pair bijection together with its exact real-branch identity; turning a search over several
pivot candidates into an asymptotic failure bound is deliberately left at the game-accounting
layer.

The formalization is in:

```text
FormalProof4FHE/RLWE/SquareZeroQuadraticCircular.lean
FormalProof4FHE/RLWE/SquareZeroQuadraticCircularRq.lean
```
