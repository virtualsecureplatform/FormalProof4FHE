# Centered-binomial hinted quadratic RLWE

This note records the centered-binomial path for proving security of an RLWE encryption of the
square of its own binary or ternary secret. It separates the exact game reduction, which is now
formalized, from the quantitative estimates still needed for parameter selection.

## 1. One randomized hint

Let `S` be the RLWE secret and let `Z` be an independently sampled centered-binomial ring
element. Publish

```text
H = S - Z.
```

Starting from a hinted RLWE row

```text
(H, C, Y),       Y = C S + E,
```

apply the public map

```text
A = C - 2 H,
B = Y - H^2.
```

Direct expansion gives

```text
B = A S + S^2 + E - Z^2.
```

This identity is independent of the distribution of `Z`. In particular, it applies to the
literal finite centered-binomial sampler rather than an ideal Gaussian surrogate.

## 2. Why the interval counting proof cannot simply be reused

A centered-binomial coefficient is generated from many pairs of bits. Different coin rows often
decode to the same coefficient. Consequently, the map from uniform coin tables to the published
hint and secret is not injective. Treating the decoded CBD value as a uniform interval mask would
therefore apply the interval theorem outside its hypotheses.

The replacement is an arbitrary-law change of measure. Write

```text
P(h,s) = Pr[H=h, S=s],
P_H(h) = Pr[H=h],
P_S(s) = Pr[S=s].
```

The reference source samples a genuine marginal hint and then an independent secret:

```text
Q(h,s) = P_H(h) P_S(s).
```

It automatically covers the support of `P`. Define the exact order-two density cost

```text
C_2(P || Q) = sum_(h,s) P(h,s)^2 / Q(h,s).
```

Finite weighted Cauchy--Schwarz proves, for every conditional signed distinguishing gap
`delta(h,s)`,

```text
(E_P delta)^2 <= C_2(P || Q) E_Q[delta^2].
```

The two-copy squared-bias experiment realizes the second moment on the right. Hence the hinted
advantage is bounded by

```text
sqrt(2 C_2(P || Q) Adv_2copy).
```

The complete quadratic-versus-zero hybrid is therefore

```text
Adv_KDM
  <= sqrt(2 C_2(P || Q) Adv_2copy)
     + Adv_zero_endpoint.
```

The last term is the ordinary zero-message RLWE endpoint with effective error `E-Z^2`. The CBD
theorem does not hide that endpoint inside a new circular assumption.

## 3. A two-hint alternative

Sample two independent CBD masks and publish

```text
H_1 = S - Z_1,
H_2 = S - Z_2.
```

Given two same-secret hinted RLWE rows

```text
Y_1 = C_1 S + E_1,
Y_2 = C_2 S + E_2,
```

use

```text
A = C_1 + C_2 - H_1 - H_2,
B = Y_1 + Y_2 - H_1 H_2.
```

Then

```text
B = A S + S^2 + E_1 + E_2 - Z_1 Z_2.
```

The mask residual is now a product of independent ring elements instead of a self-product. This
makes its moment calculation substantially cleaner. It is not automatically a better parameter
choice: two hints reveal more about the same secret, so their density cost is larger, and the
base error contains both `E_1` and `E_2`.

## 4. Expected size of the mask residual

For orientation, suppose the negacyclic degree `n` is even, there is no modular wrap, and the
coefficients are independent CBD variables of width `eta`. One coefficient has

```text
E[Z_i] = 0,
E[Z_i^2] = eta / 2,
E[Z_i^4] = (3 eta^2 - eta) / 4.
```

A direct quadratic-form calculation predicts for a coefficient indexed by `k`

```text
E[((Z^2)_k)^2] = n eta^2 / 2                  if k is odd,
E[((Z^2)_k)^2] = (n eta^2 - eta) / 2          if k is even.
```

For two independent masks,

```text
E[((Z_1 Z_2)_k)^2] = n eta^2 / 4.
```

Thus the typical mask contribution is on the order of `eta * sqrt(n)`, whereas the support-only
bound is on the order of `n * eta^2`. This is the potential correctness gain of the CBD path.

For even negacyclic degree, the mean polynomial `E[Z^2]` is already zero: the two diagonal terms
contributing to each even output coefficient have opposite negacyclic signs. Therefore adding a
public mean correction does not improve the power-of-two cyclotomic case. The useful target is a
second-moment or tail bound, not recentering.

The independent-product formula is now proved in Lean for the centered-coefficient presentation
of two executable CBD coefficient vectors. The proof also gives the per-coefficient inverse-square
tail

```text
Pr[ |(Z_1 Z_2)_k| >= T ] <= n (eta/2)^2 / T^2.
```

The real calculation uses `2 eta < q` to identify modular coefficients with their signed CBD
values. It is now transferred to the product of two actual executable `Rq` samples under the
explicit additional condition

```text
2 n eta^2 < q.
```

This deterministic condition ensures that the complete negacyclic convolution is unchanged by
modular reduction and centered lifting. A finite union bound also gives

```text
Pr[ max_k |(Z_1 Z_2)_k| >= T ] <= n^2 (eta/2)^2 / T^2.
```

The sharper one-mask `Z^2` formulas remain open.

## 5. Closed quantitative bridges

The implementation and concentration bridges needed by the two-independent-mask route are now
formalized.

1. Hint concentration. For adjacent fair-binomial coefficient tables, Lean proves exactly

   ```text
   Delta(p, shift(p)) = 2 / (2 eta + 1).
   ```

   Hence the uniform-binary scalar density cost is exactly

   ```text
   1 + 1 / (2 eta + 1),
   ```

   and its IID degree-`n` product is at most `exp(n/(2 eta+1))`. The executable `eta`-pair sampler
   is proved equivalent to `2 eta` fair bits: every Hamming-weight fiber has cardinality
   `choose(2 eta,k)`, and its modular signed output has the corresponding fair-binomial point mass
   whenever `2 eta < q`. For a uniform ternary secret, the three concrete translated tables are
   normalized and their two adjacent discriminations are proved exact, giving scalar cost at most
   `1 + 4/(2 eta+1)` and product cost at most `exp(4n/(2 eta+1))`.

2. Quadratic residual concentration. The deterministic ring-product bridge, exact moment,
   inverse-square coefficient tail, and finite maximum-coefficient union bound are proved for two
   actual independent `Rq` CBD samples under `2 eta < q` and `2 n eta^2 < q`.

These formulas make the intended tradeoff explicit: larger `eta` reduces hint leakage while
increasing the residual scale `eta * sqrt(n)`. The optional one-mask route still requires the
fourth CBD moment and the fixed-point analysis of the negacyclic square; it is not needed by the
closed two-hint route. A final parameter judgment must instantiate the chosen full ring secret
sampler and evaluate the displayed inequalities, but no implementation-law or residual no-wrap
bridge remains implicit.

## 6. Formal scope

The formal development checks:

- the generic weighted squared-mean change-of-measure theorem for finite samplers;
- the genuine randomized hint joint law and its independent reference law;
- automatic support coverage;
- the exact finite density-cost formula;
- the two-copy hinted-RLWE reduction;
- the quadratic-versus-zero hybrid;
- equality of the zero endpoint with an explicit ordinary one-sample RLWE reduction;
- the literal centered-binomial one-hint instantiation;
- the two-independent-hint product-residual identity;
- the exact adjacent fair-binomial triangular discrimination;
- the exact fair-binomial law of the executable bit-pair coefficient sampler;
- the concrete ternary adjacent-translate certificate;
- binary and ternary IID exponential density-cost bounds; and
- the exact independent-product coefficient moment, per-coordinate tail, and maximum-coordinate
  union bound, both in the real coefficient model and for the actual modular ring product under
  explicit no-wrap hypotheses.

No Gaussian approximation, heuristic independence of `Z` and `Z^2`, or injective decoding claim
is used.
