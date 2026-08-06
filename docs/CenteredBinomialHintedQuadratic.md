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

The moment formulas in this section are mathematical targets; the current Lean endpoint proves
the exact compiler identities and the finite density reduction, but not yet these negacyclic
quadratic-form moments or their simultaneous coefficient tail.

## 5. Quantitative obligations that remain

Two estimates determine whether this path yields workable parameters.

1. Hint concentration. Prove or compute a useful upper bound on `C_2(P || P_H P_S)` for the
   binary or ternary product secret and the coefficientwise CBD channel. The expected product-law
   form is a scalar coefficient cost raised to the ring degree. A closed estimate should behave
   like `exp(O(n / eta))`, but that asymptotic bound is not assumed by the formal theorem.

2. Quadratic residual concentration. Prove the coefficient second moments above and then a tail
   bound for the maximum centered coefficient of `Z^2`, or use the independent-product variant.
   A union bound over coefficient tails is sufficient for correctness; a sharper vector bound is
   optional.

After these are available, parameter selection can trade larger `eta`—which reduces hint
leakage—against the resulting `eta * sqrt(n)` residual scale. Until both bounds are instantiated,
the CBD path is a valid conditional security theorem but not yet a positive parameter judgment.

## 6. Formal scope

The formal development checks:

- the generic weighted squared-mean change-of-measure theorem for finite samplers;
- the genuine randomized hint joint law and its independent reference law;
- automatic support coverage;
- the exact finite density-cost formula;
- the two-copy hinted-RLWE reduction;
- the quadratic-versus-zero hybrid;
- equality of the zero endpoint with an explicit ordinary one-sample RLWE reduction;
- the literal centered-binomial one-hint instantiation; and
- the two-independent-hint product-residual identity.

No Gaussian approximation, heuristic independence of `Z` and `Z^2`, or injective decoding claim
is used.
