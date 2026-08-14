# BFV circular security through HNF and number-ring knapsack

## Outcome

The finite algebra proposed in `sketch/bfv_standard_assumption_circular_security.tex` is sound,
but its final “standard search M-LWE only” theorem does not follow from the cited black-box
theorems as stated.

The Lean development therefore does two things:

1. it proves all exact algebraic and finite-field transformations used by the proposed route;
2. it gives a corrected proof-carrying security composition that retains every imported
   computational and statistical premise.

No theorem claiming stock BFV circular security from search M-LWE alone is introduced.

## Exact BFV normal form for both branches

For any public scalar `gamma`, Lean defines

```text
b_i = a_i*s + e_i + gamma*B^i*s².
```

The adjacent-difference equivalence gives exactly

```text
beta_i = alpha_i*s + eta_i,

eta_0 = gamma*s² + e_0,
eta_i = e_i - B*e_(i-1).
```

This simultaneously covers `gamma=1`, the quadratic relinearization key, and `gamma=0`, the
zero-message key. For every fixed `gamma`, the source map

```text
(s,e_0,...,e_levels) -> (s,eta_0,...,eta_levels)
```

has an explicit recursive inverse and preserves every point mass.

## Exact HNF--knapsack normalization

Write a matrix-knapsack public matrix as a first column `c` followed by an invertible square tail
`V`. For a source `(x_0,x_E)`, its value is

```text
x_0*c + V*x_E.
```

The public normalization

```text
a = -V⁻¹*c,
z =  V⁻¹*y
```

is an explicit equivalence and satisfies

```text
z = -a*x_0 + x_E = [-a | I]x.
```

The same equivalence maps a fully uniform first-column/output pair to uniform exactly. The only
loss in passing from a completely random square tail to this normalized game is the singular-tail
event. Its exact probability is the checked finite-field product

```text
1 - product_(i=0)^(r-1) (1 - |F|^i / |F|^r),
```

and Lean proves the manuscript's bound

```text
Pr[singular tail] <= 1 / (|F|-1).
```

## Exact extension-field encoding

For any `F`-linear equivalence

```text
iota : F^r ≃ E,
```

the first column and every tail column map bijectively to weights in `E`. Lean proves

```text
iota(K*x) = sum_j x_j • iota(K_j)
```

and proves exact preservation of uniform public weights. This part needs only finite-dimensional
linear algebra; it does not assert that a particular number-ring order satisfies the hypotheses
of an external knapsack theorem.

## First missing premise: general-distribution HNF

The general-distribution M-LWE paper does prove search hardness for bounded sufficient-entropy
sources and transfers it to HNF. Its cited main general-distribution theorem, however, contains
separate computational terms for standard decisional M-LWE and M-SIS/second-preimage resistance,
as well as statistical and parameter losses. The HNF transformation then transports that search
hardness.

Accordingly, `GeneralDistributionHNFReduction` records four separate quantities:

```text
HNF one-way bound
decision M-LWE bound
M-SIS bound
statistical loss.
```

The corrected theorem never labels this collection “search M-LWE alone.”

## Second missing premise: the medium folded family

Mandal--Singh Theorem 3.1 requires all of the following:

- one-wayness of the original bounded knapsack;
- pseudorandomness of specified small-norm folded knapsacks; and
- existence of a medium-norm folded knapsack with noticeable distinguishing advantage.

The manuscript's unit-fold argument makes every relevant folded quotient the zero ring. That
does prove those folded games statistically uniform, but it also sets every folded distinguishing
advantage to zero. It cannot produce the theorem's required positive medium-fold witness.

Lean records the actual interface as `NumberRingKnapsackReduction.mediumFoldWitness` and proves

```text
all fold advantages = 0
  -> no NumberRingKnapsackReduction certificate exists.
```

Thus the unit-fold condition and the omitted distinguishable-fold premise are incompatible when
they refer to the same fold family.

## Corrected BFV bound

The checked end-to-end theorem has the form

```text
Adv_BFV-KDM
 <= Adv_decision-M-LWE
    + Adv_M-SIS
    + loss_general-distribution
    + loss_HNF-to-knapsack
    + loss_folded-knapsack
    + loss_knapsack-to-HNF
    + Adv_ordinary-zero-RLWE.
```

The adjacent BFV transform and extension encoding contribute no loss. The two HNF--knapsack
steps contribute their explicit singular-tail conditioning losses. Any future theorem that
absorbs M-SIS and the folded-knapsack term into a standard assumption can be supplied through
the explicit absorption hypothesis; until then, those are genuine remaining proof obligations.

## Formalization

The implementation is in:

```text
FormalProof4FHE/RLWE/BFVStandardAssumptionCircularSecurity.lean
```

Principal declarations include:

- `adjacent_gammaStockTranscript` and `gammaSourceEquiv`;
- `normalize_invertibleTailKnapsackValue` and `publicNormalizationEquiv`;
- `encode_matrixKnapsackValue` and `weightEncodingEquiv`;
- `squareTailFailureProbability_toReal_eq` and
  `squareTailFailureProbability_toReal_le_inv_card_sub_one`;
- `no_numberRingReduction_of_all_fold_advantages_zero`;
- `corrected_hnfPseudorandomBound`;
- `stockKDMAdvantage_le_corrected_standard_terms`.
