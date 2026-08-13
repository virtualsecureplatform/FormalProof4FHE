# BFV quadratic-circular security

## Exact result

For a stock same-key BFV relinearization-key batch with radix gadget

```text
(a_i, a_i s + e_i + B^i s²),   i = 0,...,levels,
```

the checked adjacent-difference map is

```text
alpha_0 = a_0
alpha_i = a_i - B a_(i-1)

beta_0  = b_0
beta_i  = b_i - B b_(i-1).
```

It is an explicit equivalence over every commutative ring. Its recursive inverse is

```text
a_0 = alpha_0
a_i = alpha_i + B a_(i-1),
```

and the same formula recovers the bodies. Applying it to the stock real transcript gives exactly

```text
(alpha_i, alpha_i s + eta_i),

eta_0 = s² + e_0,
eta_i = e_i - B e_(i-1).
```

Thus every gadget multiple except the first cancels. No modulus change, error replacement,
secret-dependent public operation, approximation, or per-row hybrid is used.

The source-coordinate map

```text
(s, e_0, ..., e_levels)  ->  (s, eta_0, ..., eta_levels)
```

is also an explicit equivalence. Consequently it preserves every point probability, and hence
all probability properties determined by point masses, including min-entropy for finite source
laws. Appending an ordinary public-key error leaves this true: the public-key row is unchanged,
and only the relinearization batch is adjacent-differenced.

## Game theorem

The public transcript equivalence maps the real stock BFV batch exactly to the correlated-HNF
batch. Since it is bijective, it maps a fully uniform transcript exactly to a fully uniform
transcript. Lean proves both directions of the advantage equality:

```text
Adv(stock real, uniform; A)
  = Adv(correlated HNF, uniform; A ∘ inverse)

Adv(correlated HNF, uniform; D)
  = Adv(stock real, uniform; D ∘ forward).
```

The matching zero-message sampler is proved distributionally identical to the repository's
ordinary common-secret batch-LWE problem. When the carrier is an executable RLWE ring, this is
the usual rank-one batch-RLWE endpoint. The triangle inequality therefore gives the exact
conditional bound

```text
Adv(stock real, stock zero; A)
  <= Adv(correlated HNF, uniform; A ∘ inverse)
     + Adv(ordinary zero-message RLWE, uniform; A).
```

The standard BFV relinearization phase identity is checked independently: if
`c2 = sum_i d_i g_i`, relinearization preserves `c0 + c1*s + c2*s²` and adds exactly
`sum_i d_i*e_i`.

## Security boundary

This is not a reduction of the unchanged stock BFV key to ordinary decisional RLWE alone. The
remaining correlated-HNF decisional claim is advantage-preservingly equivalent to stock BFV
quadratic-circular pseudorandomness. The normal form is valuable because it makes every row
linear in `s` and isolates all nonstandard dependence in the explicit source

```text
(s, s²+e_0, e_1-Be_0, ..., e_levels-Be_(levels-1)).
```

A search-hardness result for bounded entropic sources does not, without an additional
search-to-decision theorem and its quantitative hypotheses, prove this decisional claim.

The formalization deliberately records two warnings from the manuscript:

- rewriting a quadratic row as an ordinary linear row shifts its public mask by the hidden
  secret, so it is not a public ordinary-RLWE reduction;
- in the noiseless scalar case, the discriminant is identically a square:
  `a² + 4g(-as+gs²) = (a-2gs)²`.

The square-zero `q=p²` construction is a separate, already formalized variant that does reduce
quadratic circular security to ordinary base-ring RLWE by changing the modulus and secret/error
laws. It should not be confused with this exact normal form for unchanged stock BFV.

## Formalization

The declarations are in:

```text
FormalProof4FHE/RLWE/BFVQuadraticCircularSecurity.lean
```

The main entry points are:

- `adjacentEquiv` and `adjacent_stockTranscript`;
- `correlatedSourceEquiv` and `correlatedSource_probOutput`;
- `correlatedHNFAdvantage_eq_stock_forward` and
  `stockUniformAdvantage_eq_correlatedHNF_reverse`;
- `zeroUniformAdvantage_eq_baseProblem`;
- `stockKDMAdvantage_le_correlatedHNF_add_zero`;
- `joint_adjacent_stockTranscript` and `jointCorrelatedSourceEquiv`;
- `relinearization_phase`, `completeSquare`, and
  `recoverSecret_of_exactSquareLeakage`.
