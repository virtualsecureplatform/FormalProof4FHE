# Corrected BFV circular security

The formalization corresponding to `sketch/bfv_circular_security_corrected.tex` is in
`FormalProof4FHE/RLWE/BFVCircularSecurityCorrected.lean`.  It imports the exact algebra and the
corrected computational boundary from `BFVStandardAssumptionCircularSecurity.lean`, and closes the
manuscript's independent high-collision-entropy alternative.

## Computational statement

The earlier module already proves all exact computational transformations:

- adjacent differencing for both `gamma = 0` and `gamma = 1`;
- bijectivity and point-mass preservation of the correlated source map;
- fixed-HNF/invertible-tail knapsack normalization;
- extension-field encoding; and
- the exact finite-field singular-tail product and its `1 / (|F| - 1)` upper bound.

Its final theorem retains every term required by the imported reductions: decision M-LWE,
M-SIS/second preimage, general-distribution statistical loss, both conditioning losses, the folded
knapsack term, and ordinary RLWE.  No search-M-LWE-only conclusion is asserted.  It also proves
that making all folded advantages zero contradicts the positive medium-fold witness in the
number-ring reduction certificate.

## Universal fixed-HNF hashing

For a finite field `F` and a finite row type, define

```text
h_a(x0, xE)[i] = a[i] * x0 + xE[i].
```

`hnfHash_isTwoUniversal` proves two-universality exactly.  If two sources have the same first
coordinate, a collision would force their remaining coordinates to agree.  If their first
coordinates differ, any two colliding seeds are equal.  Thus there are either no colliding seeds
or at most one.

The sign differs from the manuscript's `-a*x0+xE` only by the public seed permutation `a -> -a`.

## Arbitrary-source strong leftover hashing

The repository's previous leftover-hash theorem accepted a uniform input.  This development proves
the nonuniform collision form required here.  `sum_weighted_hash_bucket_sq_eq` identifies the exact
weighted second moment of all hash buckets.  Two-universality then gives

```text
Col((a, h_a(X))) <= Col(X) / |Seed| + 1 / (|Seed| * |Output|).
```

Combining this with the finite collision-to-total-variation theorem yields

```text
TV((a, h_a(X)), (a, U)) <= sqrt(|Output| * Col(X)) / 2.
```

This theorem applies to arbitrary finite `ProbComp` sources; it is not restricted to uniform
random tapes.

## Stock BFV consequence

`gammaStock_to_gammaHNF_evalDist` proves that adjacent differencing maps every stock `gamma`
branch to the affine hash presentation.  The transcript equivalence preserves the uniform law and
therefore preserves total variation exactly.

`collisionProbability_map_equiv` proves that the real and zero correlated-source maps preserve
collision probability.  `collisionProbability_independentPairSampler` proves that independent
secret and error-batch collision probabilities multiply.  Consequently,

```text
TV(stock relinearization key, encryption-of-zero key)
  <= sqrt(|F|^(levels + 1) * Col(secret) * Col(errorBatch)).
```

This is `stock_zero_tvDist_le_sqrt_collision`.  The theorem
`stock_zero_tvDist_le_of_collisionBudget` gives the equivalent parameter-facing condition: if the
quantity inside the square root is at most `target^2`, the circular distance is at most `target`.
Taking `target = 2^(-lambda)` recovers the manuscript's exponentiated collision-entropy statement
without introducing logarithms into Lean.

## Coefficient and support bounds

The two coefficient lemmas are stated against an abstract size function.  Instantiating its
multiplication factor with the negacyclic ring degree and the public-radix multiplication factor
with `B` gives

```text
size(s^2 + e0) <= E + n*S^2,
size(e_i - B*e_(i-1)) <= (B + 1)*E.
```

Finally, `one_le_card_mul_collisionProbability` proves the finite support lower bound on collision
probability.  `coefficientAlphabet_support_obstruction` specializes its consequence to a degree-`n`
secret alphabet and `r` degree-`n` error alphabets:

```text
outputCard <= (secretAlphabetCard^n * errorAlphabetCard^(r*n)) * collisionBudget.
```

This is the log-free necessary condition behind the manuscript's observation that fixed ternary
secret and narrow error alphabets cannot satisfy the statistical theorem as the required output
space grows.  This negative parameter conclusion does not affect the exact algebra or the
corrected conditional computational bound.
