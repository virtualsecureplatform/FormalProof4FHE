# Native TRGSW support-sensitive and robust leakage bounds

`FormalProof4FHE.TFHE.NativeTRGSWAggregateRobustLeakage` formalizes the two proof-side refinements
that remained after the exact projected-leakage barrier.

## Support-sensitive cutoff accounting

The previous bridge used one uniform low-frequency certificate `delta` and paid

```text
N_d * delta.
```

The new bridge accepts a separate budget for every frequency. When the budget depends only on
support size, finite indicator-word/subset reindexing and exact powerset counting prove

```text
sum_(frequency in Low_d) delta_(|frequency|)
  = sum_(j=1)^d choose(t,j) * delta_j.
```

This is `sum_lowSubsetFamily_supportBound_eq_binomial`. Theorems
`diagonalGap_le_binomialSupportBounds_add_aggregate` and
`diagonalGap_le_binomialSupportBounds_add_approximateAggregate` retain this exact sum while adding
the signed aggregate gap and both executable Jordan-sampler defects. The endpoint theorem retains
the same support-sensitive expression.

The existing affine-source certificate can be sharpened without adding a premise. Its leakage
removal theorem pays the cardinality of the actual Walsh support. Therefore
`supportSizeLowFrequencyBound_of_certificate` and
`diagonalGap_le_affineCertificateSupportBounds_add_aggregate` derive the explicit term

```text
sum_(j=1)^d choose(t,j) * sqrt(2^(j+1) * delta),
```

instead of using `sqrt(2^(d+1) * delta)` for every support.

This refinement can improve concrete accounting only when the installed source bounds actually
decrease with support size. It does not assert such cryptographic decay.

## Robust deterministic leakage

For a real table `w`, let

```text
D_1(w,a) = sum_x |w(a xor x) - w(x)|.
```

If a shift `a` flips any Walsh character retained by the canonical high-pass measure, finite
Walsh duality gives

```text
2 <= D_1(highPass_d,a)
  <= lambda_d * (D_1(Q_d^+,a) + D_1(Q_d^-,a)).
```

This is `two_le_normalization_mul_sum_translationL1Defects`. It is quantitative: no appeal to an
exact equality or a topological limit is made.

Let `eta` bound the complete plaintext-table `L1` construction defect for each sign and key. If
two different prefixes have the same deterministic leakage, the triangle inequality supplies
four such defects. Therefore

```text
2 <= 4 * lambda_d * eta.
```

For `d + 2 <= t`, `prefix_eq_of_equal_leakage_of_four_mul_normalization_mul_defect_lt_two` proves
that `4 * lambda_d * eta < 2` still forces exact prefix recovery. For normalized probability
tables, `L1` is twice total variation, so a per-instance TV defect `tau` corresponds to
`eta = 2 tau`.

## Randomized leakage

The robust statement is not restricted to a deterministic projection. At an explicitly shared
leakage value, the same four-defect inequality holds for two keys. Hence
`prefix_eq_of_shared_stochasticLeakageValue_of_small_pointwise_defect` proves that, below the same
threshold, stochastic leakage distributions of different prefixes have disjoint supports.

For average rather than pointwise accuracy, define the pairwise overlap

```text
Overlap(k,k') = sum_l min(Pr[L_k=l], Pr[L_k'=l]).
```

Then `two_mul_stochasticLeakageOverlap_le_normalization_mul_averageDefects` proves

```text
2 * Overlap(k,k')
  <= lambda_d * (average defects for both signs and both keys)
```

whenever the two prefixes differ. Thus small average construction error forces nearly disjoint
leakage laws; randomized leakage cannot hide many prefixes while remaining an accurate natural
public-translation builder.

## Consequence

Both refinements are technical and are now discharged. Support-dependent source bounds may still
improve parameter accounting. Approximate or randomized leakage, however, does not create a
negligible-error route around the exponential prefix-recovery barrier. Removing that barrier still
requires a qualitatively different complete-view simulator, a changed key law, a dual mode or
trapdoor, or a stronger aggregate/circular assumption.
