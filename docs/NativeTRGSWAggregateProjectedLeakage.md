# Native TRGSW aggregate projected leakage

`FormalProof4FHE.TFHE.NativeTRGSWAggregateProjectedLeakage` formalizes the new claims in
`sketch/trgswaggregate.md`.

## Checked positive results

The known-message zero-row construction is represented directly by
`addKnownGadgetToZeroRows`. It proves that public gadget addition converts a homogeneous native
TGSW batch into the desired known-message batch without changing its error vector.
`knownMessageTranslations_uniform_evalDist_eq` proves exact sign erasure on the uniform complete
row source: any two fixed known-message translations have identical distributions.

For an arbitrary deterministic key projection `L`, the module defines the genuine projected
aggregate advantage, the independent fake-leakage two-copy advantage, and

```text
C_half(L(K)) = (sum_l sqrt(Pr[L(K)=l]))^2.
```

`projectedAggregateAdvantage_le_sqrt_matchSquare` proves

```text
Adv_projected <= sqrt(2 * C_half(L(K)) * Adv_two_copy)
```

under the explicit support-cover and square-root-tilted fake-law hypotheses.
`nativeProjectedAggregateGap_le_defects_add_sqrt` adds the two complete-view construction defects
and an external source bound.

`nativeAggregateGap_le_of_approximateErasure` checks the approximate uniform-source variant. If
the uniform signed gap is at most `upsilon`, its contribution is inside the radical:

```text
sigma_plus + sigma_minus
  + sqrt(C_half * (2 * Adv_source + upsilon^2)).
```

The fake-law loss is sharp for this method. `diagonalFunctionalRatio_le_sum_div` proves the
weighted diagonal upper bound, while `diagonalFunctionalRatio_inverseWeightWitness_eq` proves that
the direction `delta(k) = 1 / q(k)` attains `sum_k p(k)/q(k)`. Thus the previously proved
square-root tilt is not merely an artifact of a loose Cauchy--Schwarz step.

## Checked stabilizer barrier

`commonAggregateTranslationInvariant_iff_walsh_eq_one` proves the exact character description of
the common translation stabilizer of the positive and negative canonical aggregate laws:

```text
a stabilizes both laws
  iff
walsh(S, a) = 1 for every S outside the bounded-degree set.
```

The proof includes finite Walsh inversion rather than assuming Fourier injectivity.

Two consequences are checked:

- `commonAggregateTranslationInvariant_iff_eq_zero_of_degree_add_two_le` proves that the
  stabilizer is trivial when `degree + 2 <= t`.
- `commonAggregateTranslationInvariant_iff_evenWalshParity` proves that at cutoff `t - 1` it is
  exactly the even-parity subgroup, represented by the full Walsh character being one.

`prefix_eq_of_equal_leakage_phaseOblivious` then formalizes the natural-builder lower bound. If a
builder chooses known plaintexts as a function only of projected leakage and is exactly correct
for both aggregate signs, two keys with equal leakage have equal binary prefixes whenever
`degree + 2 <= t`.

Rényi-half concentration is proved monotone under deterministic processing in
`halfRenyiConcentration_map_le`. Combining this with an explicit recovery function gives the final
uniform binary-prefix result:

```text
2^t <= C_half(L(K)).
```

This is `twoPow_card_le_projectedLeakageConcentration_of_phaseOblivious`. It is independent of the
suffix carrier size, so a projected builder may remove the suffix factor but cannot remove the
exponential prefix factor in the usual cutoff regime.

The exceptional cutoff is quantified as well.  Full parity of a uniform nonempty binary cube is
an exactly uniform bit, proved by
`halfRenyiConcentration_fullWalshParityBit_uniform_eq_two`.  Therefore
`two_le_projectedLeakageConcentration_of_phaseOblivious_lastCutoff` proves

```text
2 <= C_half(L(K))
```

when `degree + 1 = t`: exact phase-oblivious correctness forces leakage to reveal that parity bit,
but the stabilizer argument alone does not force recovery of the entire prefix at this boundary.

## Boundary

The barrier applies to exact phase-oblivious builders that select known plaintexts and use public
gadget translations of zero rows. It does not rule out nonlinear processing of source bodies, a
source-correlated or synthesized KSK, a dual-mode/trapdoor construction, or directly assuming the
complete aggregate transcript. Those remain cryptographic construction questions rather than
missing finite algebra in this module.
