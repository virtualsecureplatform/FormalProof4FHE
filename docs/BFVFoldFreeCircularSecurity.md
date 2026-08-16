# Corrected fold-free BFV circular-security framework

## Outcome

The fold-free algebra and its quantitative composition from
`sketch/BFVStandardAssumptionCircularSecurity_Corrected.tex` are formalized in Lean. The result is
an explicit conditional framework; it is not an unconditional proof of stock BFV circular
security from standard RLWE or M-LWE.

The checked development separates three kinds of statements:

1. exact finite algebra and probability transport that Lean proves outright;
2. quantitative composition lemmas that Lean proves from named bounds;
3. cryptographic and algorithmic interfaces that the manuscript still has to instantiate.

## Direct CRT candidate randomization

At one split-field coordinate, write a fixed-error row as

```text
(a, a*s + e).
```

For candidate `c` and fresh randomizer `r`, the public transform is

```text
(a, a*s + e) -> (a+r, a*s+e+r*c).
```

For `c=s`, Lean proves that this is the same fixed-error row with fresh coefficient `a+r`. For
`c != s`, Lean constructs the inverse explicitly. Hence the map from `(a,r)` to the output pair
is bijective and the pair is exactly uniform.

The theorem is also lifted through an arbitrary state sampler. The retained state may contain all
other CRT slots, the complete correlated error, and arbitrary leakage; no independence inside
that state is assumed.

The existing `RNSSplitSearchToDecisionCorrelated` module supplies the stronger multirow/RNS
version and the exact hybrid telescoping lemmas. The corrected module reuses that infrastructure
rather than restating candidate estimation as an unproved equality.

## Shared-pivot algebra

Let `P` be an invertible linear map, `A` a target linear map, and

```text
t = P*z + s*u
y = A*z + eta.
```

Define `C=A*P⁻¹`, `alpha=-C*u`, and `w=y-C*t`. Lean proves exactly

```text
w = s*alpha + eta.
```

It also proves the recovery identity

```text
P⁻¹(t-s*u) = z.
```

For a uniformly sampled public row, applying an arbitrary invertible row transformation,
projecting one coordinate, and negating it produces an exactly uniform ring element. This is the
finite distributional fact used by the manuscript's derived-mask argument. Independence of a
whole row/block family must still be connected to the concrete sampler that generates those
rows.

## Grouped correlated-error source

For group secrets `s_h`, block errors `e_hbi`, and optional padding, the compiler replaces every
block error by

```text
eta_hb,0 = gamma*s_h² + e_hb,0
eta_hb,i = e_hb,i - B*e_hb,i-1.
```

Lean gives an explicit equivalence for the complete grouped source, leaving all group secrets and
padding visible. Consequently every correlated output point has exactly the probability of its
unique ordinary-source preimage. The compiler itself therefore incurs no statistical or
min-entropy loss.

This does not establish the residual-entropy, boundedness, rank, dimension, or sample-count
hypotheses of a general-distribution theorem. Those properties concern the full correlated law
and remain separate obligations.

## Dual absorption and the honest endpoint

The dual test is represented by two exact probability premises. If an M-SIS solver succeeds with
probability `p`, the real test accepts with probability at least

```text
p * (1-tailLoss),
```

and the uniform test accepts with probability at most

```text
p * uniformWindowMass.
```

Lean derives

```text
p * kappa <= |Pr[real accept] - Pr[uniform accept]|,
kappa = 1 - tailLoss - uniformWindowMass.
```

When `kappa>0` and the exact imported M-SIS challenge satisfies

```text
MSIS_bound * kappa <= dMLWE_bound,
```

the full weighted general-distribution bound

```text
search <= P1*dMLWE + P2*MSIS + statisticalLoss
```

becomes

```text
search <= (P1 + P2/kappa)*dMLWE + statisticalLoss.
```

The two-branch BFV theorem applies this substitution separately to `gamma=1` and `gamma=0` and
retains one explicit `externalLoss` for partial-CRT estimation, pivot aborts, automorphism
transport, and amplification.

## What remains unproved

The following are not hidden by the Lean endpoint:

- a cost-aware partial-CRT recovery construction from hybrid gaps and repeated same-secret blocks;
- success amplification across groups and CRT slots, including pivot singularity and abort loss;
- a concrete automorphism action that transports the heavy slot while preserving the chosen
  secret and error laws;
- verification that the full grouped error law satisfies every hypothesis of one precise
  general-distribution search theorem;
- identification of that theorem's exact M-SIS or second-preimage matrix distribution and a proof
  that it matches the public matrix used by the dual test;
- the concrete no-wrap, tail, norm, dimension, and positive-`kappa` parameter inequalities.

Until these obligations are closed, the manuscript supports a proposed standard-assumption path,
not a theorem that any current BFV parameter set is circular-secure.

## Formalization

The implementation is in
`FormalProof4FHE/RLWE/BFVFoldFreeCircularSecurity.lean`. Principal declarations include:

- `candidateRandomize_correct` and `candidateCoinMap_jointState_uniform_evalDist`;
- `sharedPivotResidual_eq_derived` and `recoverCommonSecret`;
- `derivedMaskCoordinate_uniform_evalDist`;
- `groupedCorrelatedSourceEquiv` and `groupedCorrelatedSource_probOutput`;
- `dualTest_success_mul_gap_le_absAdvantage`;
- `weightedGeneralDistribution_absorb_moduleSIS`;
- `foldFree_twoBranch_bound`.
