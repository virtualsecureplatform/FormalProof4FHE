# Cost-aware and tagged-source fold-free BFV framework

## Outcome

The new finite claims in `sketch/BFV_fold_free_circular_security_framework.tex` are formalized in
`FormalProof4FHE/RLWE/BFVFoldFreeCircularSecurityFramework.lean`. The module extends the earlier
conditional fold-free BFV development; it does not turn the external general-distribution
interface into a proved standard-M-LWE theorem.

## Fixed-block erratum

For fixed `a`, varying only the randomizer `r` gives

```text
u = a+r,
v = c*u + a*(s-c)+e.
```

Lean proves this affine-line identity and proves that the resulting map from `r` to `(u,v)` is not
surjective over any nontrivial commutative ring. Thus wrong-candidate uniformity requires the
public coefficient and randomizer to be jointly fresh. Independent same-secret blocks may be
reused across candidate tests, but one fixed block cannot be counted as fresh pair samples.

## Joint shared-pivot mask law

The earlier module proved uniformity of one derived mask coordinate. The new module constructs an
explicit equivalence splitting a complete row family into:

```text
(all derived masks, all unused transformed row coordinates).
```

It follows that applying the public invertible row transform, projecting the pivot coordinate,
and negating it maps one canonical uniform row-family law exactly to the canonical uniform law on
the complete derived-mask family. This proves joint uniformity and hence independence across all
indexed rows and blocks.

## Partial-recovery arithmetic

The machine-checked real inequalities include:

```text
delta <= p + (1-p)*(delta/2), delta < 2
  -> delta/(2-delta) <= p,
```

and the weaker `delta/2 <= p` consequence for `0 <= delta <= 1`. Two estimates of one common
wrong-candidate score are proved to differ by at most twice their individual error, while a true
correct-versus-wrong gap decreases by at most twice that error.

These are the deterministic constants used by the manuscript's self-certifying candidate rule.
The Hoeffding theorem, oracle-call cost semantics, and construction of the repeated independent
same-secret samples are not represented by these arithmetic lemmas.

## Mixed-radix unit tags

For a finite source type `W`, base `C`, and tag length `T` satisfying

```text
|W| <= C^T,
```

Lean uses the canonical equivalence `W ≃ Fin |W|` and padded base-`C` digits. It proves that two
distinct sources differ in one of the `T` digits. If the modulus `q` is prime and

```text
1 < C < q,
```

the differing digits remain distinct in `ZMod q`, so their difference is a unit. Mapping that
unit through the algebra map proves the same statement for any target ring algebra over
`ZMod q`.

Appending these tags to arbitrary base source coordinates is injective. Therefore deterministic
tagging preserves every point probability and introduces no min-entropy or statistical loss.

## Exact support-constrained collision theorem

For a public row table `A` and source vector `x`, define

```text
f_A(x) = Aᵀx.
```

If `x-x'` contains a unit coordinate, Lean proves that the additive map

```text
A -> f_A(x)-f_A(x')
```

is surjective. A uniform finite additive-group input therefore produces the exact uniform output
law. Consequently,

```text
Pr_A[f_A(x)=f_A(x')] = 1 / |R^d|.
```

For fixed `x` in a support of cardinality `K`, a finite union bound gives

```text
Pr_A[there exists x' != x with f_A(x')=f_A(x)]
  <= (K-1) / |R^d|.
```

The final theorem instantiates this directly for the mixed-radix tagged source.

## Exact limitation

The collision theorem discharges only a support-constrained second-preimage game whose public map
is exactly `x ↦ Aᵀx` and whose matrix is sampled uniformly from the same complete function space.
It does not discharge:

- unrestricted norm-bounded M-SIS;
- a second-preimage problem with a different source domain;
- a transposed, conditioned, or structured matrix law not proved distributionally equivalent;
- the residual-entropy, norm, sample-count, rank, or residue-degree conditions of an external
  general-distribution theorem.

The remaining decisive step is still to select one precise external theorem and construct its
complete admissibility certificate. The proposed calibration/Hoeffding cost, pivot success,
amplification, and automorphism accounting must also be connected into an actual oracle reduction.

## Principal declarations

- `fixedCoefficientCandidateMap_affineLine`;
- `fixedCoefficientCandidateMap_not_surjective`;
- `derivedMaskFamily_uniform_evalDist`;
- `goodSecretMass_ge` and `halfGap_le_goodSecretMass`;
- `equalScore_estimates_close` and `estimatedCorrectGap_ge`;
- `exists_mixedRadixDigit_ne`;
- `exists_mixedRadixTag_sub_isUnit`;
- `mixedRadixTaggedSource_probOutput`;
- `moduleKnapsackHash_pairCollision_probability`;
- `moduleKnapsackHash_secondPreimage_probability_le`;
- `mixedRadixTaggedSource_secondPreimage_probability_le`.
