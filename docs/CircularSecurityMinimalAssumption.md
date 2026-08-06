# Minimal circular assumptions for true self-key TFHE

`FormalProof4FHE.TFHE.CircularSecurityMinimalAssumption` formalizes the exact algebra,
finite-distribution transformations, assumption hierarchy, and hybrid accounting in
`sketch/tfhe_circular_security_minimal_assumption.tex`.

The result deliberately separates proved transformations from cryptographic premises. It does
not derive native TFHE circular security from ordinary RLWE. Instead, it identifies the smallest
complete-view correlation statement needed by this proof route and proves how that statement
composes with standard independent-message endpoints.

## Complete-view scope

The experiment carrier `View` is unrestricted. A concrete instantiation may include the whole
BRK, a designated same-key auxiliary tape, serialization data, and fixed public state. Thus the
theorems concern the prescribed joint law rather than independent row marginals.

This is not a claim of security under arbitrary auxiliary leakage. The chosen auxiliary
interface must be part of the experiment itself, and any mismatch between its proof sampler and
the implementation sampler remains an explicit whole-view defect.

## Exact message-RLWE closure

For a row `(A,B)` with phase `B-AS`, define the public translation

```text
T_{alpha,beta}(A,B) = (A-alpha, B+beta).
```

`affineTranslateRow_homogeneous` and `phase_affineTranslateRow` prove that applying this map to a
homogeneous row installs exactly the affine plaintext `alpha*S+beta`. The inverse translation is
explicit, so `affineTranslateRow_bijective` proves that it is a permutation.

The construction is lifted coordinatewise to an arbitrary finite complete batch.
`affineTranslateBatch_uniform_evalDist` proves equality of the whole translated and untranslated
uniform laws. This is stronger than a list of rowwise marginal equalities and retains every joint
coordinate of the batch.

The native specializations are exact:

- body placement uses `(alpha,beta)=(0,mu)` and has phase `mu+E`;
- nonce placement uses `(alpha,beta)=(-mu,0)` and has phase `-mu*S+E`.

The second equality is the native secret-message obstruction in normalized message-RLWE form.

## Standard two-branch endpoint

`affineBranchView` samples any public prefix and applies one of two prefix-dependent affine maps
to a complete source batch. On an exactly uniform batch, the two branches have identical
distributions. `affineTargetAdvantage_le_two_sourceBranches` inserts those two uniform branches
and proves that the real branch gap is bounded by the sum of two ordinary real-versus-uniform
source advantages. If both are at most `epsilon`,
`affineTargetAdvantage_le_two_mul_sourceBound` gives

```text
Adv_affine-branch <= 2 epsilon.
```

This factor is proved by an exact complete-batch hybrid; it is not postulated as part of the
circular assumption.

## Public aggregation

`aggregateRows` is a public linear combination of two-component rows, and
`phase_aggregateRows` proves that phase commutes with this operation. For basis coefficients
`u_i`, control bits `p_i`, and the embedding `E(P)=sum_i u_i p_i`, the native identities are

```text
phase(body aggregate)  = g E(P) + E_1,
phase(nonce aggregate) = -g E(P) S + E_2.
```

When `E(P)=S`, `aggregateNativeBodyRows_phase_linear` gives a scaled encryption of `S`.
Negating the nonce aggregate, `aggregateNegativeNativeNonceRows_phase_square` gives

```text
g S^2 - E_2.
```

There is no hidden additional scale in this theorem, and the sign of the aggregate error is
recorded exactly.

## Minimal coefficient-product correlation

`CoefficientProductExperiment` supplies a secret sampler, a complete view indexed by an
encryption secret and a control secret, and a zero-message view. It defines three games:

```text
self:        View(S,S),
independent: View(S,S'),
zero:        ZeroView(S),
```

where `S` and `S'` are independent samples in the middle game. The minimal nonstandard premise
is `CorrelationHardAgainst`: the complete self view is hard to distinguish from the complete
independent-control view. `IndependentZeroHardAgainst` is kept separate because it is the place
where ordinary known-message or zero-row RLWE reductions should be installed.

`oneCircularAdvantage_le_correlation_add_independentZero` proves the exact triangle

```text
Adv_1-circular <= Adv_CP-correlation + Adv_independent-to-zero.
```

`oneCircularAdvantage_le_minimalCorrelation` then substitutes the checked factor-two standard
endpoint and leaves layout and auxiliary defects explicit. The module also exposes the direct
stronger alternative `OneCircularHardAgainst` for a proof that works on the native self view
without the independent-copy intermediate.

## Square correlation and its direction

`SquareExperiment` gives the analogous self, independent-product, and zero games for a projected
scaled-square evaluation key:

```text
SquareView(S,S),  SquareView(S,S'),  ZeroSquareView(S).
```

Its correlation and independent-to-zero premises imply square circular security by the same
exact triangle. `ofCoefficientProjection` applies a deterministic public projection to a
coefficient-product experiment. The theorem
`ofCoefficientProjection_correlationAdvantage_eq` proves data-processing as an equality after
lifting the distinguisher, and `correlationHardAgainst_of_coefficientProjection` transfers the
hardness bound forward.

Only this direction is claimed:

```text
coefficient-product correlation  ==>  projected square correlation.
```

The reverse direction is unavailable because public aggregation discards the individual native
control rows.

The separate hinted-square theorem in
`FormalProof4FHE.RLWE.IntervalMaskedQuadratic` may be used for a modified square evaluation key.
Its generated error law is not automatically the native TRGSW error law, so a concrete evaluator
must supply the corresponding fidelity or evaluation defect.

## End-to-end accounting

Three final theorems expose the intended choices:

- `directOneCircularSecurity_le` uses a direct complete-view one-circular premise;
- `minimalCorrelationSecurity_le` uses coefficient-product correlation plus the standard
  independent-to-zero endpoint;
- `squareKeySecurity_le` uses square correlation for a modified square-key evaluator.

They prove the manuscript's additive bounds while charging every correlation, zero-row source,
zero endpoint, layout, auxiliary, sampler, and evaluator term once. These are literal game
compositions, so the terms cannot silently absorb an unproved sampler or representation match.

## Formal boundary

The following are proved in Lean:

- native nonce/body phase normalization;
- public affine closure and uniform preservation for complete batches;
- the factor-two ordinary source endpoint;
- exact aggregation to scaled `S` and `S^2`;
- self/independent/zero game decompositions;
- forward projection from coefficient-product to square correlation; and
- the final loss accounting.

The coefficient-product correlation, direct native one-circularity, and square-correlation
interfaces are named propositions supplied to the composition theorems. They are not declared as
Lean axioms, but proving one from a standard accepted assumption is still a cryptographic
research obligation. Consequently this module does not by itself certify any current TFHEpp
parameter set. Correctness, concrete source security, implementation sampler alignment, and the
chosen auxiliary interface must be instantiated separately.
