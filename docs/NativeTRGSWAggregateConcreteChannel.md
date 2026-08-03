# Concrete native TRGSW aggregate channel

## Result

`FormalProof4FHE.TFHE.NativeTRGSWAggregateConcreteChannel` connects the abstract high-pass
aggregate theorem to the existing complete native BRK/KSK sampler.

For any finite mask sampler, `nativeAggregateView` performs the actual experiment

```text
P <- uniform binary prefix,
C <- mask sampler,
output fixedPrefixMessageView(P, P xor C).
```

The mask is private challenger randomness. The suffix secret, native BRK, suffix KSK, and all
shared-key correlation remain inside `fixedPrefixMessageView`; no marginal BRK/KSK replacement is
made. The acceptance probability of this experiment is proved exactly equal to the weighted
orbit mean whose weight is the real point-mass function of the mask sampler.

Consequently, positive and negative samplers with point masses equal to the normalized Jordan
weights realize the two abstract aggregate games exactly. The resulting theorem bounds the
actual native real-cloud versus independent-message gap by the low-frequency term plus the
acceptance gap of these two concrete native aggregate experiments.

## Certified finite mask compilation

The module also constructs a mathematical `PMF` for each normalized Jordan law and proves its
point masses exactly. A proof-carrying finite ticket table may approximate either PMF. If its
certified total-variation error is `epsilon`, the corresponding native aggregate acceptance
differs from the ideal acceptance by at most `2 epsilon`.

For the two signs, the final executable bridge is therefore

```text
|real - independent|
  <= N_d * lowBound
     + lambda_d * (|AggTablePlus - AggTableMinus|
                   + 2 epsilonPlus + 2 epsilonMinus).
```

`roundedAggregateMaskCertificate` supplies a canonical denominator-bounded certificate. Its
construction is noncomputable proof data: once a ticket table is materialized, its sampler is a
finite executable `ProbComp`. This theorem does not claim that the generic rounded table is the
polynomial-time Krawtchouk sampler from the paper.

## Final conditional theorem

`realCloudKey_conditionalCertifiedAggregateSecurity` specializes the complete native proof to:

1. a low-degree heterogeneous affine-source certificate;
2. the actual positive-versus-negative native aggregate advantage;
3. the two certified mask-sampler errors; and
4. the independent-message endpoint.

All channel normalization, Fourier/Jordan identities, real-cloud distributional equalities, and
sampler-error bookkeeping are discharged internally.

The remaining cryptographic problem is now isolated to bounding the concrete native aggregate
advantage by an accepted full-key zero-row RLWE problem. If that reduction guesses the complete
binary/ternary key, the already-proved Renyi-half concentration factor is exponential and optimal
within the current match-and-square argument. The low-degree joint affine-source reduction and
the final random-message/zero-message endpoint also remain explicit premises.

The source-reduction and concentration problem is stated independently in
`NativeTRGSWAggregateZeroRowHardProblem.md`.
