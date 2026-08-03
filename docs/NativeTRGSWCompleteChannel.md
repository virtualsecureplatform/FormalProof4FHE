# Complete native TRGSW channel

`FormalProof4FHE.TFHE.NativeTRGSWCompleteChannel` instantiates the abstract diagonal-spectral
framework with the actual finite shared-prefix/suffix TFHE cloud-key sampler.

## Exact experiment

For a fixed binary prefix `p` and a fixed binary BRK message `m`, the conditional sampler draws
an independent binary suffix, forms the rank-one ring secret from the two pieces, generates every
native TGSW entry encrypting `m`, and generates the retained suffix KSK under the same key. The
correlated BRK and KSK are kept together as one finite view.

The diagonal sampler chooses `p` uniformly and sets `m = p`. Lean proves that this distribution is
exactly the pre-existing native `realCloudKeyView`. The comparison sampler chooses `p` and `m`
independently. Consequently, diagonal and independent channel means are literally the two
adversarial acceptance probabilities; there is no row-marginal approximation.

For negation-symmetric ring error, the public xor action on the BRK is lifted to the whole cloud
key while leaving the correlated KSK unchanged. Lean proves the resulting fixed-prefix,
arbitrary-message distribution identity exactly.

## Conditioned affine source

After conditioning on a known message `m`, a direct TGSW row satisfies

```text
<s,A> + gadgetPhase(s,g,m) + e
  = <s,A - gadgetMaskShift(g,m)> + gadgetBodyShift(g,m) + e.
```

Thus the secret-message product that obstructs an unconditional rowwise reduction becomes an
ordinary affine ring-LWE body in each conditioned game. This is also proved distributionally:
publicly normalizing a structured TGSW sample is exactly an ordinary affine batch-RLWE sampler.
The result is lifted through every independently generated BRK entry, through the retained real
KSK, and through suffix sampling. The resulting equality is a whole-view law preserving the
shared prefix/suffix key, not an argument from separate marginals.

What remains is the cryptographic reduction for that joint affine BRK/KSK source.
`LowDegreeAffineSourceCertificate` records its game identification for each low Walsh frequency
and the corresponding leakage-removal advantage.

The leakage itself is not a tunable proof parameter. For a frequency `S`, Lean restricts the
binary prefix to exactly `S`, proves that the carrier has cardinality `2^|S|`, and derives

```text
leakedAdvantage <= sqrt(2^(d+1) * delta)
```

whenever `|S| <= d`. Hence a completed affine-source certificate automatically supplies every
low-frequency premise of the spectral theorem.

## Decoder sanity boundary

The module defines the exact success probability of a deterministic predictor of a diagonal
Walsh parity from the complete view. A normalized-channel calculation proves

```text
FourierCorrelation = 2 * decoderSuccess - 1.
```

Therefore success at least `1 - epsilon` forces the posterior spectral radius to be at least
`1 - 2 epsilon`; exact recovery forces radius at least one. This prevents an incompatible
spectral-tail premise from silently certifying a channel that already reveals the parity.

## Result and remaining premises

The final theorem applies directly to adversarial acceptance on the actual native cloud-key
sampler. It derives the low-frequency leakage factor internally and gives

```text
|realAcceptance - independentMessageAcceptance| + endpointAdvantage
  <= (sum_{k=1}^d choose(t,k)) * sqrt(2^(d+1) * delta)
       + spectralTail + endpointBound.
```

This is still conditional. The subsequent infeasibility module sharpens the remaining work:

1. construct the low-degree hardness reduction for the now-explicit joint affine BRK/KSK source;
2. reduce the concrete complete native aggregate games to a full-key zero-row source and improve
   their exponential key-concentration loss; and
3. instantiate the two-hop independent-message/zero-message endpoint from the chosen joint
   source theorem.

Under ordinary typical-set separation and correctness, the small statistical radius in the old
item 2 is false: exhaustive KSK plus BRK decoding forces the exact binomial lower bound proved in
`NativeTRGSWSpectralInfeasibility.lean`. The concrete native KSK separation and bounded-CBD
correct-key BRK conditions are discharged in `NativeTRGSWConcreteSuffixSeparation.lean` and
`NativeTRGSWConcreteBRKRecovery.lean`. The finite aggregate replacement and generic
match-and-square reduction are discharged in
`NativeTRGSWAggregateSecurityAndComplexityLeveraging.lean`.
The corresponding actual native positive/negative cloud-key experiments and certified finite
mask-sampler defects are discharged in `NativeTRGSWAggregateConcreteChannel.lean`.

In particular, the module does not claim that a current TFHE parameter set satisfies the spectral
premise. The remaining mathematical research statements are collected in
[`NativeTRGSWRemainingHardProofs.md`](NativeTRGSWRemainingHardProofs.md).
