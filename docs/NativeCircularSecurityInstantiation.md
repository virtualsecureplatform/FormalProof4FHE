# Concrete native instantiation of the minimal circular assumption

`FormalProof4FHE.TFHE.NativeCircularSecurityInstantiation` connects the generic three-game
theorem to the literal shared-prefix native TFHE cloud-key samplers already formalized in
`FormalProof4FHE.TFHE.NativeTRGSWCompleteChannel`.

## Exact experiment

The experiment secret is the shared binary prefix. Given an encryption prefix `P` and control
message `M`, `productView P M` invokes `fixedPrefixMessageView P M`. That sampler:

- samples the independent binary suffix;
- forms the full nested ring key;
- generates the complete native BRK encrypting `M`; and
- generates the genuine suffix KSK under the same nested key.

The three games are therefore

```text
self:        P <- binary; NativeCloudKey(P,P),
independent: P,M <- independently binary; NativeCloudKey(P,M),
zero:        P <- binary; NativeCloudKey(P,0).
```

`nativeCloudKeyExperiment_selfSampler_eq_diagonalNativeView`,
`nativeCloudKeyExperiment_independentSampler_eq_independentMessageNativeView`, and
`nativeCloudKeyExperiment_zeroSampler_eq_zeroMessageNativeView` are definitional equalities.
There is no layout or row-order comparison hidden in these statements.

The imported native-channel theorem identifies the diagonal sampler with the pre-existing literal
real implementation-facing cloud-key law. Consequently
`nativeCloudKeyExperiment_selfSampler_evalDist_eq_realCloudKeyView` proves equality of their full
finite distributions, including the retained KSK.

## Minimal concrete assumption

`NativeCorrelationHardAgainst` is the exact remaining nonstandard premise:

```text
NativeCloudKey(P,P)  approximately equals  NativeCloudKey(P,M),
```

where `M` is an independent binary vector. It is not parameterized by arbitrary product-view or
zero-view functions. The BRK format, suffix sampler, KSK sampler, gadget layout, and error
samplers are fixed arguments of the proposition.

This remains a cryptographic assumption. The module proves that it is the only nonstandard term
in the compact native composition; it does not derive the assumption from ordinary RLWE.

## Bundled standard endpoint

`nativeCloudKeySecurity_le_correlation_add_standard` proves

```text
Adv(real native cloud key, ideal)
  <= correlationBound + standardBound.
```

The `standardBound` premise compares the independent-message native view directly with the final
ideal view. It may be discharged in two explicit hops:

```text
independent message -> zero message -> ideal.
```

The generic theorem
`ThreeGameExperiment.standardEndpointHardAgainst_of_independentZero_and_zeroIdeal` proves that
bundling. Thus the shorter bound does not discard either transition or improve a reduction loss
by notation.

## Payload and auxiliary transcript

`nativeCompleteViewExperiment` attaches a prescribed transcript sampled under the encryption
prefix in every game. The transcript may contain a base TLWE ciphertext challenge, public
metadata, or their product. Its games are literal samplers on

```text
(native BRK/KSK cloud key, transcript).
```

`nativeCompleteViewSecurity_le_correlation_add_standard` gives the same two-term bound for this
complete view. Because the transcript is retained during the correlation hop, the assumption
does not silently infer joint security from separate cloud-key and ciphertext marginals.

The constructor currently models a transcript whose private randomness is conditionally
independent of cloud-key generation given the encryption prefix. This matches an independently
sampled base ciphertext challenge. More complicated implementation state must either be encoded
by a genuinely joint sampler or charged through an explicit sampler-alignment theorem.

## What is now technical and what remains cryptographic

The following connections are proved exactly:

- generic coefficient-product games to the reusable three-game hybrid;
- native self, independent, and zero samplers to the concrete native channel;
- native diagonal sampling to the existing real cloud-key law;
- optional payload retention across every game; and
- the compact correlation-plus-standard loss accounting.

The remaining obligations are:

- prove or explicitly assume the concrete native diagonal-to-independent correlation bound;
- discharge the independent-message-to-ideal standard endpoint using the selected joint RLWE/LWE
  source theorem;
- identify a concrete ciphertext/auxiliary sampler with the implementation law; and
- treat correctness separately from confidentiality.

The first item is the genuine cryptographic premise. The others are instantiation and sampler-law
work unless the selected auxiliary transcript introduces a new same-key correlation.
