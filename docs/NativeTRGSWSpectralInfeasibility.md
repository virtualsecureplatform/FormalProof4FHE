# Native TRGSW suffix-KSK recovery and spectral infeasibility

## Result

`FormalProof4FHE.TFHE.NativeTRGSWSpectralInfeasibility` formalizes the finite claims in
`sketch/nativetrgsw.md`.

The main conclusion is conditional but negative. If the native suffix KSK has ordinary
typical-set unique decoding and the resulting key plus the BRK decryptor recover the hidden
prefix/message with error `epsilon`, then every posterior diagonal Walsh radius is at least

```text
1 - 2 epsilon.
```

Consequently its high-degree sum is at least

```text
(2^t - 1 - sum_(k=1)^d choose(t,k)) * (1 - 2 epsilon).
```

Thus the information-theoretic statistical-decay premise used by the earlier conditional native
theorem cannot be small in a normal correctness regime. This does not break computational LWE or
RLWE security. It shows that computational lattice hardness cannot imply this particular
unbounded-posterior tail premise.

## Exact suffix-KSK decoder bound

For rows

```text
C_j = <U_j,P> + h_j(Z) + E_j
```

and typical sets `Eset_j`, the module proves:

- distinct binary prefixes differ in a coordinate equal to `1` or `-1`;
- that coordinate is a unit over every commutative coefficient ring;
- for every fixed wrong-prefix/suffix candidate, the independent residual vector is exactly
  uniform, not merely statistically close;
- its all-row consistency probability is exactly
  `product_j |Eset_j| / |R|`;
- suffix separation rules out every wrong suffix paired with the correct prefix; and
- exhaustive decoding fails with probability at most

```text
tau_E + (2^t - 1) * |Z| * product_j |Eset_j| / |R|.
```

The `ZMod q` specialization proves that `|R|` is literally `q`. The result is lifted through
arbitrary independent prefix and suffix samplers. No computational-efficiency claim is made for
the exhaustive decoder.

## Concrete TFHEpp lvl10 instantiation

`NativeTRGSWConcreteSuffixSeparation` closes the KSK separation premise for the native
level-1-to-level-0 layout. It models the implementation's binary prefix, centered-ternary suffix,
seven base-four levels, two positive digit multipliers, and all 5516 flattened rows. If two suffix
vectors differ, their top unit-multiplier row has centered code distance at least `2^14`.

Using centered radius `127`, each typical set has at most 255 residues in the `2^16` carrier. For
independent scalar row errors with one-coordinate tail `tau`, exhaustive recovery therefore fails
with probability at most

```text
5516 tau + (2^630 - 1) 3^394 (255 / 2^16)^5516.
```

The second term is formally bounded by `2^-42710`. For the executable centered-binomial sampler
of width at most 127, the first term is exactly zero. For TFHEpp's current
`std::normal_distribution<double>` followed by `dtot16`, establishing the scalar tail requires a
separate exact finite implementation-law certificate; the C++ standard does not specify one
portable normal-distribution algorithm.

## Concrete native lvl01 BRK recovery

`NativeTRGSWConcreteBRKRecovery` closes the correct-key BRK decoder for the native rank-one,
degree-1024, three-level base-64 layout over `ZMod (2^32)`. The constant coefficient of the
selected final-block top row is the encrypted control codeword `0` or `2^26` plus the row error.
Those two codewords have exact centered distance `2^26`.

Consequently, a row-error infinity-norm bound `eta` with

```text
2 eta < 2^26
```

is sufficient to decode one entry. The support theorem for the executable centered-binomial ring
sampler supplies that bound simultaneously for every coefficient and every selected BRK row.
Coordinatewise decoding of all 630 entries therefore has exactly zero failure probability. The
proof accepts an arbitrary level-one ring secret, so binary, ternary, and binary-prefix/ternary-
suffix secret laws all satisfy the deterministic statement.

## BRK and spectral composition

A generic two-stage union theorem proves that key-recovery error plus correct-key BRK decoding
error bounds full `(P,M)` recovery error. A full decoder is then converted to a Boolean predictor
for every diagonal Walsh parity. The existing posterior prediction lemma supplies the pointwise
radius bound, and exact finite character counting supplies the binomial aggregate lower bound.

## Joint affine source

The module packages the conditioned normalized BRK plus retained KSK as one complete-batch
heterogeneous affine source

```text
(A, A x + E)  versus  (A,W).
```

The output may be a product of ring and scalar modules, and `E` is sampled as one complete vector,
so within-batch BRK/KSK correlations are retained. The low-support leakage theorem is restated with
the exact squared-bias loss

```text
sqrt(2^(d+1) * delta).
```

This is a named conditional source assumption, not a reduction to separate ordinary RLWE and LWE
assumptions.

That distinction is necessary: the module formalizes the counterexample

```text
X = R,   Y = R xor B.
```

Each marginal is exactly uniform for either hidden bit, while the joint public xor decoder
recovers `B` with certainty. Separate marginal security therefore cannot imply the required joint
theorem as a black-box statement.

## Random-message endpoint

The random-known-message and zero-message games are at distance at most `2 delta` whenever each is
at distance at most `delta` from the same complete affine reference. The theorem includes the
independent message sampler and arbitrary Boolean continuation explicitly.

## Remaining research boundary

The statistical high-frequency route is now concretely ruled out for the proof-aligned CBD model:
the native KSK separation/false-candidate arithmetic and the correct-key native BRK decoder are
both discharged. A literal theorem about the current `std::normal_distribution` implementation
still needs an exact finite-law sampler compiler; replacing it by the executable CBD sampler makes
that particular obligation disappear. Neither choice can recover statistical spectral decay. The
meaningful security path is computational:

1. reduce the complete heterogeneous affine BRK/KSK source to an accepted joint assumption, or
   state that assumption explicitly; and
2. reduce the now-concrete complete native aggregate high-pass games to a full-key zero-row
   source while avoiding their exponential Renyi-half key-concentration factor.

The finite aggregate identity and its generic match-and-square theorem are proved in
`NativeTRGSWAggregateSecurityAndComplexityLeveraging.lean`; the remaining part of item 2 is the
cryptographic source reduction and loss improvement, not channel construction, Fourier algebra,
or parameter arithmetic. The concrete channel is formalized in
`NativeTRGSWAggregateConcreteChannel.lean`.
