# TFHE circular-security scope and roadmap

## Why this milestone is required

Base TLWE/RLWE IND-CPA security does not by itself justify publishing a TFHE cloud key. The cloud
key contains encryptions of secret-key material, and its two components form a heterogeneous key
cycle. Any end-to-end TFHE security theorem must therefore prove security of this joint
distribution or retain the unresolved part as an explicit assumption.

The original TFHE construction has the following dependency graph:

```text
TLWE key s
   │  coefficients of s, encrypted as TGSW/TRGSW samples under s''
   ▼
bootstrapping key BK(s → s'')

TRLWE key s'' ── KeyExtract ──▶ extracted TLWE key s'
   │                              │ gadget-scaled coefficients of s',
   │                              │ encrypted as direct TLWE samples under s
   └──────────────────────────────▼
                           key-switch key KS(s' → s)
```

Thus each secret is encrypted, directly or indirectly, under the other key. Treating the two
components as independent public views would erase the security issue that circular security is
supposed to capture.

The original TFHE paper defines the bootstrapping key and key-switching key in this cyclic form,
but its practical security section estimates the component bin-LWE/bin-RingLWE problems
separately. It does not provide a reduction for their joint key-dependent distribution. The Lean
development therefore preserves the paper's exact cloud-key graph while making this missing joint
argument explicit instead of inferring it from the two component estimates.

## Checked abstract hybrid layer

`FormalProof4FHE.TFHE.Circular.CycleSpec` records the two secret samplers, coefficient extraction,
and real/zero-message generators for both evaluation-key components. For an arbitrary payload
generated from the same secrets, it defines the joint games

```text
G0: real BK,  real KS,  payload
G1: zero BK,  real KS,  payload
G1': real BK, zero KS,  payload
G2: zero BK,  zero KS,  payload.
```

`circularAdvantage_le_replacements` checks

```text
Adv_circular ≤ Adv_BK-replacement + Adv_KS-replacement.
```

The continuation layer now checks the opposite ordering as well:

```text
continuationCircularAdvantage_le_keySwitchFirst_add_bootstrapAfter

Adv_circular
  ≤ Adv_KS-first[(real BK, real KS) versus (real BK, zero KS)]
    + Adv_BK-after[(real BK, zero KS) versus (zero BK, zero KS)].
```

Two further triangle theorems prove that the BRK-first and KSK-first intact-cycle costs bound one
another after adding the two post-cut edges. Thus changing the hybrid order cannot make the
circular assumption disappear.

The secret-dependent `Continuation` interface additionally supports the actual symmetric TFHE
IND-CPA order: the adversary sees the cloud key, chooses its messages, and receives a TLWE
encryption under the same hidden scalar key. The continuation-level triangle theorem retains this
correlation rather than treating the challenge as an independent payload.

## Concrete finite-modulus native layer

`FormalProof4FHE.TFHE.Basic` and `TFHE.Native` now instantiate the abstract graph. The checked
finite-modulus model contains:

- scalar TLWE ciphertexts, phase, assembly, encryption, and batched rows over `ZMod q`;
- structured TGSW/TRGSW matrices of homogeneous TLWE rows plus the block gadget matrix;
- binary scalar and binary-polynomial ring keys;
- coefficient key extraction;
- one TRGSW bootstrapping-key ciphertext for each scalar-key bit;
- one direct TLWE key-switch row for each extracted ring-key coefficient and gadget level; and
- real and zero-message cloud-key samplers.

`Native.nativeCycleSpec` connects these samplers to `CycleSpec`, while
`circular_realView_eq_native` and `circular_zeroView_eq_native` prove the view equalities.

The original paper works over the real torus. The executable security games here use `ZMod q` and
the finite negacyclic ring `RLWE.Rq q degree`; error samplers and gadget values are explicit. The
development does not falsely identify an ideal continuous Gaussian with a finite `ProbComp`
sampler.

### Checked finite-sampler replacement loss

`TFHE/SamplerReplacement.lean` isolates the exact statistical cost of changing those explicit
finite samplers. The independent-product inequality, shared public challenges, deterministic
TLWE/TGSW assembly, shared secret sampling, and arbitrary adaptive postprocessing are all lifted
through total variation. For an adaptive query budget `Q`, the checked end-to-end bound is

```text
TV(Game_impl, Game_ref)
  ≤ lweDimension * ((ringRank + 1) * tgswLevels) * TV(ringError_impl, ringError_ref)
    + (ringRank * degree) * keySwitchLevels * TV(kskError_impl, kskError_ref)
    + Q * TV(inputError_impl, inputError_ref).
```

`tvDist_adaptiveRealGame_le` states this for the existing native adaptive game, and
`abs_signedAdvantage_adaptiveReal_le_reference_add` transfers any reference-sampler security
bound to implementation samplers. The final
`abs_signedAdvantage_implementation_le_directBilinear_add_batchLwe_add_replacement` theorem leaves
exactly three terms: the native direct-bilinear circular/KDM advantage under the reference
samplers, ordinary binary-secret batch LWE, and the displayed statistical replacement cost.
`adaptiveHardAgainst_implementation_of_reference` gives the corresponding adversary-class
transfer.

`TFHE/CutCycleSamplerReplacement.lean` composes the same exact finite loss with the alternative
KSK-first proof. Its strongest equal-reference-noise statement is

```text
abs_signedAdvantage_implementation_le_keySwitchFirst_add_three_batchLwe_add_replacement
```

so an implementation is bounded by one native intact-cycle term, two ordinary ring batches, one
ordinary scalar KSK-plus-query batch, and the displayed statistical cost. The implementation KSK
and input samplers need not be equal.

This theorem compares two finite executable `ProbComp` samplers. It deliberately does not turn the
paper's continuous-torus Gaussian into a `ProbComp`.

`Probability/FinitePMFCompiler.lean` supplies a checked finite interface for this remaining model
alignment. A `TicketTable` is a nonempty vector sampled uniformly; repeated outcomes encode exact
rational weights. Lean proves its output probability exactly and defines the finite expression

```text
(1 / 2) * sum_residue |ticketMultiplicity(residue) / ticketCount - targetPMF(residue)|
```

as exactly the PMF total-variation error. `Certificate.ofPointwise` reduces the check further to
one finite inequality per residue. Thus an offline-generated table is untrusted data, while its
claimed error bound is checked in the kernel.

The canonical finite-PMF approximation layer additionally proves existence of such a table for
every PMF on a nonempty finite type. It rounds every mass downward at denominator `D`, assigns the
at most `card` leftover tickets to one distinguished output, and proves pointwise error at most
`(card + 1) / D`. Because its input masses may be irrational, this is a noncomputable finite
witness rather than a uniform efficient table-generation algorithm.

`TFHE/DiscreteGaussianSampler.lean` specializes the target to
`ModularGaussian.torusDistribution q alpha`, the exact centered integer discrete Gaussian with
standard deviation `alpha * q` reduced modulo `q`. Its table sampler is executable; the target PMF
is not. Two tables certified against that common target have scalar TV gap at most the sum of the
certificate errors. Independent coefficient sampling and deterministic polynomial assembly give

```text
TV(ringTableLeft, ringTableRight)
  <= degree * (certificateErrorLeft + certificateErrorRight).
```

The same certificate now also controls smudging translations. For every fixed scalar residual
`r`, `addShiftDistance_scalarSampler_le` proves

```text
TV(r + scalarTable, scalarTable)
  <= 2 * certificateError + idealModularGaussianShiftDistance(r).
```

`addShiftDistance_ringSampler_le_sum_ideal` lifts this coefficientwise to one native ring error.
These are executable finite-sampler theorems: the ideal modular Gaussian appears only on the
right-hand side as an analytic comparison distribution.

`adaptiveReplacementCost_le_certificates` substitutes these scalar and ring estimates into the
complete BRK/KSK/adaptive-query count above. Concrete parameter tables and numerical per-residue
proofs remain inputs to the certificate; this development checks their consequences but does not
silently postulate a finite sampler for an irrational PMF.

### End-to-end theorem with the circular premise exposed

`TFHE/DiscreteGaussianSecurity.lean` composes the model-alignment theorem with the computational
proof. For any query-bounded adaptive adversary,

```text
|Adv_TFHE_implementation|
  <= Adv_native_degree_two_monomial_KDM
     + Adv_binary_secret_batch_LWE
     + certifiedReplacementBound.
```

The first summand is exactly the normalized native BRK-first hop, not a surrogate game: the
monomial sampler and the direct native sampler were previously proved equal. The second summand
contains every KSK row and every adaptive input row under the shared scalar key. The third is the
explicit BRK/KSK/query-weighted ticket-certificate error.

`TFHE/AsymptoticMonomialSamplerReplacement.lean` lifts this statement. In particular,
`implementationSecurityGame_secureAgainst_of_monomialKDM_and_batchLWE` proves negligible
implementation advantage from negligible native monomial-KDM advantage, negligible ordinary
batch-LWE advantage, negligible one-draw sampler gaps, and polynomial evaluation-key growth.
This is the complete conditional theorem corresponding to TFHE with circular security included
as a named cryptographic premise.

This qualification matches the supplied sources. Gentry--Sahai--Waters explicitly invoke a
circular-security assumption when bootstrapping a leveled LWE construction into pure FHE. The
2016 TFHE paper defines the mutually dependent bootstrapping and key-switching keys and estimates
their lattice-attack costs separately, but it does not reduce their joint native key cycle to
ordinary LWE/RLWE. ACPS, BV, and BGK establish positive KDM results for modified encryption or
secret-key geometries; none is definitionally the native TFHE hint generator formalized here.

`TFHE/AsymptoticSamplerReplacement.lean` additionally proves that this complete loss is
negligible. `PolynomialEvaluationKeyGrowth` bounds the BRK and KSK draw counts, while each adaptive
adversary contributes its query polynomial. The theorem
`replacementSecurityGame_advantage_negligible` applies polynomial-times-negligible closure to the
three gaps separately. Consequently
`implementationSecurityGame_secureAgainst_of_directBilinear_and_jointLWE` and its ordinary
batch-LWE specialization transfer the complete reference-sampler asymptotic theorem to the
implementation samplers. Equal scalar noise is needed only for the reference batch-LWE
specialization; the implementation KSK and input samplers may differ if both approximation gaps
are negligible.

`TFHE/AsymptoticCutCycleSamplerReplacement.lean` proves the parallel transfer for the KSK-first
ordering. `implementationSecurityGame_secureAgainst_of_keySwitchFirst_and_three_batchLWE` combines
negligible intact-cycle KDM, three ordinary reference batch-LWE games, and negligible sampler gaps
into negligible adaptive implementation advantage. The checked centered-binomial family exposes
both reference forms directly through `Family.secureAgainst_of_keySwitchFirst_and_*`.

## Checked direct-TLWE security reductions

`FormalProof4FHE.LWE.AffineCircular` first proves an exact one-key result: a fixed batch of direct
fresh LWE rows may encrypt arbitrary public affine functions of its own secret. A simultaneous
challenge/output translation is bijective, so there is no per-row hybrid loss.

`FormalProof4FHE.LWE.MultiKeyAffine` proves the paper-suggested master-mask strengthening. For
`users` independent binary keys of one common dimension, every row under any target key may carry
an arbitrary fixed public affine function of the complete key tuple. The reduction samples one
hidden master key and uniform masks, proves that toggling the master by those masks gives exactly
the independent uniform key-family distribution, and applies a triangular challenge/output
permutation. The checked equality is

```text
Adv_direct-affine-clique(users, samples)
  = Adv_ordinary-binary-LWE(users * samples).
```

There is no user-by-user hybrid or statistical term. Thus direct 1-circular, 2-circular, and
affine-clique hint distributions are covered in this common-vector-LWE model. This implements the
clean affine baseline described in `../circular.md`; it does not import the construction-specific
public-encryption transformations from ACPS.

For the native cloud key, `TFHE.Native.KeySwitchSecurity` proves the cloud-key-only KSK replacement
from two ordinary binary-secret batch-LWE advantages after BRK messages have been zeroed.

The adaptive encryption game needs a stronger construction because the KSK rows and fresh TLWE
challenge share the same hidden scalar key. `FormalProof4FHE.LWE.TwoBlock` formalizes two unequal
sample blocks sharing one secret. Splitting `m₁ + m₂` ordinary samples is an exact bijection when
the error sampler is shared. A heterogeneous variant retains separate error samplers for protocol
objects that use different noise parameters.

`TFHE.Encryption.Security` then places

```text
first block:  (ringRank * degree) * keySwitchLevels KSK rows
second block: 1 adaptive TLWE challenge row
```

in one binary-secret LWE instance. This preserves the hidden-key correlation. Conditional
translation of the first uniform block handles the extracted-key gadget messages, and translation
of the uniform one-row second block masks the adaptively selected challenge message.

The strongest checked theorem is

```text
abs_signedAdvantage_real_le_bootstrap_add_jointLwe
```

which proves

```text
|Adv_TFHE-one-time|
  ≤ Adv_contextual-structured-TRGSW-BK-replacement
    + Adv_joint-binary-LWE(KSK rows, challenge row).
```

The uniform branch of the real-message reduction is already the fair challenge game, so the bound
pays one joint-LWE term rather than separately paying two KSK hybrids and another base-encryption
term. When the KSK and input ciphertext errors use the same sampler,
`abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_same_noise` identifies that computational
term exactly with ordinary binary-secret batch LWE on

```text
((ringRank * degree) * keySwitchLevels) + 1
```

samples. With distinct error samplers, the theorem deliberately states the exact two-noise
shared-secret generalized-LWE problem; it does not silently assume the samplers are equal.

### Fixed-batch query accounting

`TFHE/MultiQuerySecurity.lean` extends this experiment to a public `queryCount`. After seeing the
single cloud key, the adversary chooses two message vectors of length `queryCount` and state. One
fair hidden bit selects a whole vector, and the resulting TLWE batch is returned at once. The
checked joint transcript is

```text
first block:  (ringRank * degree) * keySwitchLevels KSK rows
second block: queryCount TLWE challenge rows
```

The uniform second block is a vector one-time pad, so its winning probability is exactly one
half. Consequently

```text
|Adv_TFHE-fixed-batch(queryCount)|
  ≤ Adv_direct-bilinear-KDM(one whole continuation)
    + Adv_joint-binary-LWE(KSK rows, queryCount challenge rows).
```

With equal scalar error samplers, the LWE term is exactly ordinary binary-secret batch LWE on
`keySwitchSamples + queryCount` samples. There is no per-query circular-security union bound: the
cloud key is replaced once before the whole downstream batch game. The adversary-class theorems
`hardAgainst_of_directBilinear_and_jointLwe` and
`hardAgainst_of_directBilinear_and_batchLwe_same_noise` expose the corresponding closure and
hardness premises.

This remains the simpler fixed-batch multi-challenge notion: both message vectors are selected
before any challenge ciphertext is returned. The separate
`TFHE/AdaptiveEncryptionSecurity.lean` module now supplies the sequential strengthening. Its
adversary is an `OracleComp`; later message pairs may depend on earlier ciphertexts, and an
`IsQueryBound` premise limits charged encryption queries to `queryCount`. The source reduction
consumes one eager LWE row per charged query, and `uniformAdaptive_probOutput_true` proves that the
complete adaptive uniform game wins with probability exactly one half. Its final bound has the
same single circular replacement and the same `keySwitchSamples + queryCount` equal-noise sample
count.

### Asymptotic adaptive security

`TFHE/AsymptoticSecurity.lean` lifts that finite theorem into VCVio's asymptotic security
framework. `Parameters` permits the modulus, dimensions, gadgets, encodings, and error samplers
to vary with the security parameter. A `PolynomialQueryAdversary` supplies both its sequential
native adversary and a polynomial witnessing the maximum number of encryption-oracle queries.
The target games are not abstract placeholders: `directBilinearSecurityGame` evaluates the exact
native intact-cycle direct-bilinear continuation, while `jointLWESecurityGame` preserves the exact
two-noise shared-secret LWE transcript. When key-switch and input samplers coincide,
`batchLWESecurityGame` evaluates the ordinary binary-secret LWE reduction with

```text
(ringRank * degree) * keySwitchLevels + queryCount
```

rows. `securityGame_advantage_le_directBilinear_add_jointLWE` lifts the general checked finite
inequality pointwise from `ℝ` to `ℝ≥0∞`; the corresponding equal-noise theorem replaces its joint
term by batch LWE. Closure of efficient adversaries under the concrete reductions, negligibility
of the direct-bilinear KDM advantage, and negligibility of the appropriate LWE advantage imply

```text
secureAgainst_of_directBilinear_and_jointLWE:
  negligible Adv_native-adaptive-TFHE

secureAgainst_of_directBilinear_and_batchLWE (equal scalar noise):
  negligible Adv_native-adaptive-TFHE.
```

`PolynomialKeySwitchGrowth` and `batchSampleCount_le_polynomial` separately verify that the full
LWE transcript has polynomially many rows whenever ring rank, ring degree, and KSK level count
have polynomial bounds. Thus the query/sample accounting is no longer merely informal in the
asymptotic statement. This packaging does not discharge the native circular assumption; it shows
exactly how a negligible bound for that assumption composes with standard batch-LWE security.
`PolynomialEvaluationKeyGrowth` strengthens the accounting to every BRK and KSK error draw, and
the sampler-replacement theorem uses it to prove that negligible one-draw approximation gaps stay
negligible in the full adaptive execution.

#### Finite centered-binomial instantiation

`TFHE/CenteredBinomialInstantiation.lean` removes the remaining abstract sampler and gadget
fields for a finite centered-binomial TFHE variant. It adds an executable scalar sampler using
the same bit-pair construction as the checked ring sampler, and proves deterministic support
bounds plus exact negation symmetry. `CenteredBinomial.Family.parameters` installs:

- coefficientwise ring centered-binomial BRK errors;
- separate scalar centered-binomial KSK and input errors;
- the checked exact power-of-base ring and scalar gadgets; and
- a parameter-indexed message encoding.

Both gadget reconstruction equations and all three sampler support bounds are checked. The
pointwise theorems `Family.securityGame_advantage_le_monomialKDM_add_jointLWE` and
`Family.securityGame_advantage_le_monomialKDM_add_batchLWE` now state the exact native
degree-two monomial-KDM first hop explicitly. Their asymptotic `secureAgainst` companions show
that negligible monomial-KDM and LWE advantages imply negligible adaptive TFHE advantage.
Because these executable centered-binomial samplers are used directly on both sides, there is no
implementation/reference sampler gap. Equal scalar widths give the ordinary batch-LWE
specialization. `linearModulusFamily` additionally witnesses a fully
specified scalable finite family with modulus and gadget levels linear in the security parameter,
and `linearModulusFamily_polynomialEvaluationKeyGrowth` proves all of its BRK and KSK dimensions
are polynomial.

This module is intentionally not labeled as the original TFHE implementation parameter set. The
2016 paper uses continuous-torus Gaussian notation and an approximate `B_g = 1024`, three-level
decomposition at 32-bit torus precision. The executable project model is finite `ZMod q`, and its
current base gadget proves exact reconstruction under `q ≤ B^levels`. The generic finite-sampler
replacement theorem now supplies all draw-count and postprocessing losses once one-draw
approximation bounds are known. Matching the paper still requires a concrete torus
discretization/truncation with those bounds and an approximate-decomposition security/correctness
bridge.

#### Shared security-and-correctness Boolean family

`TFHE/CenteredBinomialEndToEnd.lean` defines `exactRotationFamily`, with `N = λ + 1` and
`q = 2N` at every security parameter. This exact modulus identity lets the same family feed both
the adaptive security game and the signed-rotation Boolean lookup theorem. The KSK and fresh-input
centered-binomial widths coincide definitionally, and
`exactRotationFamily_polynomialEvaluationKeyGrowth` checks polynomial growth of every evaluation
key dimension.

`secureAgainst_and_refreshCorrect` returns both conclusions for that one family through the
compatibility correctness interface:

- negligible adaptive encryption advantage, conditional on the exact native degree-two
  monomial-KDM premise and ordinary query-counted batch LWE; and
- probability-one fresh native Boolean refresh, conditional on the explicit input and output
  decoding-margin inequalities.

The sharper theorem
`secureAgainst_and_refreshCorrectLinear_of_nativeCircular_ordinarySearchLwe` uses the strongest
checked confidentiality route and `RefreshCorrectLinear`. `TFHE/SharpRotationNoise.lean` proves
that every native signed rotation is a signed coefficient permutation, the sparse factor
`(X^a - 1)` costs at most two copies of its input, and each digit-row convolution costs only one
factor of `N`. Thus each historical BRK row error is charged once and the exponential propagation
factor is absent. The resulting theorem `not_exactRotation_linearOutputMargin_of_pos` shows that
this is still insufficient at `q = 2N`: no positive deterministic BRK row-error bound can satisfy
the output margin for any choice of two output codes. This is a checked parameter obstruction,
not an unresolved proof-bound issue.

`TFHE/DivisibleModulusRotation.lean` decouples these roles. Whenever `2N ∣ q`, the canonical
quotient `ZMod q → ZMod (2N)` is additive, so the body and every mask coordinate reduce to a native
rotation exponent exactly and independently. The closed Boolean lookup theorem therefore works
at a larger divisible coefficient modulus without approximate rounding accumulation.

`TFHE/CenteredBinomialLargeModulusEndToEnd.lean` instantiates that bridge with
`q = 16N^4 = (2N)^4`, base `2N`, four exact gadget levels, and centered-binomial width one for all
ring and scalar errors. Its `outputMargin` theorem proves the complete sharp BRK budget fits the
quarter-modulus code distance for `N ≥ 8` (`λ ≥ 7`), and `refreshCorrect` gives probability-one
fresh Boolean refresh with no remaining arithmetic premise. The combined theorem
`secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe` pairs this unconditional
correctness property with the strongest checked confidentiality route. Confidentiality still
retains native auxiliary-input CircLWE as the circular assumption; the supplied references do not
derive that assumption from ordinary RLWE. This exact divisible-modulus construction is also
distinct from the original TFHE paper's torus-Gaussian, approximate-modulus-switching model.

`TFHE/CenteredBinomialGrowingNoiseEndToEnd.lean` removes the constant-width limitation of that
first feasibility witness. Set `w = λ + 1` and let `N` be the least power of two at least `8w`.
Thus `8w ≤ N < 16w`; the scalar dimension and ring degree are both `N`, `X^N + 1` is a
power-of-two cyclotomic polynomial, all ring/KSK/input centered-binomial widths are `w`, and
`q = 64N^6 = (2N)^6`. The polynomial identity `Φ_(2N)=X^N+1`, equality of the two defining
ideals, and the bijective multiplicative interpretation of the executable carrier in that
cyclotomic quotient are proved explicitly. Six base-`2N` levels reconstruct the modulus exactly,
while the factor-two rounding bound gives an explicit polynomial upper bound for `q`. The checked `inputMargin` and
`outputMargin` hold at every security parameter, so `refreshCorrect` proves probability-one fresh
Boolean refresh for the complete supported error distribution. The single theorem
`secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe` again pairs this
unconditional correctness result with native auxiliary-input CircLWE, an ordinary combined scalar
search-LWE batch, and the three post-cut LWE premises. Growing noise and cyclotomic degree make
the finite asymptotic witness materially stronger, but hardness of these particular LWE and CircLWE
families is still a computational premise rather than a parameter theorem.

For confidentiality alone, the shortest native statement is
`secureAgainst_of_nativeMonomialKDM_and_concreteBatchLWE`. It gives the checked pointwise bound

```text
Adv_TFHE <= Adv_native-degree-two-monomial-KDM + Adv_concrete-batch-LWE.
```

This exact monomial game is the intact circular key cycle after the proved native TGSW phase
normalization; it is not a Gaussian residual premise and no correctness result enters the chain.
The corresponding public-evaluation theorem preserves advantage exactly.

The literature-aligned real-versus-uniform theorem is
`secureAgainst_of_nativeCircularLWE_and_concreteBatchLWE`. It uses the direct BRK-first reduction
and states that native auxiliary-input CircLWE plus binary-secret LWE with modulus
`64N^6`, dimension `N`, `6N+Q` rows, and centered-binomial width `λ+1` implies adaptive TFHE
security. `concreteBatchLWESecurityGame_eq_batchLWE` proves that this explicitly named problem is
the exact generic reduction target, while `concreteBatchSampleCount_le_polynomial` gives the bound
`6N+Q ≤ 96(λ+1)+Q(λ)`. Its pointwise source is
`securityGame_advantage_le_nativeCircularLWE_add_three_concreteBatchLWE`:

```text
Adv_TFHE
  <= Adv_native-auxiliary-input-CircLWE
     + Adv_batch-LWE(actual zero branch)
     + Adv_batch-LWE(uniform-BRK zero branch)
     + Adv_batch-LWE(honest KSK-plus-query branch).
```

No correctness, finite-view, collision, sampler-replacement, or post-cut RLWE term occurs in this
direct route. The KSK-first cyclotomic theorem below is an independently checked alternative
decomposition of the same security boundary.

This confidentiality statement also covers public TFHE evaluation. The adaptive adversary sees
the entire circular cloud key and is an arbitrary probabilistic oracle computation, so it may run
blind rotation, sample extraction, key switching, or any larger public circuit on its challenge
ciphertexts. The formal public-evaluation compiler forwards each encryption query, applies an
arbitrary cloud-key-dependent evaluator, and preserves both the query bound and the advantage
exactly. The concrete evaluated-security theorem then invokes the same native auxiliary-input
CircLWE and explicit binary-secret LWE assumptions. Only computational-efficiency closure is new;
functional correctness is irrelevant to this indistinguishability argument and remains a separate
property.

The post-cut premise is now available directly as an exact cyclotomic quotient game, rather than
only as an algebraically identified executable carrier. The real and uniform RLWE transcript
distributions transport exactly between the coefficient-vector ring and
`(Z/qZ)[X]/(Φ_(2N))`, for the family's binary secret and width-`w` centered-binomial errors.
Consequently `postCutBinarySecretRLWE_advantage_eq_cyclotomic` has zero loss, and
`secureAgainst_of_nativeCircular_ordinarySearchLwe_cyclotomicRLWE` consumes negligible advantage
for precisely that quotient-ring game and concludes adaptive confidentiality alone. The combined
`secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe_cyclotomicRLWE` theorem is
the stronger convenience corollary that also returns the separately proved refresh property.
This strengthens the statement of the ordinary post-cut assumption; it does not discharge it or
the intact circular first hop.

The corresponding finite quantitative statement is
`securityGame_advantage_le_nativeCircular_add_ordinarySearchLwe_add_finiteLoss_add_two_cyclotomicRLWE_add_inputLWE`:

```text
Adv_TFHE
  <= viewCount * Adv_native-CircLWE
     + Pr[ordinary scalar search-LWE recovery]
     + finite-view amplification loss
     + Adv_cyclotomic-RLWE(real post-cut)
     + Adv_cyclotomic-RLWE(zero post-cut)
     + Adv_input-LWE.
```

This theorem uses no computational or negligibility hypothesis; the asymptotic endpoint is the
closure of this explicit reduction under the stated hardness premises and polynomial view growth.

`FormalProof4FHE.LWE.TwoBlockConvolution` supplies the checked bridge for a common explicit
relation between distinct samplers. If

```text
inputError =dist keySwitchError + independentWideningError
```

and the widening sampler is total, the reduction adds IID widening noise only to the challenge
block. The real branch follows from scalar-to-vector convolution, while the uniform branch is
preserved by a transcript permutation. Consequently
`abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_input_convolution` replaces the two-noise
term by ordinary binary-secret batch LWE on the same
`((ringRank * degree) * keySwitchLevels) + 1` rows, using the KSK error sampler. No equality of the
two protocol samplers is assumed.

## Checked native TRGSW normalization

`FormalProof4FHE.TFHE.BootstrappingSecurity` removes ciphertext layout as an unspecified part of
the remaining premise. For fixed secrets and message, translating the uniformly sampled TGSW mask
matrix by the mask part of `message * H` is a permutation. The checked theorem

```text
TGSW.encrypt_evalDist_eq_directEncrypt
```

therefore proves the exact distributional equality

```text
native TGSW: Z + message * H
  =dist
fresh direct module-LWE rows with messages gadgetPhase(secret, gadget, message).
```

There is no statistical distance and no row-hybrid factor. The row equations make the remaining
KDM functions explicit. For a bootstrapping-key entry encrypting scalar-key bit `μ` under ring key
`s`, gadget level `l` carries

```text
mask block j:  -(s_j * (μ * g_l))
final block:    μ * g_l.
```

Thus the final block is affine, while every mask block is bilinear across the scalar and ring key
families. `generateBootstrappingKey_evalDist_eq_direct` lifts the equality to the entire BRK, and
`continuationBootstrapReplacementAdvantage_eq_directBilinear` lifts it through the correlated real
KSK and every downstream continuation.

`TFHE.TGSW.CircularBoundary` makes the boundary a named checked decomposition:

```text
gadgetPhase = affinePhasePart + crossKeyPhasePart.
```

The final gadget block has zero cross-key part. A mask-coordinate block has zero affine part and
cross-key part exactly `-(ringKey_j * (scalarBit * gadget_l))`. The cross-key part is identically
zero when the encrypted scalar bit is replaced by zero. This connects the generic affine-clique
theorem to the native proof without overextending it: the affine theorem handles the logical key
cycle for direct common-space affine rows, while TFHE's intact heterogeneous ring/vector cycle
retains a genuine bilinear term. After the zero-message cut, that term disappears and the checked
ordinary ring-LWE reductions apply.

`DirectBilinearHardAgainst` is the resulting concrete hardness interface. The conditional
composition theorems

```text
oneTimeHardAgainst_of_directBilinear_and_jointLwe
oneTimeHardAgainst_of_directBilinear_and_batchLwe_same_noise
```

combine a bound for that exact KDM problem with the already-checked LWE reduction into an
end-to-end one-time TFHE security bound for any adversary class closed under the displayed
reductions.

## Checked security after cutting the key cycle

`FormalProof4FHE.TFHE.CutCycleSecurity` now proves that the structured BRK hop itself needs no
circular assumption once the opposite KSK edge has already been replaced by zero-message rows.
At that point the scalar key and its zero-message KSK can be sampled as a context independent of
the hidden ring key. For every scalar-key coordinate, the homogeneous TGSW rows form one ordinary
module-LWE batch under the shared binary ring key. The real BRK is obtained by adding the known
coordinate-dependent gadget matrix.

The development proves three exact distribution facts:

1. regrouping the native coordinatewise TGSW samplers into one parallel module-LWE transcript
   does not change either the real or zero-message BRK distribution;
2. the uniform branch of that parallel problem is uniform over the complete unzipped transcript;
   and
3. adding all scalar-key-dependent gadget matrices is a bijection of that finite transcript
   space, including under an independently sampled zero-KSK context and downstream continuation.

`FormalProof4FHE.LWE.ParallelBatch.advantage_eq_batch` then flattens the parallel transcript
through `finProdFinEquiv`. It proves exact equality with one conventional binary-secret ring
batch-LWE problem containing

```text
lweDimension * TGSW.rowCount ringRank tgswLevels
```

samples. This is a reshaping equality, not an additional hybrid or assumption.

For native ring rank one, the further normalization is now exact. The pushed-forward TFHE secret
sampler chooses every coefficient bit independently and embeds the resulting polynomial in
`RLWE.Rq`; `binarySecretRLWEProblem` uses that sampler in the finite rank-one RLWE interface.
`batchModuleLweProblem_one_distr_evalDist_eq_binarySecretRLWE` proves equality of the real
transcript laws, the uniform laws are equal exactly, and
`batchModuleLweProblem_one_advantage_eq_binarySecretRLWE` gives loss-zero advantage equality for
every public distinguisher. Thus the growing-noise rank-one family's two post-cut reductions are
attacks on one explicitly named binary-secret RLWE game. This statement does not equate the
binary-coefficient secret with the separate uniform-secret RLWE problem.

`TFHE/CoefficientStructuredLWE.lean` removes the remaining carrier-level ambiguity. It uses the
executable equivalence between `RLWE.Rq q N` and `Fin N → ZMod q`, proves that multiplication is
the schoolbook negacyclic convolution, and expands the module product as the sum of those
convolutions against independent Boolean secret polynomials. The transported challenge and ideal
output are exactly uniform coefficient matrices. Mapping an IID ring-error vector is exactly IID
sampling from the coefficient image, and for the centered-binomial sampler this image is the
direct independent signed-weight coefficient sampler. Both transcript directions are executable
equivalences, so real games, uniform games, and every advantage agree without loss.

For the growing family, `postCutCoefficientStructuredLWESecurityGame` fixes all parameters:
`N` is the least power of two at least `8(λ+1)`, `q = (2N)^6`, rank one, the native BRK row
count, uniform Boolean coefficient secret, and centered-binomial width `λ+1`. The theorem
`secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe_coefficientStructuredLWE`
accepts security of precisely that coefficient game and transfers it to both post-cut reductions.
The checked cardinality and point-probability lemmas show that a rank-`r`, degree-`N` Boolean
secret space has size `2^(rN)` and each secret has probability `2^(-rN)`; in this family that is
exactly `N` bits of rank-one secret min-entropy. This normalization does not invoke a literature
hardness theorem. The executable ring is now also connected to the exact power-of-two cyclotomic
quotient at the level of both complete RLWE games: source secret/error laws are pushed forward and
real/uniform transcript distributions and distinguishing advantages agree exactly. No
coefficient-to-canonical-embedding error theorem is inferred from that equivalence. In particular,
the supplied binary-secret Module-LWE reduction increases the
module rank; its own discussion leaves the rank-one binary-secret Ring-LWE case open. The
Brakerski--Döttling entropic Ring-LWE theorem does cover power-of-two cyclotomics, but its concrete
conclusion uses Gaussian target error and DSPR/noise-lossiness hypotheses, and the paper explicitly
notes that its entropy bounds are still insufficient for binary coefficient secrets without much
stronger assumptions. Neither theorem therefore discharges this centered-binomial rank-one game.

Consequently

```text
cutBootstrapReplacementAdvantage_le_two_parallelModuleLwe
cutBootstrapReplacementAdvantage_le_two_batchModuleLwe
```

checks

```text
Adv[(real BRK, zero KSK) versus (zero BRK, zero KSK)]
  ≤ Adv_parallel-module-LWE(real-message reduction)
    + Adv_parallel-module-LWE(zero-message reduction).

  = Adv_batch-module-LWE(flattened real reduction)
    + Adv_batch-module-LWE(flattened zero reduction).
```

`oneTimeCutBootstrapReplacementAdvantage_le_two_batchModuleLwe` specializes the conventional-batch
result to the adaptive one-time TFHE experiment, including the fresh TLWE challenge chosen after
the cloud key is visible. No KDM or circular-security premise occurs in this post-cut theorem.

`TFHE/AdaptiveCutCycleSecurity.lean` now carries the same cut through the complete query-bounded
sequential oracle continuation. Later message pairs may depend on every earlier ciphertext, but
the evaluation key is still replaced once for the entire interaction. Its endpoint theorem is

```text
abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_jointLwe
```

in `Encryption.Adaptive.CutCycleSecurity`: one native intact-cycle term, two ordinary ring
batch-LWE terms, and one joint-LWE term containing all KSK rows and exactly `queryCount` adaptive
input rows. With equal scalar noises, the last term flattens exactly to ordinary binary-secret
batch LWE on `keySwitchSamples + queryCount` rows.

The concrete cut games are also proved distributionally equal to `G1'` and `G2` for every
ring-secret-independent continuation, which includes the native one-time experiment. This yields

```text
abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_jointLwe
```

and hence the alternative-order end-to-end bound

```text
|Adv_TFHE-one-time|
  ≤ Adv_KS-first-intact
    + two conventional binary-secret ring batch-LWE advantages
    + one zero-cloud joint binary-LWE advantage.
```

Finally,

```text
keySwitchFirstReplacementAdvantage_le_directBilinear_add_postCutLwe
directBilinearAdvantage_le_keySwitchFirst_add_postCutLwe
```

show in both directions that the KSK-first intact term and the previously exposed direct-bilinear
BRK-first term differ by at most the checked post-cut ring batch-LWE and joint-LWE terms.

`Encryption.Adaptive.CutCycleSecurity` now proves the same comparison for the complete sequential
oracle continuation. It packages the opposite post-cut KSK edge as
`keySwitchReplacementAdvantage_le_two_jointLwe`, then derives both adaptive converse bounds using
two conventional ring batches and the native-message/zero-message joint-LWE reductions. No
query-bound hypothesis is needed for this distributional comparison.

At the family level, `Asymptotic.CutCycleSecurity.adaptiveFirstHop_secureAgainst_iff` proves that,
once those four post-cut reductions have negligible advantage and preserve the chosen efficiency
classes, BRK-first direct-bilinear security is equivalent to KSK-first intact-cycle security for
polynomial-query adaptive TFHE adversaries.

Together with the existing theorem for replacing the KSK after the BRK has been zeroed, this shows
that both *second* edges of the two possible hybrid orders are ordinary LWE/module-LWE
obligations. The remaining issue is precisely the *first* replacement while both directions of
the native key cycle are still present. This distinction prevents the ciphertext layout or the
already-cut hybrids from being mistaken for the circular-security obstacle.

### Exact degree-two monomial classification

`TFHE/MonomialKDM.lean` connects that remaining term to the nonlinear-KDM literature without
changing the native distribution. For every nonzero gadget value,
`TGSW.MonomialKDM.scaledProduct_not_affine` proves that

```text
(ringCoordinate, scalarCoordinate)
  ↦ -(ringCoordinate * (scalarCoordinate * gadgetValue))
```

cannot equal any affine expression in the two native coordinates. This is a checked obstruction
to applying the affine ACPS-style theorem directly, rather than only a syntactic observation.
For the concrete growing centered-binomial family, `firstTGSWGadget_ne_zero` proves that the first
base-`2N` gadget coordinate is nonzero at every security parameter, and
`nativeMaskBlockPhase_not_affine` specializes the obstruction to those exact TFHE parameters.
Thus the nonlinear circular boundary is not vacuous in the family used by the security endpoint.
The stronger `not_binaryVectorScaledProductAffine` theorem restricts both arguments to complete
binary key vectors and permits arbitrary affine coefficients on every bit. Its concrete
specialization `nativeBinaryKeyCoordinateProduct_not_affine` still rules out the selected native
cross coordinate. Therefore the obstruction applies on the actual Boolean support, not merely on
the ambient ring, and also excludes direct use of affine subspace-LWE/related-key theorems.
More precisely, `nativePolynomialMaskBlockPhase_not_affine_on_binaryKeys` quantifies over an
arbitrary complete binary polynomial for the rank-one ring key and an arbitrary complete binary
scalar key. Even an alleged affine expression using every coefficient and every scalar bit cannot
equal the selected mask-block function. This closes the possible loophole that ambient-ring
non-affinity might disappear after restricting to valid TFHE keys.
On the reference side,
`GeneralizedSubspaceLWE.Adaptive.noisyInnerProduct_eq_secretAffine` rewrites every fixed-randomness
Subspace-LWE oracle response as public affine coefficients times its single hidden secret plus a
public constant. Thus both sides of the mismatch are now checked algebraically: Pietrzak's oracle
remains affine in one secret, whereas the native TFHE mask block remains non-affine on its full
binary two-key support.

The same file defines the degree-two lift

```text
crossMonomial_j = ringCoordinate_j * scalarCoordinate
```

For one TGSW entry this is a restricted rank-one degree-two family, not an oracle for arbitrary
quadratic functions. For one mask-block row, write the fresh zero-encryption row as

```text
(a, b = <a, ringKey> + error).
```

TRGSW adds `scalarCoordinate * gadgetValue` only to mask coordinate `j`. The translated mask
`a' = a + scalarCoordinate * gadgetValue * e_j` is still uniform marginally, but its correlated
body satisfies

```text
b - <a', ringKey>
  = error - scalarCoordinate * gadgetValue * ringCoordinate_j.
```

Consequently the nonce observation narrows the required assumption to the public, gadget-scaled
outer-product coordinates; it does not make those coordinates affine. If the scalar coordinate
is itself a coefficient of the same binary key, diagonal products collapse by `s_i^2 = s_i`,
but every off-diagonal `s_i * s_j` remains genuinely quadratic. Native TRGSW contains all mask
blocks, not only the diagonal ones.

`TFHE/FullBRKQuadraticSpan.lean` checks the joint-table consequence that is easy to miss in the
single-row calculation. At a fixed gadget level,
`TGSW.MonomialKDM.FullTable.phase_maskRowCombination_eq` proves that an arbitrary public linear
combination of every message-by-mask row has phase

```text
-(sum_(i,j) weight_(i,j) * ringKey_j * message_i) * gadget_l
  + combinedRowError.
```

When `message_i = secret_i`, `phase_selfMaskRowCombination_eq` is the corresponding arbitrary
weighted quadratic form. The native ring specialization
`extractedOuterProduct_coefficient` proves that reading coefficient `k` from the table entry for
message coefficient `(u,v)` and mask polynomial `j` gives exactly
`s_(j,k) * s_(u,v)`. Therefore one ciphertext is rank one, whereas the complete self-BRK contains
and publicly linearly spans all pairwise Boolean monomials. The exact native assumption is still
narrower than a general adaptive degree-two KDM interface: its functions, gadget scales, row
positions, and noise correlations are fixed at key generation. But nonce placement by itself does
not remove the full table's quadratic span.

For binary secrets, that span has a sharper checked normal form.
`selfQuadraticForm_embedBinarySecret_eq_diagonal_add_offDiagonal` proves

```text
sum_(i,j) w_(i,j) s_i s_j
  = sum_i w_(i,i) s_i
    + sum_i sum_(j != i) w_(i,j) s_i s_j.
```

The first term is affine because `s_i^2 = s_i`; only the square-free off-diagonal products remain
nonlinear. `phase_selfMaskRowCombination_embedBinarySecret_eq` proves the same identity inside the
publicly obtainable BRK phase and preserves the complete combined error. The native diagonal
coefficient theorem specializes the ring table to the same Boolean idempotence. A one-coordinate
key therefore collapses algebraically to affine KDM, but it has only constant secret entropy and
does not yield a secure TFHE family. A practical polynomial ring key has many coefficient
coordinates, and the full BRK includes all of their off-diagonal products.

Here “affine” is coefficient-level algebra, not an automatic invocation of ordinary module-RLWE.
`TFHE/CoefficientAffineCircularRLWE.lean` makes this distinction checked rather than informal.
`coefficientTransfer` is the elementary linear operator that reads coefficient `i`, writes it at
coefficient `j`, and zeros the rest. `coefficientEquiv_diagonalCrossAtDegree_rankOne` proves that
the actual native diagonal cross coordinate is exactly `E_(i,i)` on the binary coefficient
vector. `rightNegacyclicMulLinear` proves directly from the negacyclic convolution formula that
multiplication by a fixed public gadget polynomial is coefficient linear. The two native product
theorems then identify a mask-diagonal term with `rightMul(g_l) ∘ E_(i,i)` and a body term with
`rightMul(g_l) ∘ E_(0,i)`. `coefficientAffineNoiseless` records the corresponding structured-LWE
class with an arbitrary fixed coefficient-linear message.

Ordinary rank-one RLWE challenge translation absorbs only maps of the form `S -> S * c` for one
fixed public ring element `c`. For every nontrivial coefficient ring and degree at least two,
`nativeFirstDiagonalCross_not_ringMultiplicationOnBinary` proves that even the first native
diagonal projector has no such representation, already on Boolean secrets: the coefficient-zero
basis forces `c = 1`, while the coefficient-one basis is killed by the projector but not by
multiplication with `1`. A complete security decomposition must therefore pair the off-diagonal
KDM argument with a coefficient-linear circular theorem whose binary-secret distribution and
circulant challenge law match native TFHE. The checked packed power-of-two theorem covers its
packed uniform-ring construction, not this native binary-ring law.

The module also instantiates the fixed-auxiliary-input circular interface with exactly this
diagonal-only BRK. The hidden secret is the master binary ring key, the real challenge is the
complete diagonal-only BRK, the zero challenge is the native zero BRK, and the unchanged real
suffix KSK is retained as correlated auxiliary input. `realGame_eq_diagonalOnlyGame` and
`zeroGame_eq_bootstrapZeroGame` are exact program equalities, while
`kdmAdvantage_eq_diagonalAdvantage` identifies this generic KDM term with the diagonal summand of
the one-cycle split. The resulting checked boundary is

```text
Adv_one-circular
  <= Adv_square-free-table
     + Adv_coefficient-affine-CircRLWE
     + Adv_zero-BRK-with-real-KSK-LWE.
```

This is a sharper theorem statement, not a proof that the new circular-RLWE term is negligible.

The native ring split is also checked entry by entry. `extractedDiagonalPart` retains the unique
coefficient where the encrypted key coordinate and the mask-key coordinate coincide, while
`extractedSquareFreePart` subtracts it from the actual ring-valued outer product.
`extractedSquareFreePart_diagonal_coefficient` proves that the remainder is zero at that location,
and `extractedSquareFreePart_coefficient_of_not_diagonal` proves that every other coefficient is
the original product of two distinct Boolean key coordinates. The generic phase theorem
`gadgetPhase_self_eq_diagonalAtDegree_add_squareFreeAtDegree` lifts this coefficient statement to
every row of the normalized native TGSW entry.

`TFHE/SharedRandomnessOneCycleSquareFreeSecurity.lean` lifts the same normal form through the
complete shared-randomness BRK and its retained real KSK. The honest cloud-key distribution is
exactly the sampler with its phase written as diagonal plus square-free contributions. For every
adversary, the checked triangle theorem is

```text
Adv_one-circular
  <= Adv_(real versus diagonal-only)
     + Adv_(diagonal-only versus zero).
```

The first summand is precisely the fixed square-free outer-product-table obligation. The second is
the coefficient-affine circular obligation. Thus a general degree-two KDM theorem is sufficient
but unnecessarily strong; a proof must cover the fixed off-diagonal table and the compatible
native affine endpoint. Neither summand is silently assumed to follow from ordinary RLWE.

The split is also checked in the stronger FHE context where the continuation receives the hidden
master key and may use it to generate all adaptive challenge ciphertexts. The honest native
continuation is distributionally identical to its explicit diagonal-plus-square-free sampler.
Using the uniform BRK as the common endpoint gives the sharper direct triangle

```text
Adv_native-CircRLWE
  <= Adv_square-free-table
     + Adv_coefficient-affine-CircRLWE.
```

Lifting this pointwise inequality to security-parameter families and composing it with the
existing adaptive encryption reduction proves

```text
Adv_TFHE
  <= Adv_square-free-table
     + Adv_coefficient-affine-CircRLWE
     + Adv_ordinary-batch-LWE.
```

Negligibility of those three exact games implies reusable-key adaptive encryption security and
security after arbitrary public deterministic FHE evaluation. This removes the opaque generic
circular-RLWE premise from the final theorem statement; it does not yet prove either native
circular component negligible.

There is now also a security-only way to discharge both native components at once. For a fixed
master secret, the exact TGSW gadget phase in every real BRK row can be regarded as an additive
translation of that row's fresh body error. Total-variation data processing gives

```text
Adv_(real self-BRK versus zero BRK)
  <= sum_(all BRK rows r) TV(E + phase_r, E).
```

The proof retains the real shared KSK and allows the continuation to use the same hidden master
key, so it applies directly to adaptive encryption and public FHE evaluation. For a certified
coefficientwise discrete Gaussian, every ring translation is bounded by `degree` times the scalar
translation cost at centered magnitude `q/2`. With polynomial BRK layout, negligible certificate
error, a Gaussian window contained in the integer standard deviation, and negligible
`(q/2)/(window+1)`, the complete one-circular KDM advantage is negligible. The resulting TFHE
theorem obtained by the direct real-to-zero composition assumes only the non-circular zero-BRK
auxiliary-input LWE endpoint and ordinary batch LWE; it has no circular/KDM hardness premise.

The stronger endpoint also eliminates that zero-BRK premise. The checked finite-group averaging
lemma states that any never-failing sampler whose distance from every additive translate is at
most `epsilon` has distance at most `epsilon` from exact uniform: averaging all translated laws
is exactly the uniform law. Applying it to the same coefficientwise Gaussian proves

```text
TV(ringGaussian, UniformRing)
  <= ringDegree * scalarLinearShiftBound(certificate, q/2).
```

Polynomial degree growth and the same window conditions make this one-draw gap negligible.
The existing uniform-BRK hybrid then proves both reusable adaptive TFHE confidentiality and
confidentiality after arbitrary public deterministic FHE evaluation from ordinary batch LWE
alone. Thus the strongest security-only theorem has neither a circular/KDM hardness premise nor
a zero-BRK auxiliary-input hardness premise.

The numerical hypotheses now have a concrete instantiation. Let `N` be the existing
power-of-two polynomial ring degree and choose

```text
q              = (2N)^(lambda+1),
alpha          = 2^lambda,
integer sigma  = q * 2^lambda,
window         = q * 2^lambda.
```

The finite Gaussian ticket table is obtained by rounding the exact modular Gaussian with
denominator `q * (q+1) * 2^lambda`. Its certified compilation error is at most `2^-lambda`, and
`(q/2)/(window+1)` is at most `2^-lambda`. The complete BRK layout has a checked polynomial
envelope, so these inverse-exponential terms remain negligible after charging all rows and
coefficients. The concrete conclusions are:

```text
real self-BRK versus zero BRK is negligible;
real BRK error versus uniform BRK error is negligible;
ordinary query-counted batch LWE implies reusable adaptive TFHE security;
the same implication holds after arbitrary public deterministic FHE evaluation.
```

No circular, quadratic-KDM, or zero-BRK auxiliary assumption appears in these conclusions. The
rounded ticket table is a noncomputable finite existence witness rather than a proved PPT table
compiler.

This is intentionally labeled security-only. A window large enough to absorb an arbitrary
centered residue can require noise incompatible with TFHE correctness. It proves the real
circular distribution secure under those parameters, but does not resolve circular security for
the narrow-noise, correctness-compatible parameter regime.

It then proves `gadgetPhase_eq_expandedGadgetPhase`: after adjoining those coordinates, the final
gadget block is the existing affine body term and every mask block is a public linear projection
of `crossMonomial`, scaled by the gadget. `generateBootstrappingKey_eq_direct` lifts the identity
through all native BRK entries. Consequently `advantage_eq_directBilinear` proves equality of the
complete real-KSK contextual games for every continuation.

`TFHE/AsymptoticMonomialKDM.lean` lifts the equality to security-parameter families.
`adaptiveSecurityGame_secureAgainst_iff_directBilinear` is an exact equivalence for
polynomial-query sequential TFHE adversaries, and
`adaptiveSecurityGame_secureAgainst_iff_keySwitchFirst` composes it with the four checked post-cut
LWE obligations to obtain the equivalent KSK-first presentation.

This is precisely the algebraic idea behind the Brakerski--Goldwasser--Kalai degree-two monomial
expansion, but not an application of that paper's security theorem. A theorem for every
degree-two KDM function would be sufficient, but is stronger than the exact TFHE obligation.
Their construction changes the secret-key geometry and encryption scheme so affine KDM security
applies in the expanded space. Native TFHE retains its original two heterogeneous decryption
keys, so hardness of this exact outer-product presentation remains the circular/KDM assumption
to establish or validate.

The additional GSW references sharpen this conclusion but do not remove the assumption. The
original GSW security proof replaces its public LWE matrix and then uses leftover hashing to hide
a message independent of the unknown secret; the paper explicitly states that bootstrapping to
pure FHE uses circular security. Gay--Pass prove shielded-randomness-leakage security of GSW from
LWE only in the non-circular experiment. Their encrypted-key construction explicitly assumes
2-circular SRL security between GSW and a linear scheme; it is not a reduction of that circular
property to LWE. Its randomness shielding and smudging ideas may help specify a future evaluator,
but they do not generate the unknown self-key message required in the LWE hybrid and therefore do
not discharge the native square-free table. Finally, the supplied GG-GSW manuscript states that
its Theorem 4.1 proof is incorrect and that its IND-CCA1 claims are unsupported; it cannot serve as
a security lemma here in its current form.

### Auxiliary-input CircLWE formulation

Micciancio--Vaikuntanathan's PKC 2024 CircLWE formulation compares a gadget-LWE encoding of a
fixed secret function with a uniform transcript. It also makes any retained secret-dependent side
information part of the problem statement. `LWE/AuxiliaryInput.lean` formalizes precisely this
three-endpoint interface:

```text
Real    = (secret, KDM challenge, fixed auxiliary input)
Zero    = (secret, zero-message challenge, fixed auxiliary input)
Uniform = (secret, uniform challenge, fixed auxiliary input).
```

The contextual secret is available only to the experiment/continuation so later ciphertexts can
be generated under the same key. Admissible continuation classes must still enforce that the
internal adversary is not handed that secret.

`TFHE/MonomialKDMAuxiliaryInput.lean` gives the exact native instantiation. Its secret is the pair
of TLWE and TRLWE keys, its real challenge is the checked degree-two monomial BRK sampler, its
uniform branch samples the identical native BRK type, and its fixed auxiliary input is the real
KSK. `realGame_eq_native` and `zeroGame_eq_native` are exact computation equalities. Therefore
`kdmAdvantage_eq_monomial` identifies its real-versus-zero game with the existing native
monomial-KDM advantage.

The two checked triangle bounds are

```text
Adv_native-monomial-KDM <= Adv_aux-CircLWE + Adv_zero-with-aux-LWE
Adv_aux-CircLWE          <= Adv_native-monomial-KDM + Adv_zero-with-aux-LWE.
```

`TFHE/AsymptoticAuxiliaryInputCircularLWE.lean` lifts both directions to arbitrary continuation
families and to polynomial-query adaptive TFHE adversaries. In particular,
`adaptiveSecurityGame_secureAgainst_iff_circularLWE` proves equivalence of the two named
assumptions whenever the zero-message side-information game is negligible. This is stronger than
renaming the old game: it fixes the uniform endpoint used by CircLWE and exposes the exact extra
obligation needed to move between the literature's real-versus-uniform formulation and TFHE's
real-versus-zero hybrid.

`TFHE/AuxiliaryInputZeroSecurity.lean` now discharges that extra obligation for the continuations
induced by query-bounded adaptive TFHE adversaries. First,
`generateZeroBootstrappingKey_uniformError_evalDist` proves that a zero-message native BRK whose
ring errors are uniform is itself exactly uniform: fixed phase translations and the native
transcript assembly are bijections. The adaptive zero-side comparison then factors through the
fair hidden-bit zero-cloud game with that uniform BRK context:

```text
Adv_zero-with-real-KSK
  <= Adv_joint-LWE(actual zero-BRK context)
     + Adv_joint-LWE(uniform BRK context).
```

The two terms share the complete real KSK rows and all adaptive challenge rows under one scalar
key. When KSK and input errors use the same sampler,
`adaptiveZeroLweAdvantage_le_two_batchLwe_of_same_noise` flattens each transcript exactly to an
ordinary binary-secret batch-LWE game. Its asymptotic lift,
`adaptiveZeroLWESecurityGame_secureAgainst_of_batchLWE`, proves the formerly explicit zero-side
security premise from those two reductions.

Consequently the executable centered-binomial family has the stronger theorem
`Family.secureAgainst_of_circularLWE_and_batchLWE`, and the shared Boolean family combines it with
probability-one refresh correctness in
`EndToEnd.secureAgainst_and_refreshCorrect_of_circularLWE`. Neither theorem needs a separate
zero-side assumption or a sampler-replacement term. The real-versus-uniform native
auxiliary-input CircLWE premise itself remains explicit: this result removes the retained-KSK
side obligation, but does not derive circular security from ordinary LWE or RLWE.

### Checked scalar-key randomization and search experiment

`TFHE/ScalarSecretRandomization.lean` formalizes the first native algebraic prerequisite for a
CircLWE search-to-decision route. For every fixed binary mask `r`, it transports the scalar key
`s` to the bitwise-masked key `s ⊕ r` simultaneously in both visible evaluation-key components:

- `transformBatch_batchEncrypt_evalDist` gives the exact signed-mask and affine-body
  transformation for the KSK target key. It preserves the error samples verbatim.
- `toggleTGSW_addGadget` changes a TGSW encryption of bit `sᵢ` into one of `sᵢ ⊕ rᵢ`.
  Negating homogeneous rows preserves their law whenever the ring error is negation-symmetric.
- `toggleTGSW_centeredBinomial_encrypt_evalDist` discharges that premise exactly for executable
  centered-binomial ring noise; there is no statistical or smudging loss.
- `transformBootstrappingKey_generate_centeredBinomial_evalDist` lifts the coordinate identity to
  the complete native BRK, while `transformKeySwitchKey_generate_evalDist` covers the complete
  KSK.
- `transform_realEvaluationKeyPair_centeredBinomial_evalDist` proves the joint real BRK+KSK view
  invariant under the same mask, and
  `transform_uniformBootstrapEvaluationKeyPair_evalDist` proves the corresponding
  uniform-BRK+real-KSK endpoint identity. `transformEvaluationKeyPair_bijective` also records that
  the public view transformation is a permutation.
- `maskedSecret_uniform_evalDist` proves that a uniform `r` makes `s ⊕ r` exactly uniform.
  `sampleMaskedRealScalarView_evalDist` and `sampleMaskedUniformScalarView_evalDist` lift the
  fixed-mask identities to exact couplings with a freshly sampled uniform scalar key and its real
  or uniform-endpoint evaluation-key view, while holding the ring key fixed.

`LWE/AuxiliaryInputSearch.lean` defines the matching generic search experiment: the solver sees
only the challenge and correlated auxiliary input, returns a candidate secret, and the experiment
checks exact recovery. `TFHE/AuxiliaryInputCircularSearch.lean` instantiates it with the paired
native scalar/ring secret, monomial BRK challenge, and real KSK. The theorem
`game_eq_nativeRealContinuationGame` proves that this is exactly the already classified native
real game. `fixedSecretRealView_evalDist_eq_native` connects its public view to the structured
BRK+KSK sampler, and `sampleMasked_fixedSecretRealView_centeredBinomial_evalDist` transports the
fresh-scalar-key coupling directly to that search view.

`LWE/AuxiliaryInputSearchToDecision.lean` now gives those remaining paper steps a quantitative
interface. `ViewRandomization` separately records the narrow search view, the widened decision
view, secret action, probabilistic shifted evaluator/smudger, exact fresh-secret law, and its
pointwise TV error. `randomizedView_tvDist_freshWideView_le` proves that this error is paid only
once after sampling the mask. A `Reduction` then records the actual public-distinguisher-to-search-
solver construction and its guess-and-check loss;
`publicHardAgainst_of_reduction` transfers search hardness with the two bounds added once.

`TFHE/AuxiliaryInputSearchToDecision.lean` constructs the native scalar `ViewRandomization` with
error exactly zero under centered-binomial noise and proves
`scalarViewRandomization_tvDist_eq_zero`. `TFHE/KeySwitchRecovery.lean` then proves a different and
stronger way to handle the heterogeneous secret: once the scalar key is known, a selected KSK
gadget level recovers all extracted ring-key bits for every centered-binomial KSK in support under
the explicit margin `2η < dist(0,gℓ)`. `keyExtractEquiv` reconstructs the native polynomial key.
`TFHE/AuxiliaryInputPairedRecovery.lean` lifts this pointwise fact through an arbitrary
BRK/KSK-dependent scalar solver and proves that completing its candidate preserves search success
exactly. Finally, `ScalarSecretReduction.toPairedSecretReduction` constructs the required full
`PairedSecretReduction` from a scalar-only certificate with no extra loss.
`TFHE/ScalarCoordinateRecovery.lean` further decomposes that scalar certificate. It runs one
randomized test per scalar coordinate, proves that each standalone coordinate game is exactly the
corresponding marginal of the assembled candidate, and applies a finite union bound to obtain
whole-key success at least `1 - ∑ᵢ εᵢ`. This argument permits arbitrary dependence of every test
on the common BRK+KSK view. `CoordinateSecretReduction.toScalarSecretReduction` packages the
result. `Probability/BinaryGuessCheck.lean` supplies the executable one-bit tester: it samples a
candidate, applies a public Boolean check, and keeps or flips that candidate according to the
signed distinguisher orientation. Its success and failure probabilities are proved exactly.
`CandidateViewTransformer` states the remaining native distributional law without hiding it: the
correct candidate must yield a fresh real BRK+KSK view and the wrong candidate must yield the
uniform-BRK+real-KSK endpoint. `toCheck_viewLaw` postcomposes such a transformer with any public
distinguisher, and `coordinateGame_candidateViewTransformer_failureProbability` proves exact
one-shot error `(1 - decisionAdvantage) / 2`. At the public interface this is exactly
`(1 - publicAdvantage) / 2`.

`TFHE/ScalarMaskCandidateView.lean` now tests the checked scalar rerandomizer against this exact
candidate-view boundary. `transform_realPublicView_centeredBinomial_evalDist` first averages the
fixed-secret transport over the native uniform scalar and ring keys and proves exact invariance of
the complete real BRK+KSK endpoint. `coordinateSource_randomizeContext_centeredBinomial_evalDist`
then proves the same law after sampling the hidden coordinate bit together with its correlated
public context. The result is packaged by `toAveraged` with

```text
correctError = 0
wrongError   = TV(realPublicView, uniformPublicView).
```

This is intentionally an audit, not a search-to-decision claim. The scalar transport does not
inspect the proposed coordinate bit. Therefore
`candidateCheckGap_toCandidateCheck_eq_zero` proves, for every orientation and every public
distinguisher, that its correct and wrong candidate-check experiments coincide and the signed gap
is exactly zero. Secret rerandomization supplies the `s ↦ s ⊕ r` part of the paper construction,
but a candidate-dependent homomorphic evaluation/rank-freshness argument is still required to
make the wrong-candidate BRK uniform.

There is now also a fully checked candidate-dependent route in the opposite, KSK-first ordering.
`TFHE/KeySwitchCandidateRandomization.lean` adds a fresh vector `u` to one selected scalar row of
the complete KSK challenge and adds `candidate · u` to the KSK bodies. Its two exact laws are

```text
candidate = sᵢ   ⇒ transformed KSK ≡ real KSK
candidate ≠ sᵢ   ⇒ transformed KSK ≡ uniform KSK.
```

The second law is proved by an explicit permutation, not a rank assumption: for binary bits,
`candidate - sᵢ` is `+1` or `-1`, so the shift is recoverable over every finite commutative ring.
The message and error vectors are arbitrary in the core bijection. The lifted native theorem only
requires that the executable KSK error sampler never fails; centered-binomial and certified
finite discrete-Gaussian samplers meet that operational condition.

`TFHE/KeySwitchFirstCandidateView.lean` retains the real BRK and lifts those laws through the
actual correlated source experiment. It proves exact real-BRK/real-KSK and
real-BRK/uniform-KSK candidate endpoints, then shows

```text
candidateCheckGap = keySwitchDecisionAdvantage.
```

The existing coordinate union bound gives scalar recovery at least
`1 - ∑ᵢ ofReal((1 - advantage)/2)`. Under the checked centered-binomial KSK decoding margin, the
same bound recovers the complete scalar/ring secret pair with no additional loss. This closes the
KSK-first coordinate algebra and recovery composition.

`TFHE/KeySwitchFirstSearchToDecision.lean` now packages that result into the generic quantitative
interface. Its auxiliary-input problem treats the KSK as the challenge and retains the real BRK
as correlated side information. Exact bind-swap theorems identify its real and uniform public
games with the native real-KSK and uniform-KSK endpoints, and identify its exact-recovery game
with the existing native paired-search experiment. The resulting checked reduction satisfies

```text
keySwitchDecisionAdvantage ≤ pairedSearchSuccess.toReal + oneShotLoss,
oneShotLoss = max 0 (keySwitchDecisionAdvantage - oneShotLowerBound.toReal).
```

Therefore native paired-search hardness and an explicit bound on `oneShotLoss` imply KSK-first
public-decision hardness. The theorem does not claim that this one-shot loss is negligible for
production key dimensions. It also does not prove that the paired native circular-search problem
is hard, nor replace the real BRK by a uniform or zero-message BRK. Consequently it is not an
ordinary-LWE/RLWE proof of native TFHE circular security.

`TFHE/KeySwitchFirstFreshView.lean` formalizes a stronger amplification model without weakening
that caveat. A solver receives an opaque query handle that samples independent native BRK+KSK
views under one fixed hidden key pair. Every majority-tree leaf queries a fresh view. The generic
whole-vector theorem pays the shared bad hidden-key fiber only once:

```text
pairedFailure ≤
  ∑ᵢ amplifiedError(roundsᵢ, threshold)
  + ofReal((1 - keySwitchDecisionAdvantage) / 2) / threshold.
```

The native fixed-secret candidate laws prove that every scalar coordinate has the same
conditional base error, which justifies the shared fiber term. The centered-binomial decoder then
recovers the ring key with no additional probability loss. A checked theorem transfers
fresh-view paired-search hardness to KSK-first decision hardness with the exact
schedule-dependent deficit. This is stronger than the single-view premise and is intentionally
not advertised as ordinary LWE/RLWE hardness.

`TFHE/KeySwitchFirstFiniteView.lean` makes the concrete view requirement finite. For a common
majority depth `r`, the challenge contains exactly

```text
lweDimension * 3^r + 1
```

independent native BRK+KSK views under the same hidden key pair. Each scalar coordinate receives
one explicit ternary tree with `3^r` leaves, and the last view is reserved for centered-binomial
ring-key completion. A generic deferred-sampling theorem proves that filling this tape before the
solver runs gives exactly the same output distribution as the fresh-query reduction. The
finite-batch hardness-transfer theorem therefore has no unbounded oracle premise. What remains is
cryptographic rather than operational: establish hardness of this bounded multi-view native
circular-search distribution from a conventional assumption, or retain it as an explicit
multi-view circular-search premise. No ordinary-LWE/RLWE or single-evaluation-key equivalence is
claimed.

The finite KSK-first premise now composes through the rest of the cloud-key circular game. The
checked four-game path is

```text
real BRK + real KSK
  → real BRK + uniform KSK
  → zero BRK + uniform KSK
  → zero BRK + zero KSK.
```

A zero-message KSK generated with uniform scalar errors is exactly uniform on its complete native
carrier. This identifies the middle endpoints with the existing cut-cycle reduction. Consequently
the first hop is the finite-batch paired-search term, the BRK hop is bounded by two ordinary
binary-secret ring batch-LWE advantages, and the final KSK hop is one ordinary binary-secret
scalar batch-LWE advantage. Thus bounded multi-view search hardness, its explicit amplification
loss, and ordinary post-cut LWE hardness imply native cloud-key circular security.

The bounded adaptive extension now incorporates the missing secret-dependent transcript
explicitly. Each augmented view consists of a real BRK, a real KSK, and an independently sampled
zero-message input tape under the same fixed scalar key. Candidate randomization carries the tape
unchanged. Conditional on the fixed key pair, the correct candidate preserves the whole view and
the wrong candidate makes only the KSK uniform, so the same common-fiber majority argument applies.
For common depth `r`, scalar-key recovery receives exactly

```text
lweDimension * 3^r
```

augmented views; no completion view is needed because this reduction recovers only the scalar key.
The resulting adaptive path is

```text
real BRK + real KSK + real input tape
  → real BRK + uniform KSK + real input tape
  → zero BRK + uniform KSK + real input tape.
```

At the final endpoint the BRK and KSK are independent of the scalar key, leaving only the bounded
input tape. It is exactly the real branch of ordinary binary-secret batch LWE on `queryCount`
rows, while bounded adaptive uniform-tape independence proves its uniform branch has success
probability one half. Consequently `hardAgainst_of_finiteSearch_and_lwe` derives full bounded
adaptive TFHE security from finite augmented scalar-search hardness, its explicit amplification
loss, two ordinary ring batch-module-LWE assumptions, and one ordinary scalar batch-LWE
assumption. The augmented search premise remains explicitly circular and is not identified with
ordinary LWE/RLWE or single-evaluation-key search.

The same route is now lifted to security-parameter families. A polynomial-view schedule records
the majority depth, a reference scalar coordinate, and a polynomial upper bound on the exact
`lweDimension * 3^rounds` augmented views. The pointwise family bound contains finite-search
success, the explicit majority recurrence, the two ordinary ring batch-module-LWE terms after the
uniform-KSK cut, and ordinary scalar batch-LWE on exactly the adaptive input rows. Choosing the
balanced threshold `(2 - decisionAdvantage)/4` gives the checked inequality
`decisionAdvantage ≤ 2 * searchSuccess + 2 * summedMajorityError`; hence the stronger asymptotic
theorem has no opaque amplification-deficit premise.

The finite fixed-schedule interface uses the capped residual
`min(summedMajorityError, decisionAdvantage / 2)`. The same two-for-one inequality holds, and this
residual is exactly zero whenever the decision advantage is zero. This avoids imposing raw
majority-error negligibility on zero-advantage adversaries: at threshold one half, that raw error
stays one half regardless of the majority depth.

The universal-schedule theorem now discharges this residual analytically. A quantitative proof of
the majority-of-three recurrence first uses logarithmically many warm-up rounds to amplify any
inverse-polynomial decision bias to a constant, then logarithmically many cooling rounds to drive
the error down. The resulting `3^rounds` leaf count is proved polynomial. For each exponent in the
definition of negligibility, the proof selects a corresponding polynomial-view schedule, absorbs
the polynomial scalar dimension, and bounds the scaled capped residual by a constant times
`(securityParameter + 1)⁻²`. This is the standard quantifier order: no single fixed schedule is
claimed to handle every exponent.

There is also a stronger sufficient coordinate-error theorem. The summed majority error is
exactly `lweDimension` times the common coordinate recurrence. Because every coordinate consumes
at least one view, the polynomial view-count certificate also bounds `lweDimension`, so
polynomial-loss closure absorbs the full sum if the coordinate recurrence is negligible. That
raw-error premise is not claimed to hold for every efficient adversary family; the capped
residual is the preferred asymptotic interface.

The executable centered-binomial family instantiates this theorem directly. Its scalar sampler is
proved total, so the finite-view sampler premise disappears, and its existing scalar-dimension
growth supplies the polynomial bound used by the canonical schedules. Universal augmented native
search hardness and ordinary post-cut LWE hardness now suffice; there is no separate
residual-negligibility premise. Centered-binomial noise does not by itself remove circularity:
hardness of that augmented same-secret search distribution remains the sole nonstandard
cryptographic premise in this route.

The augmented-search premise now has a decision-style normalization. The complete finite batch is
viewed as one auxiliary-input circular challenge: the real branch contains all same-secret
BRK+KSK+input-tape views, while the comparison branch is sampled independently of the scalar key.
For any public scalar-key solver, generic game hopping gives

```text
real recovery ≤ full-transcript circular advantage + independent recovery.
```

The independent recovery probability is proved exactly equal to `2^(-lweDimension)`. When
`lweDimension ≥ securityParameter`, that function is negligible. Consequently the universal
logarithmic-schedule theorem yields adaptive TFHE security from universal polynomial-view
full-transcript circular decision security and the ordinary post-cut LWE assumptions. The
centered-binomial specialization discharges sampler totality and dimension growth, and the
exact-rotation family has `lweDimension = securityParameter + 1`.

The stronger full-transcript decision result remains available, but its components are now also
separated exactly. `AdaptiveKeySwitchFirstFiniteViewCircularDecomposition.lean` inserts the
intermediate with uniform independent BRKs and real KSK/input-tape side information. For every
solver,

```text
real augmented recovery
  ≤ same-secret multi-view BRK circular advantage
    + uniform-BRK side recovery.
```

The second term is not mislabeled as decisional LWE: the continuation must still compare the
solver's answer with the sampled hidden scalar key. Instead,
`AdaptiveKeySwitchFirstFiniteViewSideLWE.lean` proves an exact search-LWE compilation. A checked
equivalence flattens the `lweDimension` majority trees to exactly
`lweDimension * 3^rounds` independent views. For each fixed hidden key pair, native KSK generation
and zero-message input encryption are exactly a two-block scalar-LWE sample followed by the public
KSK-message translation. Deferred sampling then preserves the complete joint experiment and the
original scalar key used by the final recovery check.

`AdaptiveKeySwitchFirstFiniteViewSideLWEFlatten.lean` concatenates all per-view rows. The first
conventional matrix has

```text
views * ((ringRank * degree) * keySwitchLevels)
```

columns, and the second has `views * queryCount` columns. Both use one binary scalar secret and
may use different executable error samplers. `LWE.SearchEquiv` proves this public reshaping
directly for search experiments, rather than inferring it from decision-game equality. If the KSK
and input samplers coincide, `LWE.TwoBlockSearch` concatenates the two blocks once more into one
ordinary batch with no loss.

The asymptotic theorem
`secureAgainst_of_universal_bootstrapCircular_flatSearchLwe_and_lwe` therefore derives adaptive
TFHE security from universal polynomial-view BRK-only circular security, conventional scalar
search LWE for the flattened rows, and the three existing post-cut LWE games. Centered-binomial
and exact-rotation wrappers are checked. In the equal-noise case,
`searchSecurityGame_secureAgainst_of_bootstrapCircular_and_ordinarySearchLwe` lifts the exact
finite concatenation to each polynomial schedule. Composing it with the native CircLWE hybrid
gives `secureAgainst_of_universal_nativeCircular_ordinarySearchLwe_and_lwe`; the exact-rotation
wrapper discharges sampler equality definitionally. Its scalar-side hypothesis is one ordinary
combined-batch search-LWE game, not the heterogeneous two-block fallback.

The contextual batch premise is now discharged by the generic randomized hybrid in
`LWE/AuxiliaryInputBatch.lean`. For a batch of `m` views, the reduction chooses one coordinate
uniformly, embeds the supplied native CircLWE challenge there, samples uniform challenges before
it and real same-secret challenges after it, and samples a fresh correlated auxiliary input at
every coordinate. The signed adjacent gaps telescope, giving the exact identity

```text
same-secret batch advantage = m * one-challenge auxiliary-input CircLWE advantage.
```

`AdaptiveKeySwitchFirstFiniteViewNativeCircular.lean` instantiates this with the native monomial
BRK challenge and the `(KSK, input tape)` auxiliary record. The monomial/direct/native BRK sampler
equalities and the majority-tree equivalence prove that `m` is exactly
`lweDimension * 3^rounds`, with no hidden resampling or independence change. The existing
polynomial-view schedule bounds this factor, so polynomial-times-negligible closure yields
`secureAgainst_of_universal_nativeCircular_flatSearchLwe_and_lwe`. Centered-binomial and exact
rotation wrappers consume the earlier one-challenge native auxiliary-input CircLWE game directly.
The equal-noise ordinary-search variant additionally removes the two-block interface from the
exact-rotation theorem statement without adding any statistical approximation.

The remaining circular obligation is therefore the native one-challenge CircLWE assumption
itself, not an extra multi-view strengthening. In accordance with `circular.md` and the supplied
SoK, no reduction of that intact native distribution from ordinary LWE/RLWE is asserted.

`CandidateViewTransformerReduction.toScalarSecretReduction` connects this one-shot contract
through the candidate tester and finite union bound, conditional on an explicit global inequality;
it does not itself amplify. `Probability/MajorityAmplification.lean` now provides an executable
majority-of-three tree, proves the exact update `e ↦ e²(1 + 2(1 - e))`, and iterates that recurrence.
Its recovery theorem samples the original BRK+KSK context exactly once and repeats only the public
candidate guess. Soundness therefore assumes a base-error bound for every supported hidden-bit and
context pair. `PointwiseGapAmplificationReduction.toScalarSecretReduction` packages precisely this
support-wise condition, the checked amplifier, and the whole-key union bound.

`TFHE/PointwiseCandidateView.lean` records the required stronger conditional law explicitly.
`TFHE/WidenedAuxiliaryInputSearchToDecision.lean` then completes the cross-distribution accounting:
the recovery source uses narrow centered-binomial ring and KSK errors, the decision target may use
arbitrary wider executable samplers, and the effective coordinate gap is

```text
targetDecisionAdvantage - correctSmudgingError - wrongSmudgingError.
```

The checked majority tree, coordinate union bound, centered-binomial KSK completion, and final
search-hardness transfer charge exactly the amplified coordinate errors; they no longer require
the narrow and wide samplers to coincide.

`TFHE/ConditionalSmudging.lean` proves the statistical implication for generic native TLWE/TGSW
rows. Once a source context and its evaluator residuals are fixed, adding independent wide body
errors costs at most the sum of the per-row translation distances. The proof is pointwise in those
residuals and accepts any executable finite sampler. `TFHE/NativeConditionalSmudging.lean` lifts
this to the complete BRK+KSK layout:

```text
correct residual pair  ~  fresh widened monomial BRK + real KSK
wrong residual pair    ~  uniform BRK + widened real KSK.
```

The correct bound sums all BRK and KSK translation costs. In the wrong normal form the BRK is
already exactly uniform, so only the KSK residual cost remains.
`TFHE/NativeResidualCandidateView.lean` packages the pointwise route as
`ResidualCandidateViewTransformer.toPointwise`: exact residual normal forms plus row-cost bounds
automatically discharge the support-wise conditional-TV fields consumed by amplification. It now
also provides a separate `AveragedResidualCandidateViewTransformer`. Its correct and wrong
normal-form equations are required only after sampling the original hidden bit and public context;
the residual-cost bounds remain support-wise only for the fresh target secrets sampled inside the
normal forms. `AveragedResidualCandidateViewTransformer.toAveraged` discharges the weaker averaged
contract directly, and `AveragedResidualCandidateViewTransformerReduction.publicHardAgainst_of_search`
carries it through thresholded amplification, whole-key recovery, and KSK completion.

`TFHE/InternalProduct.lean` now supplies the missing generic homomorphic algebra underneath a
candidate evaluator. It defines the native rowwise TGSW internal product and proves that a row
encodes the product message plus exactly three residuals: the control message times the data-row
error, the control message times the gadget-decomposition residual phase, and the external
product's weighted control-row error. Its native CMux theorem encodes

```text
falseMessage + controlMessage * (trueMessage - falseMessage)
```

and adds only the false-branch row error to that internal-product residual. Thus Boolean controls
select the declared branch at the phase level. Exact decomposition now also reconstructs the
complete TLWE input under a pure message-one gadget, yielding complete-ciphertext CMux laws:
message zero is the false branch plus the homogeneous-control internal product, and message one
is the true branch plus the same kind of explicit perturbation. These are deterministic
correctness identities; they do not imply that the perturbation's output masks are fresh,
independent, or uniform.

`TFHE/NativeShiftedCandidateEvaluator.lean` now instantiates that algebra with the executable
coefficientwise base digitizer. It toggles a selected structured TGSW control by the candidate,
uses that control in a native CMux for every BRK coordinate, and proves exact correct- and
complementary-candidate row normal forms. The correct candidate yields the zero CMux message; the
complementary candidate yields one. More strongly, every arbitrary public source BRK is proved
equal to its declared binary gadget message plus a canonical homogeneous remainder. Consequently
the correct-candidate theorem applies to the actual public ciphertext and exposes the concrete
digitized-CMux residual without assuming a syntactic key-generation witness. An explicit
coherence proof identifies the zero, one, and subtraction operations from the proof-facing `Rq`
ring dictionary with the executable coefficient-vector operations. The native evaluator then
exports whole-BRK complete-ciphertext identities: the correct output entry is the transported
source entry plus a named homogeneous internal product, while the wrong output entry is the fresh
true-branch entry plus its named homogeneous internal product.
`TFHE/NativeAdaptiveShiftedCandidateEvaluator.lean` then
samples a uniform scalar XOR mask and an independent uniform true-branch BRK, transports the BRK,
KSK, input tape, and candidate coherently, and exposes the resulting complete public transform.
The concrete true-branch map is named explicitly. Fixed-context bijectivity proves exact uniform
output, and that conditional law is lifted over the complete augmented source. The resulting
uniformized experiment is proved exactly equal to the existing public uniform view, including the
freshly masked KSK and adaptive tape. On the correct side, overwriting the selected mask
coordinate with the unique bit that transports a source candidate to a fresh target bit is proved
to be an exact reparameterization of an ordinary uniform mask. The equality remains exact after
sampling the independent uniform true-branch BRK. This supplies a total construction-specific
residual sampler and a rowwise phase theorem for every conditioned coin, at zero conditioning
loss. The same complete-ciphertext correct and wrong endpoint identities are exposed directly at
this fixed-coin adaptive transform boundary.

Universal bijectivity over every public context is too strong for the intended final theorem: it
also quantifies over degenerate controls, while the native digitized CMux can lose rank. The
`DirectStatisticalCertificate` therefore uses the actual TV distance between the mask-averaged
branch experiment and its uniform-BRK comparison. Its lifting theorem permits bad masks or
contexts and installs this explicit freshness cost directly as the wrong-candidate error in the
existing averaged recovery interface. It states the correct-candidate obligation as the direct
averaged distance of the same executable transform to the real public view; this avoids assuming
that a randomized evaluator has a fixed deterministic residual representation. The
`SampledResidualCertificate` gives the coin-aware smudging specialization: a residual sampler may
depend on the fresh secret pair, must have zero failure, and every residual in its support must
satisfy the explicit translation-cost bound. The deterministic `StatisticalCertificate` is
proved to embed into it by a probability-one sampler. The exact two-normal-form `Certificate`
remains available as a still stronger special case. `ConcreteStatisticalCertificate` fixes the
residual sampler to the actual computed CMux residual and splits the final evaluator loss into
three explicit terms: output-mask/error-law normal-form freshness, support-wise smudging, and the
mask-averaged wrong-branch distance. All interfaces fix the executable transform rather than
accepting an abstract one. The remaining normal-form task is therefore quantitative: prove the
freshness and smallness laws for the explicit homogeneous internal-product perturbation, rather
than establish another ciphertext-algebra identity.

`TFHE/NativeShiftedResidualBounds.lean` now closes the deterministic part of the smudging term.
The complete correct residual is exactly one source-row error plus the external-product error of
the zero-message toggled control. Toggling changes an arbitrary TGSW row error only by sign, and
the centered coefficient infinity norm is sign-invariant. Exact base digits and the checked
negacyclic convolution estimate therefore yield an explicit residual budget. There are two
specializations: an `eta` budget when source and target keys are coupled, and a universal modular
budget using `q / 2` when the sampled-residual interface quantifies over an independent fresh
scalar/ring key pair.

`TFHE/NativeShiftedDiscreteGaussianBounds.lean` lifts those row budgets coefficientwise to the
proof-carrying finite modular discrete-Gaussian sampler. The original finite
`scalarShiftEnvelope` remains as a compatibility bound. The sharper `scalarLinearShiftBound`
uses translation subadditivity and sign symmetry to reduce any centered shift of magnitude at
most `B` to

```text
2 * samplerCertificateError + B * TV(D_Z,sigma + 1, D_Z,sigma).
```

The ring theorem pays one hybrid per coefficient, the native theorem pays one term per complete
BRK row, and both the universal and coupled support-wise constructors directly fill the concrete
certificate's `smudgingCost_le` field. The unit-shift term is no longer opaque:
`shiftDistance_discreteGaussian_unit_eq_mass_zero` proves it is exactly the centered discrete
Gaussian's mass at zero. For every natural `W ≤ sigma`, the finite-window theorem proves

```text
TV(D_Z,sigma + 1, D_Z,sigma) <= exp(1/2) / (W + 1).
```

This estimate is threaded through the scalar, ring, complete-BRK, universal-certificate, and
coupled averaged-real endpoints. `TFHE/AsymptoticNativeShiftedDiscreteGaussianBounds.lean` now
performs the parameter-growth accounting. Its `PolynomialGrowth` certificate derives polynomial
BRK-layout and centered-binomial residual bounds from explicit degree, rank, dimension, gadget
level/base, and error-width polynomials. Negligible ticket-certificate error and any inverse
window that is negligible then make the complete correct-side smudging loss negligible. In
particular, a checked `2^λ ≤ sigma = αq` window absorbs all polynomial factors; the result remains
negligible after adding a negligible output-normal-form term and after polynomially many uses.
The existing growing centered-binomial dimensions instantiate the full polynomial-growth
certificate. Their present polynomial modulus is not claimed to admit the exponential window:
choosing a correctness-compatible wide-Gaussian parameter family remains a real construction
obligation. A merely polynomial window yields only inverse-polynomial decay and is insufficient
for cryptographic negligibility. The universal `q / 2` residual fallback remains generally too
loose; the coupled centered-binomial residual bound is the intended sharp route.

`TFHE/NativeShiftedCenteredBinomialBounds.lean` proves that scalar-XOR transport changes each
source BRK row error only by sign under the transported scalar secret and unchanged ring secret.
`TFHE/NativeCoupledShiftedResidualBounds.lean` then retains the complete source secret pair as a
latent witness, proves that its public projection is exactly the existing coordinate source, and
uses centered-binomial support to replace the universal `q / 2` envelope by the sharp `eta`
envelope for every fixed coupled coin. Its averaged endpoint regenerates only the residual-bearing
BRK at the masked source scalar key, retains the exactly transported KSK and input tape, and is
proved close to its monomial comparison by the sharp discrete-Gaussian expression. Uniform XOR
masking and sampler reordering identify that comparison exactly with the ordinary augmented real
view. `DirectStatisticalCertificate.ofCoupledCenteredBinomialDiscreteGaussian` installs this
entire correct-side bound automatically; only output normal-form freshness and wrong-branch
rank/freshness remain as evaluator laws.

The normal-form audit is now refined by
`TFHE/NativeShiftedDifferenceReparameterization.lean` and
`TFHE/NativeAdaptiveShiftedDifferenceView.lean`. Translation by the transported source BRK is a
permutation, so the uniform true branch is exactly an independent uniform difference. The
digitizer consequently depends on that independent difference alone. The correct residual then
splits exactly into the retained transported source-row error and a separately bounded
zero-control perturbation; the adaptive evaluator is distributionally unchanged by this
reparameterization. This avoids automatically adding a second fresh error to the full source
error. `TFHE/NativeCiphertextTranslation.lean` proves the missing fixed-ciphertext translation
law: adding a public TGSW perturbation to an independent fresh direct encryption translates its
uniform masks bijectively and moves exactly the perturbation phase into the residual. The law also
lifts through an independently sampled perturbation.

`TFHE/NativeOffDiagonalResidualNormalForm.lean` derives the required independence from the actual
native BRK generator rather than postulating it. A generic two-coordinate finite-product theorem
pulls two distinct, never-failing coordinate samplers out independently. Consequently every
correct shifted-CMux output entry away from the selected control coordinate is exactly a direct
TGSW residual-encryption mixture, with the zero-control internal-product phase as residual. The
stronger whole-key theorem pulls the selected source entry out once, factors all remaining source
and difference entries into one conditional independent product, and residualizes every
off-diagonal coordinate simultaneously. It then compares this normal form with a fresh direct BRK
using the finite-product hybrid inequality and proves the explicit bound

```text
TV(correct shifted key, fresh direct key)
  <= diagonalError + sum_(j != i) offDiagonalError(j).
```

The diagonal is no longer an untracked failure of the factorization: it is the sole named
self-correlation term. There the retained fresh entry is itself the selected control, so the
translation lemma's independence hypothesis is genuinely unavailable. The separate
`NativeDiagonalResidualNormalForm` module now analyzes this term directly rather than assuming
independence.

The first bound above accepted a support-wise uniform estimate for that diagonal. The stronger
averaged-diagonal theorem avoids this generally wasteful requirement. It first replaces only the
off-diagonal residual encryptions, leaving the actual diagonal untouched. The intermediate whole
key is proved exactly equal to the diagonal marginal followed by fresh independent completion of
every other coordinate. Data processing therefore charges the second hop by

```text
TV(averaged self-correlated diagonal, one fresh direct TGSW entry),
```

not by the maximum conditional distance over fixed controls.

For the selected diagonal, fixing the complete uniform difference ciphertext fixes its gadget
digits. The apparently nonlinear self-correlated operation then becomes one linear row operator
on the homogeneous source TGSW ciphertext. The same operator acts on every public mask column and
on the source error vector. The checked assembly theorem proves this as a complete-ciphertext
identity. The transformed uniform challenge matrix is bounded by the exact finite
fiber-second-moment excess of this operator, without assuming that `ZMod q` is a field.

The same linear normal form gives a second exact route. If the fixed-difference row operator is
bijective, applying it independently to every mask column is bijective on the complete challenge
matrix, so uniform challenge transport is exact. Averaging the resulting zero cost on good
differences and the universal unit bound on bad differences proves

```text
TV(original diagonal mask, replaced uniform mask)
  <= Pr_difference[row operator is not bijective].
```

This applies directly over the production power-of-two coefficient ring and never invokes
finite-field rank.

The row operator now has a canonical square matrix. Entrywise it is exactly the identity matrix
plus the difference-digit matrix, with the latter negated for the `true` candidate. A general
commutative-ring theorem proves

```text
row operator is bijective
  <-> determinant(row matrix) is a unit.
```

Thus the displayed bad-rank probability is exactly a determinant non-unit probability, not an
upper-bound relaxation. The determinant-bounded whole-key constructor accepts any proved
candidate-wise estimate of this event and carries it through the existing mixed-error,
off-diagonal, and wrong-control accounting.

The probability space feeding that determinant is also explicit. Under exact gadget capacity
`q = B^ℓ`, fixed-length scalar decomposition is a bijection between `ZMod q` and its `ℓ`
base-`B` digits. The checked coefficientwise and complete-ciphertext lifts give the exact law

```text
uniform native TGSW difference
  --decompose every row/block/coefficient-->
uniform tensor of Fin B digits.
```

This is a joint distributional equality, so every digit in the tensor is mutually independent
and uniform. Casting those finite digits into `ZMod q` recovers exactly the entries used in the
identity-plus-signed-digit row matrix. Therefore no independence heuristic is needed in the next
determinant calculation.

That calculation gives a negative result for the rank route. When the level count is positive and
the exact-capacity base is even, reducing coefficients modulo two and evaluating at `X = 1` is a
checked ring homomorphism from the executable negacyclic carrier to `ZMod 2`. It maps the native
row matrix to the binary matrix above. The latter is exactly uniform, and exact finite-field
counting gives

```text
Pr[binary row matrix is rank-deficient] >= 1/2.
```

Binary rank failure implies that the original determinant is not a unit because ring
homomorphisms preserve units. Thus, for both candidate bits,

```text
Pr[determinant(row matrix) is not a unit] >= 1/2,
rankSharpDiagonalOperatorLoss >= 1/2.
```

The second inequality holds for arbitrary source and target error samplers. Consequently the
exact-rank and bounded-determinant certificate routes cannot prove negligible loss for this native
exact-capacity even-base family. They remain sound generic interfaces for other regimes; the
native proof must instead exploit the hidden difference jointly with the public challenge,
stronger cancellation in the self-correlated diagonal, or a construction change.

The direct joint-collision hybrid is now formalized. For every fixed source-error vector, its
uniform extractor input is the pair `(difference ciphertext, public challenge)`. Its retained side
information is the error vector transformed by the difference digits, and its extracted output is
the public challenge transformed by those same digits. A generic finite side-information
collision theorem groups total variation by the retained error and applies Cauchy--Schwarz only
over the challenge coordinate. Averaging this exact loss under the real source-error sampler and
then reassembling the TGSW ciphertext proves

```text
TV(averaged self-correlated diagonal, mask-replaced diagonal)
  <= E_sourceError[joint side-information collision loss].

TV(averaged self-correlated diagonal, fresh target entry)
  <= E_sourceError[joint side-information collision loss]
     + TV(mixed transformed source errors, fresh target errors).
```

The proof checks that both pair presentations are distributionally identical to the existing
difference-first operator and mask-replaced experiments. In particular, the transformed error is
not discarded or assumed independent, and the difference is never conditioned on. No row-matrix
invertibility, field structure, or linear digitizer is required. The corresponding whole-key
constructor installs this direct diagonal bound together with the existing off-diagonal and
message-one wrong-control fiber bounds.

The direct loss is also reduced completely to finite counting. For each retained-error value and
transformed challenge, the formal expression contains only the cardinality of the corresponding
joint extractor fiber, the retained-side fiber cardinality, and the finite input/output sizes.
The probability-level side-wise loss is proved exactly equal to that normalized cardinality sum.
A parallel Pearson interface proves

```text
TV(real joint extractor, side-marginal times uniform challenge)
  <= sqrt(conditional fiber chi-square) / 2.
```

The chi-square term is itself an explicit normalized sum of the same fiber counts. It is a
counting-friendly relaxation of the side-wise bound, useful when one global rank, codimension, or
Fourier estimate is available. Averaging it over centered-binomial source errors, assembling the
ciphertext, maximizing over both candidate bits, and installing it in the whole-key certificate
are all formalized; no additional security premise is introduced by this reformulation.

The squared fibers are now expanded one step further into two-copy collisions. Fix two independent
difference ciphertexts. Equality of their two transformed challenges is the zero fiber of the
rectangular additive map

```text
(left challenge, right challenge)
  |-> A_left(left challenge) - A_right(right challenge).
```

Its row-level domain has twice the width of its codomain. If that row map is surjective, the full
challenge-pair collision count is proved exactly equal to the uniform baseline. The retained-side
fiber itself is proved to be the difference-only fiber times the complete challenge space, and the
full conditional collision count is exactly

```text
uniform baseline over all retained difference pairs
  + summed paired-operator collision excess.
```

This expansion now keeps the exact side-fiber weights. Write `D` for the number of difference
ciphertexts, `C` for the number of challenges, `K_t` for the number of differences producing a
retained error `t`, and `E_t` for the paired collision excess summed over ordered pairs in that
fiber. The checked identity is

```text
fixed-error conditional chi-square
  = sum over t with K_t > 0 of E_t / (D C K_t).
```

No worst-case retained-fiber estimate occurs. Nonnegativity of every pair excess also gives the
source-error-independent relaxation

```text
fixed-error conditional chi-square
  <= total excess over all ordered difference pairs / (D C).
```

The latter no longer mentions the source error, its sampler, or a retained side fiber. The
whole-key constructor
`ofDiagonalGlobalPairCollisionBudgetAndMessageOneControlFiberLoss` consumes candidate-wise bounds
on precisely this global quantity. This source-error independence is a strict relaxation:
replacing each nonempty `K_t` by one can discard essential cancellation.

The equal-difference slice now gives a checked obstruction to using this global relaxation. When
the left and right differences coincide, the paired zero fiber is exactly a freely chosen base
point times the kernel of the original square row operator. Every non-bijective square operator
therefore contributes at least one complete challenge-cardinality unit of excess. After
normalization, Lean proves

```text
single-difference rank-failure probability
  <= source-independent global pair-collision budget.
```

At exact gadget capacity with positive levels and even base, the left side is at least `1/2`.
Thus the global budget cannot be negligible for this regime, regardless of how many gadget levels
grow with the security parameter. This is a statement about the relaxed upper-bound expression,
not the exact retained-fiber chi-square loss.

The exact retained-fiber expression is now split before that relaxation. For every fixed source
error, Lean partitions the ordered difference pairs into equal and distinct slices and proves

```text
conditional chi-square = normalized self excess + normalized distinct excess,

sqrt(conditional chi-square) / 2
  <= sqrt(normalized self excess) / 2
     + sqrt(normalized distinct excess) / 2.
```

For one equal pair, its challenge-collision excess is exactly the challenge cardinality times
`kernelCard^ringRank - 1`. Substitution into the retained-fiber denominator cancels the complete
challenge cardinality. The normalized self slice is therefore an average of these kernel factors
inside each nonempty transformed-error fiber, divided by the complete difference-space
cardinality. A pointwise kernel-factor bound `B` yields the checked estimate

```text
normalized self excess
  <= number of nonempty transformed-error fibers * B / D.
```

The pointwise hypothesis is stronger than necessary. The formal certificate instead bounds the
average kernel factor separately inside every nonempty transformed-error fiber. A native
difference ciphertext is exactly a challenge matrix paired with a body vector, and that body has
the same carrier as the transformed error. Combining this cardinality factorization with the
nonempty-fiber count gives the sharper checked interface

```text
within-fiber average kernel factor <= B
  implies
normalized self excess <= B / |Challenge|.
```

The certificate is required only on the support of the actual centered-binomial source-error
sampler and for the two candidate bits. Its challenge-normalized square-root loss feeds the base
and public-evaluation TFHE confidentiality theorems directly. Thus the remaining self-slice task
is precisely to prove that this conditional average kernel factor is a negligible fraction of the
challenge space; a worst-case pointwise kernel bound is not silently substituted for it.

The distinct slice now has the parallel retained-fiber interface. If the total distinct-pair
challenge excess in every transformed-error fiber satisfies

```text
distinct excess in fiber t <= K_t * |Challenge| * B,
```

then its normalized Pearson contribution is at most `B / |Challenge|`. This condition measures
the average normalized collision excess per retained first difference; it does not sum unrelated
fibers or replace `K_t` by one. It too is required only on the actual centered-binomial support.

The native paired-row magnitude is now exact rather than estimated only from residue rank. Let
`N` be the cardinality of one native row space and `I` the image cardinality of the paired row
operator. The finite homomorphism theorem gives

```text
row zero-fiber cardinality = N * (N / I),

fixed-pair challenge collision excess
  = |Challenge| * ((N / I)^ringRank - 1).
```

Thus `N / I` is the actual native cokernel cardinality. It is one for every binary-full-rank
pair, and its complete challenge factor cancels from the retained-fiber normalization. A checked
bridge now reduces the distinct certificate to an upper bound on the conditioned average of
`(N / I)^ringRank - 1`. This avoids the earlier worst-case replacement of one missing binary rank
by a full `|Rq|` factor. The remaining quantitative problem is to control this exact cokernel
average under the gadget-digit law while retaining the transformed-error fiber; residue-rank
failure probability alone does not provide that magnitude bound.

The source-error quantifier is now weakened to the event that is actually typical. For any
predicate `Good` on a sampled source-error vector, the checked mixture theorem gives

```text
selected-diagonal mask distance
  <= good-event retained self/cokernel loss + Pr[not Good].
```

No maximum over bad errors occurs: the universal distance bound one is multiplied by their actual
probability. For positive-width centered-binomial ring errors, toggling one source coin proves that
coefficient reduction modulo two followed by evaluation at `X = 1` is exactly a fair bit. Hence,
for `m` independently sampled TGSW rows,

```text
Pr[every source-error row has zero parity] = 2^-m.
```

The canonical modulus and negacyclic degree are both proved to be positive powers of two. The
parity map is local on this ring, so nonzero parity reflects an actual unit. Therefore the chosen
good event is equivalently strong enough to provide a unit source-error row, and its complement is
negligible in the canonical growing family. The complete static-mask, adaptive-context, and
post-smudging proof now consumes estimates only on this good event. The remaining statistical
lemma is correspondingly sharper: bound the retained self-kernel and paired native cokernel
averages conditioned on a source-error vector that contains a unit row. The parity calculation
does not itself prove those conditioned estimates.

The unit row is now also used quantitatively at exact gadget capacity. Choose its flattened
block/level coordinate and fix every digit column except that one. Equality of the transformed
retained error then determines the omitted small-coefficient digit polynomial uniquely in every
matrix row. The proof is an injective slice, not a claim that the small digit polynomial is
uniform over the whole coefficient ring. Transferring through the exact ciphertext-to-digit
equivalence gives the checked native fiber bound

```text
|fixed transformed-error fiber|
  <= base^(m * (m - 1) * (degree + 1)),

m = TGSW.rowCount.
```

Thus conditioning on a good source-error vector provably removes at least one complete
digit-polynomial column per row. This is the first direct conditioned-fiber count supplied by the
unit event. For the canonical centered-binomial family, failure of this existential unit-column
fiber bound has probability at most `2^-m`. It does not alone bound the self-kernel or
distinct-cokernel averages, because those quantities weight the remaining fibers by operator
zero-fiber sizes.

The conditioned fiber is now described exactly. An assignment of every nonselected base-digit
column determines one selected ring polynomial; it belongs to the fiber precisely when that
polynomial is representable by small base digits. The predicate uses only one matrix row at a
time. Consequently the complete valid assignment type is equivalent to the dependent product of
its valid-row types, and the fiber cardinality is their exact product.

This row product also factors the self-kernel moment without assuming that the conditioned rows
are uniform in an ambient ring. Expanding the `ringRank`-th kernel-cardinality power chooses
`ringRank` proposed kernel vectors. Exchanging the finite sums turns the number of row families
annihilating those vectors into a product of simultaneous one-row acceptance counts. The zero
tuple accepts every valid row and is exactly the uniform baseline, so it cancels. The retained
self excess is therefore exactly

```text
sum over nonzero tuples v
  product over rows r
    |valid reconstructed rows at r annihilating every vector in v|.
```

The distinct-pair cokernel sum has also been reindexed as a double product of valid reconstructed
rows.

The first quantitative nonzero-tuple bound is now checked. Besides the retained equation, a
proposed kernel vector gives a second equation in the selected digit column and any chosen pivot
column. If the corresponding native `2 × 2` minor is a unit, two accepting valid rows that agree
off the pivot are equal. Hence accepting rows inject into the digit space with both columns
omitted, removing a second complete digit polynomial.

For the production power-of-two local ring, parity evaluation characterizes the complementary
event exactly. Once the selected source entry is a unit, every selected/pivot minor is nonunit if
and only if the proposed value's binary parity vector is a scalar multiple of the source parity
vector. This binary line has two points. Uniform fibers of the surjective coordinatewise parity
map give the division-free exact identity

```text
badValueCount * 2^m = 2 * allValueCount.
```

For a tuple of `t` proposed values, the all-bad tuple set is the Cartesian `t`-th power and has
the corresponding powered density. The complete simultaneous-row moment is therefore bounded by
a two-column term for all tuples plus a one-column term only for this exactly counted bad set.

This does not yet prove the retained statistical loss negligible. The loss divides by the size of
each conditioned valid transformed-error fiber, whereas the new theorem is an absolute count.
Replacing every nonempty fiber size by one loses the cancellation needed by the canonical
parameters. The next analytic obligation is a distribution-aware good/bad estimate that preserves
that denominator, together with the paired reconstructed-row cokernel weight. Independently, this
rank calculation does not remove the computational bilinear circular-coordinate prediction
premise of intact TFHE.

After averaging over the real source-error sampler and maximizing over both candidate bits, the
canonical selected-diagonal mask loss is bounded by the sum of the corresponding self and
distinct losses. The two finite fiber-average certificates combine into one selected-diagonal
loss and discharge the exact base and public-evaluation confidentiality endpoints. This is a
sound route around the global-budget obstruction, not yet a proof that the canonical certificate
loss is negligible: the remaining analytic work is a distribution-aware bound for the certified
within-fiber kernel average and a paired-rank or Fourier estimate for the certified distinct-pair
average.

For the production-style exact-capacity even-base distribution, that rectangular digit law is
now exposed over the binary residue field. If `m = TGSW.rowCount`, the two independent square
binary row matrices concatenate and transpose to an exactly uniform `2m`-by-`m` matrix. The
checked finite-field bound is

```text
Pr[binary paired rank < m] <= 2 / 2^(m + 1).
```

The matrix is proved entrywise equal to the transpose of the parity image of the concrete paired
native row matrix. This supplies genuine exponential entropy slack for independently sampled
generic pairs, but it cannot repair the global sum: the equal-difference diagonal pairs retain the
square obstruction above. The abstract lifting step is now proved as well. For any
surjective ring homomorphism that reflects units, a left inverse of the reduced transpose lifts
entrywise; the lifted square product has unit determinant, and its transposed inverse gives a
right inverse of the original paired row matrix. Thus binary full rank implies native row
surjectivity and zero challenge-collision excess for that pair. Unit reflection is now proved for
the concrete production ring `ZMod (2^k)[X]/(X^(2^d)+1)`, `k > 0`. Coefficient reduction to the
binary quotient has nilpotent kernel, while the binary parity kernel is nilpotent because the
modulus is `(X - 1)^(2^d)`; hence a binary-full-rank pair has exactly zero native excess without a
local-ring premise. The residual rank-deficient event and its native zero-fiber sizes are
translated into the weighted collision excess above by a checked accounting bound. If `B` is the
number of deficient ordered pairs, `D` the difference
cardinality, and `C` the challenge cardinality, then `B / D^2` is exactly the rank-failure
probability, total excess is at most `B C^2`, and the relaxed global budget is at most
`(B / D^2) D C`. The additional `D C` magnitude factor shows formally why rank-failure probability
alone is insufficient.

The next zero-fiber step is now formalized. For every finite additive homomorphism,

```text
zeroFiberCard * imageCard = domainCard.
```

Coefficient reduction induces a surjection from the native matrix image to the binary image. More
importantly, when the reduction is local, binary rank `r` lifts to a free native image of size at
least `|Rq|^r`. The proof chooses a basis of the reduced image, lifts preimage columns through the
surjective parity map, and proves their native column map injective by lifting a left inverse; no
Smith-normal-form assumption is used. Therefore every pair satisfies

```text
native row zero fiber <= rowDomainCard / |Rq|^r.
```

Full-rank pairs are still assigned exact zero excess. Deficient pairs use the displayed
rank-sensitive zero-fiber bound, and their individual envelopes are summed before division by
`D C`. The resulting `binaryRankWeightedDifferencePairCollisionBudget` bounds the earlier global
budget, the exact retained-fiber Pearson expression, and the selected-diagonal distance. It is
also installed directly in a whole-key certificate. For coefficient modulus `2^k`, `k > 0`, and
ring degree `2^d`, the construction is premise-free because the parity map's local property was
already proved.

This closes the algebraic zero-fiber lift, but the diagonal-slice theorem shows that no
higher-adic refinement of this unconditional global sum can make it negligible in the stated
exact-capacity even-base regime. Completing the native statistical proof through collisions now
requires a direct estimate of the exact retained-fiber-weighted quantity
`sum E_t / (D C K_t)` or another argument that preserves the retained transformed-error
restriction. The alternative computational endpoint is the explicit native CircLWE/KDM
assumption together with ordinary LWE.

For the earlier concrete family with six fixed gadget levels, ring rank one gives
`m = (1 + 1) * 6 = 12`, independent of `λ`. Exact capacity and the even base identify the generic
paired-rank tail with one fixed uniform `24`-by-`12` binary matrix experiment. Lean proves its
exact finite-field product formula, the uniform lower bound

```text
2^-24 <= Pr[rank < 12],
```

and `not negligible (fun λ => Pr[rank < 12])`. The newer global-budget obstruction is stronger:
its constant floor persists even in the growing-level family. Both statements concern certificate
terms, not the true diagonal statistical distance; cancellation in the exact retained-fiber
expression can still be stronger.

For comparison, the earlier conditional bound averages the challenge-fiber loss after fixing the
difference and then hides the difference inside a single mixed transformed-error marginal:

```text
TV(averaged self-correlated diagonal, fresh target entry)
  <= E_difference[challengeFiberLoss]
     + TV(mixed transformed source errors, fresh target errors).
```

That conditional first term may instead be replaced by the exact bad-rank probability above. The
direct joint expression is installed by
`WholeKeyRankCertificate.ofDiagonalJointCollisionAndMessageOneControlFiberLoss`, while its global
chi-square relaxation is installed by
`WholeKeyRankCertificate.ofDiagonalJointChiSquareAndMessageOneControlFiberLoss`; the legacy
conditional expressions are installed by
`WholeKeyRankCertificate.ofDiagonalOperatorAndMessageOneControlFiberLoss` or
`WholeKeyRankCertificate.ofDiagonalRankFailureAndMessageOneControlFiberLoss`. Thus the diagonal
is no longer an opaque statistical premise. A third constructor accepts an external bound on the
equivalent determinant non-unit event. Proving the direct side-information collision loss and the
mixed-error distance negligible for a compatible parameter family remains the quantitative
construction-specific obligation.

The whole-key argument also has a two-sampler form. The real shifted key may use a
centered-binomial source sampler while the comparison BRK uses any target sampler, including the
certified ring discrete Gaussian. Off-diagonal replacement completes every changed coordinate
with the target sampler, and the diagonal hop compares the averaged source diagonal directly with
one target entry. Thus no same-noise assumption is hidden in the finite-product hybrid.

`NativeAdaptiveOffDiagonalSecurity` lifts this statement to the actual adaptive public view.
Centered-binomial scalar transport is proved distributionally exact for the direct BRK, the
source BRK and uniform true branch are reordered or erased only through checked totality laws, and
the transported KSK and bounded input tape are retained verbatim. The correct coupling is exactly
the actual averaged evaluator; the target coupling is exactly the ordinary augmented real public
view. Hence the checked adaptive theorem has the same bound

```text
TV(actual averaged correct transform, target real public view)
  <= averagedDiagonalError + sum_(j != i) offDiagonalError(j).
```

The corresponding direct statistical-certificate constructor now discharges the generic
correct-view field from precisely these diagonal and off-diagonal premises. Wrong-branch
freshness remains a separate premise, as required by the candidate-recovery interface. If the
stronger fixed-mask `WrongBranchFresh` bijectivity law is supplied, the mask-averaged wrong branch
is proved exactly equal to the uniform comparison distribution. Its TV contribution is therefore
exactly zero. The whole-BRK bijectivity law is now factored exactly into independent
TGSW-entry maps, and each entry map into independent TLWE-row maps. Consequently the transported
`WrongBranchFresh` condition follows from a family of explicit `RowBranchFresh` predicates on
finite row spaces; no additional probabilistic loss is introduced by either product lift.

There is also a quantitative form for contexts where those row maps are not permutations. The
TV defect of one TGSW entry is bounded by the sum of its independent TLWE-row defects, and the
whole-BRK defect is bounded by the sum over entries. Data processing retains the transported KSK
and input tape for free. Finally, shared-mixture convexity averages the resulting double sum with
the exact probabilities of the scalar XOR masks. Thus the native freshness obligation can be
supplied as an explicit mask-averaged family of single-row TV estimates; it is not inflated to a
worst-case mask bound.

The final certificate no longer requires this inequality separately for every BRK in the source
support. A joint bad-event game samples the actual correlated `(BRK, KSK, input tape)` context and
then the independent scalar mask. The complete wrong-view distance is at most the probability
that the sufficient rowwise bijectivity condition fails in that joint game. A finite union bound
decomposes it into named output-coordinate/row failure probabilities as a compatibility bound.

A sharper exact conjugacy removes that union. After translating the true row by its fixed false
row, every row map is the same control-only map. The false row appears only through invertible
input/output translations, so all named row-failure events coincide. Exact gadget recomposition
then writes the normalized map as the identity plus the digit-weighted canonical homogeneous
part of the message-one candidate control. Scalar XOR transport cancels against the transported
complementary candidate, so its bad-event probability is unchanged when the evaluator mask is
discarded. Projecting the original coordinate source further leaves a minimal marginal containing
only the hidden bit and its selected original TRGSW control. Expanding secret, BRK, KSK, and tape
generation proves that this marginal is exactly equal in distribution to a canonical experiment: sample
one uniform bit, sample one uniform ring secret, and generate one TRGSW control. Thus the complete
wrong-view distance is bounded by one coordinate-free control-failure probability, with no KSK,
input tape, scalar-coordinate name, unselected BRK entry, or TGSW-row factor. Rare bad controls
are still charged by their actual probability rather than prohibited support-wise.

For centered-binomial noise, the canonical experiment normalizes one step further. The checked
coefficientwise negation symmetry of centered binomial proves that applying the complementary
candidate to an encryption of the hidden bit has exactly the distribution of a native TRGSW
encryption of message one. Averaging this pointwise equality erases the uniform hidden-bit draw
entirely. Consequently both the canonical non-bijectivity probability and the canonical expected
one-row TV defect equal quantities over only a uniform ring secret and one generated message-one
control. This is an exact distributional reduction, not a negligibility estimate.

Exact bijectivity is not mandatory. Translation conjugacy also proves equality of every data-row
TV defect with the normalized control-only defect. Product-TV accounting then bounds the complete
wrong view by the number of independently transformed TLWE rows times the expected normalized
defect in the same canonical one-control experiment. This direct route is potentially sharper
when a control map is non-bijective but its uniform pushforward remains close to uniform.

The normalized defect now has a sound collision formulation that does not treat the digitizer as
linear and does not treat `ZMod q` as a field. For a fixed message-one control, let `F` be the
concrete identity-plus-digit endomorphism of the finite TLWE row space and let

```text
M2(F) = sum_y |{x : F(x) = y}|^2.
```

The checked finite collision argument proves

```text
TV(F(U), U) <= sqrt(M2(F) / |Row| - 1) / 2.
```

This pointwise bound is averaged under the actual generated message-one control sampler, even
though that sampler is nonuniform, and the existing product lift then bounds the complete wrong
view by the output-row count times this expected fiber loss. A second theorem accepts the more
familiar support-wise estimate `M2(F) <= |Row| * (1 + epsilon)` and returns
`sqrt(epsilon) / 2`. `WholeKeyRankCertificate.ofMessageOneControlFiberLoss` threads the exact
expected form into the final native certificate. The remaining task is number-theoretic or
probabilistic: prove that this explicit fiber excess is negligible for a compatible generated
control family.

The message-one reduction is now parameterized by its actual algebraic requirement rather than
by the name of one distribution. Any native ring-error sampler whose point probabilities are
invariant under negation admits exact complementary-candidate normalization. For compiled
discrete Gaussian noise, `TicketNegationSymmetric` is the finite check that every ticket value and
its negation occur equally often. It implies exact symmetry of the scalar table and its
coefficientwise ring lift. Consequently the same certified table supports exact scalar-XOR BRK
transport, exact hidden-bit elimination, the complete wrong-view fiber theorem, and the existing
Gaussian shift bounds. This supplies a coherent wide symmetric Gaussian interface, but it does
not prove the wrong-control fiber excess or the selected diagonal's challenge-fiber and mixed-error
terms negligible.

These three construction laws are packaged as `WholeKeyRankCertificate`; the name is deliberate.
It is a transparent native TFHE rank/circularity premise, not a claimed consequence of ordinary
LWE. A certified ring discrete-Gaussian target is available as a direct specialization. The
`ofWrongBranchFresh` constructor installs exact bijectivity with zero freshness error, leaving
only the diagonal and conditional off-diagonal distances. The companion
`ofMaskedRowBranchDistance` constructor installs the quantitative row sum as the freshness error.
The average-case `ofAveragedRowwiseFailure` constructor instead accepts the joint generated-view
rowwise failure probability, while `ofAveragedControlFailure` accepts the sharper single-control
bound. The still sharper `ofCanonicalControlFailure` constructor accepts one scalar bound for the
coordinate-free canonical experiment and installs it uniformly at every scalar coordinate. The
transported control probability, selected-control marginal, and canonical probability are all
proved exactly equal, so no auxiliary-sampler or coordinate loss is introduced.
The `ofCanonicalControlDistance` constructor installs the direct expected-TV alternative, with
the explicit output-row multiplier retained in its premise.
For centered-binomial source noise, `ofMessageOneControlFailure` and
`ofMessageOneControlDistance` expose the final normalized premises directly, with no hidden bit;
the corresponding complete wrong-view endpoint theorems use the same exact equalities.
`ofMessageOneControlFiberLoss` further replaces the opaque direct-TV premise by the explicit
finite-map fiber loss above.
`ofDiagonalOperatorAndMessageOneControlFiberLoss` additionally replaces the opaque correct-side
diagonal premise by the sharp finite operator loss while retaining the conditional off-diagonal
premise.
`ofDiagonalRankFailureAndMessageOneControlFiberLoss` uses the exact diagonal non-bijectivity
probability in place of the challenge-fiber term and retains the same mixed-error and
off-diagonal obligations.
`ofDiagonalDeterminantBoundAndMessageOneControlFiberLoss` accepts an explicit bound on the
equivalent determinant non-unit probability. The binary obstruction proves that no negligible
bound can satisfy this premise for a positive-level exact-capacity even-base native instance.
The certificate builds the finite augmented paired-search reduction after its amplification
rounds and positive threshold schedule are supplied. The averaged adapter has no separate
effective-gap premise; its full bad-context term remains in the resulting loss.

The general asymptotic candidate-view lift then proves

```text
public augmented CircLWE advantage
  <= narrow augmented paired-search success + direct candidate loss.
```

For the growing centered-binomial family this is now composed pointwise with the adaptive TFHE
hybrid itself:

```text
adaptive TFHE advantage
  <= narrow augmented paired-search success
     + direct native candidate-evaluator loss
     + three ordinary joint-LWE advantages.
```

The corresponding asymptotic theorem concludes confidentiality alone, and a second theorem
preserves it under arbitrary public cloud-key-dependent evaluation with exactly zero additional
advantage. Neither theorem mentions functional correctness. This is a complete whole-key-search
accounting endpoint, but the averaged amplification loss is not claimed negligible: the
bad-context division term can remain large when the base averaged coordinate error is close to
one half. Candidate loss and paired-search hardness must therefore still be bounded separately
before using this route for a selected construction.

Unlike the older adapter, this theorem does not require an auxiliary residual witness. The
growing centered-binomial family also has a convenience wrapper that pairs security with its
independent probability-one refresh theorem. That wrapper is optional; the security theorem does
not use refresh or any other correctness proposition.

`PointwiseCandidateViewTransformer.realUniformDistance_le_errors_of_context_overlap` now audits
the strength of that endpoint. If the same fixed public BRK+KSK context occurs in the source
support with both hidden scalar-bit values, triangle inequality forces

```text
TV(realPublicView, uniformPublicView) ≤ correctError + wrongError.
```

Thus a small pointwise statistical error cannot follow merely from computational CircLWE
indistinguishability. `TFHE/AveragedCandidateView.lean` records the weaker averaged contract and
proves its exact one-shot gap. Shared-context repetition remains sound through the new generic
threshold theorem

```text
amplified failure ≤ amplifiedError(rounds, τ) + averageBaseError / τ.
```

The division term is the cost of bad fixed contexts and cannot generally be removed. In
particular, an averaged advantage by itself does not supply the high-quality conditional gap
needed to recover every scalar coordinate from one shared cloud key.

The preferred security-only fallback therefore stops after one coordinate instead of claiming
whole-key recovery. The averaged transformer induces an executable tester for any selected
scalar-secret coordinate, and Lean proves the exact finite inequality

```text
public augmented CircLWE advantage
  <= selected-coordinate prediction bias
     + selected-coordinate correct-view error
     + selected-coordinate wrong-view error.
```

This statement has no shared-context repetition, threshold, bad-context division, or coordinate
union bound. The scalar-key randomization theorem does not provide those missing independent
contexts: it holds the ring key fixed and transports one already sampled cyclic BRK--KSK view.
Accordingly, the unused effective-gap field has been removed from the averaged reduction
interfaces; the pointwise interface keeps its genuinely used support-wise gap premise.

The asymptotic one-shot lift defines the corresponding coordinate-prediction security game and a
separate statistical-error game. Negligibility of both implies public augmented CircLWE security.
For the growing centered-binomial family, composition with the adaptive zero-side hybrid gives

```text
adaptive TFHE advantage
  <= selected-coordinate prediction bias
     + selected-coordinate statistical error
     + two actual-context joint-LWE advantages
     + one uniform-BRK-context joint-LWE advantage.
```

The direct-certificate specialization exposes the statistical term as the selected coordinate's
correct error plus freshness error. It concludes adaptive TFHE confidentiality from negligible
coordinate-prediction bias, negligible component errors, and ordinary joint LWE. Public
cloud-key-dependent evaluation adds zero loss. No correctness proposition appears in either
endpoint. The remaining computational premise is deliberately named one-coordinate native
circular-prediction hardness; it is not asserted to follow from ordinary LWE or RLWE.

The discrete-Gaussian target growing family now makes the correct-side smudging premise
parameter-compatible. It chooses

```text
q = (2N)^(lambda + 1),   levels = lambda + 1,   alpha = 1/(2N),
```

and proves `alpha * q = (2N)^lambda >= 2^lambda`. The canonical specialization constructs finite
Gaussian ticket tables at denominator `q(q+1)2^lambda`, proves their certificate error at most
`2^-lambda`, and proves exact ticket-count symmetry under negation by assigning every leftover
ticket to zero. The wrong-view law is now internalized: the exact message-one control fiber loss
is multiplied by the polynomial native BRK layout. The selected diagonal law is also internalized
by the sharp challenge-fiber plus mixed transformed-error operator theorem. Finally, each
complete off-diagonal replacement hop is bounded by convexity using its exact expectation under
the generated source control. Exact equivalence between structured and direct TGSW sampling then
rewrites this average as an IID expectation over the control-error vector. The control's public
mask, ring secret, and gadget message disappear from the residual law. Centered-binomial
negation symmetry then removes the remaining Boolean maximum. What remains is the explicit
finite `L²` mass difference between
`fresh centered-binomial error + uniform-digit operator (signed centered-binomial control error)`
and the compiled target error vector, summed over the off-diagonal layout. The source law is
proved to be a deterministic image of uniform bit-pair tables and the target law a deterministic
image of uniform ticket indices. At exact gadget capacity, the uniform difference ciphertext is
also replaced exactly by one IID base-digit tensor, so the whole expectation is one finite uniform
average of explicit digit/bit-pair/ticket output-fiber cardinalities. Ordinary `L²` is used instead
of Pearson divergence because downward ticket rounding may give some target residues zero
executable mass.

This normalization also exposes an obstruction to the proposed wide-Gaussian statistical hop.
Every coefficient of every real residual row is deterministically bounded by

```text
eta + ((rank + 1) * levels) * N^2 * (base - 1) * eta.
```

The checked norm-threshold theorem proves that one minus the target's mass in this ball is a lower
bound on total variation from the real residual law. For the present family the real bound is
polynomial while the target integer Gaussian width is `(2N)^lambda`; consequently this hop must
not be presented as generic statistical smudging. The conditional canonical theorem remains a
valid implication from its explicit fiber-negligibility premise, but the sound completion route
is now a computational RLWE/native-circular hybrid (or a matching narrow target), not a proof that
the current wide target is statistically close. No correctness statement is used.

`Widened.AveragedCandidateViewTransformerReduction.toCoordinateSecretReduction` propagates this
exact thresholded error through every scalar coordinate. Its scalar and paired-secret adapters
apply the finite union bound and the existing centered-binomial KSK decoder, after which
`publicHardAgainst_of_pairedSecretReduction` transfers narrow search hardness to the widened
public decision game. Thus the averaged fallback is complete at the generic reduction-accounting
level; every bad-context division term remains visible in the final loss.

`TFHE/AsymptoticNativeResidualCandidateView.lean` lifts this final finite inequality without
adding a cryptographic assumption. It defines security-parameter-indexed public native CircLWE
distinguishers, paired-search solvers, evaluator reductions, and an explicit reduction-loss game,
then proves

```text
public CircLWE advantage
  ≤ generated narrow paired-search success + residual reduction loss.
```

Negligibility of both right-hand terms implies public CircLWE security. A public distinguisher is
embedded into the repository's older continuation carrier by ignoring both secret arguments; the
two advantages are proved exactly equal. Adding the existing zero-message side-information branch
therefore also gives native monomial-KDM security for this exact public image class.

`TFHE/CenteredBinomialGrowingNoiseCircularSearch.lean` supplies the concrete arithmetic needed by
that theorem. It selects level one of the six-level base-`2N` KSK gadget, proves the selected code
is `2N`, proves its centered distance from zero is exactly `2N`, and derives the KSK recovery
margin from the already checked `2(λ+1) < N` family bound. Thus the growing-family endpoint now
leaves only an averaged shifted-evaluator certificate, narrow paired-search hardness, and
negligibility of the displayed evaluator loss.

### Public augmented CircLWE for the actual adaptive transcript

The adaptive encryption adversary does not need a secret-aware continuation once its bounded
zero-message input tape is made part of the auxiliary input. The public view is exactly

```text
BRK, KSK, bounded TLWE input tape.
```

`TFHE/AdaptivePublicAuxiliaryInputCircular.lean` proves that scalar XOR masking transports all
three components exactly. The existing BRK and KSK permutation is paired with the exact batch-TLWE
transport, so both the real centered-binomial endpoint and the uniform-BRK endpoint incur zero
statistical loss. It then proves that the honest bounded adaptive real-to-zero BRK replacement is
exactly the public augmented KDM advantage for this view. The generic KDM triangle gives

```text
adaptive BRK replacement
  ≤ public augmented CircLWE + public augmented zero branch.
```

The zero branch is not retained as a circular assumption: it is bounded by an ordinary joint-LWE
game in the actual zero-BRK context and another in the exactly uniform-BRK context. Composing with
the final adaptive endpoint yields one public augmented CircLWE term, two copies of the
actual-context joint-LWE term, and one uniform-BRK-context joint-LWE term. The asymptotic lift
proves negligible adaptive TFHE advantage whenever the public-view and joint-LWE reductions
preserve the selected efficiency classes and those two target games are secure.

`TFHE/AdaptiveAugmentedPairedRecovery.lean` gives the matching search backend. A scalar solver may
inspect the BRK, KSK, and complete tape; the retained centered-binomial KSK still completes a
correct scalar candidate to the full scalar/ring key pair with exactly the same success
probability. A cross-distribution adapter therefore reduces public augmented CircLWE hardness to
narrow augmented paired-search hardness plus the explicit loss of a supplied scalar candidate
reduction. `TFHE/AdaptiveAugmentedCandidateView.lean` constructs that scalar reduction from an
averaged candidate transformer over the complete `(BRK, KSK, tape)` source, with the sound
threshold/bad-context term and whole-key coordinate union bound. The residual adapter then proves
that averaged correct-real and wrong-uniform-BRK residual normal forms, plus support-wise smudging
costs, satisfy this transformer contract automatically. Its asymptotic lift bounds public
augmented CircLWE advantage by narrow augmented paired-search success plus the exact evaluator
loss. Finally, the growing centered-binomial specialization composes that bound with the adaptive
bridge. Its security-only headline has search, residual-loss, and ordinary joint-LWE premises but
no correctness proposition or separate public CircLWE premise; probability-one refresh is an
independent optional conclusion.

The remaining BRK-first construction is therefore precise: prove negligible quantitative bounds
for the now-executable transform. For the correct candidate, the computed residual phase law, the
exact conditioned-coin reparameterization, the complete off-diagonal residual-encryption normal
form, and its exact adaptive lift to the ordinary real target are checked. The security theorem
now fixes the remaining correct loss canonically as the sharp diagonal operator quantity plus the
effective residual-vector `L²` loss averaged under the actual generated control and maximized over
the finite secret pair. Public masks, gadget messages, and ciphertext assembly are no longer part
of that analytic obligation; what remains is to prove that these explicit finite mass expressions
are negligible for the chosen parameters.
For the complementary candidate,
the open quantity is the exact averaged fiber-second-moment loss for one generated message-one
control's identity-plus-homogeneous digit perturbation.
The hidden scalar bit, mask, tape, KSK, false rows, output coordinates, and row indices have all
been removed from this event by exact equalities. Because bijectivity is only a sufficient route,
a future joint-distribution theorem
may bypass it if it is too strong for multilevel digit decomposition. The whole-key search route
must additionally make the explicit thresholded loss negligible. The one-shot security route
instead needs only the selected-coordinate correct/freshness errors to be negligible, together
with the explicitly named coordinate-prediction premise. Generic augmented
candidate recovery, residual smudging, homomorphic phase algebra, exact tape transport,
scalar-to-paired completion, the finite and asymptotic public adaptive composition, and the
opposite-edge KSK-first coordinate transform are checked. In the canonical one-shot endpoint,
the correct/freshness laws themselves have been replaced by the three exact finite quantities
above. Ordinary RLWE alone is not substituted for their missing analytic bounds, the circular
coordinate-prediction premise, or augmented paired-search hardness.

The generic finite-field rank lemmas do not directly discharge this message-one obligation. The
production map contains multilevel base-digit decomposition, which is nonlinear as a map of the
ring coefficient, and the power-of-two coefficient ring is not a field. Applying a random-matrix
rank theorem here would therefore require a separate, construction-specific linearization or
fiber-count theorem; no field assumption is silently introduced.

## Standalone `RGSW_S(-S)` short-preimage route

The standalone ring-square distribution admits a separate reduction that does not assume generic
degree-two circular security. After the checked direct-phase normalization, each upper row has
target phase `S² g_l` and each lower row has target phase zero. A public compiler starts from
ordinary batch-RLWE rows and, for every gadget level, seeks public coefficients `x_i` satisfying

```text
Σ_i x_i a_i = g_l.
```

On success, the resulting row is exactly a genuine square row except that its fresh error is
translated by `S * Σ_i x_i e_i`. With ring degree `N`, `m_source` source rows, secret bound
`B_s`, selector bound `B_x`, and source-error bound `B_e`, the checked coefficient bound is

```text
||S * Σ_i x_i e_i||∞ ≤ N² * m_source * B_s * B_x * B_e.
```

There is now a nearly matching information-theoretic construction for `B_x = 1`. Reserve one
uniform mask with coefficient one and give each of `m` additional masks a binary coefficient.
For every fixed target, a second-moment argument proves that a fraction at least

```text
2^m / (2^m + q^N)
```

of mask families has such an anchored binary preimage. Consequently, a pointwise-complete
selector fails at one level with probability at most `q^N/(2^m + q^N)`, and at `L` levels with
probability at most `L*q^N/(2^m + q^N)`. Sampling the hidden secret and source errors cannot add a
selector failure, because the selector reads only the public challenge masks.

For centered-binomial source errors of width `eta` and certified discrete-Gaussian widening, the
complete finite-game theorem is therefore

```text
Adv_RGSW(-S)
  ≤ L*q^N/(2^m + q^N)
    + L*N*scalarLinearShiftBound(certificate, N²*(m+1)*B_s*eta)
    + Adv_batch-RLWE(narrow source error).
```

Pointwise completeness is stronger than security needs. The finite development now also accepts
an arbitrary public bit-selector and charges its actual failure probability on the uniform public
mask matrix:

```text
Adv_RGSW(-S)
  ≤ Pr[the selector misses at least one gadget target]
    + L*N*scalarLinearShiftBound(certificate, N²*(m+1)*B_s*eta)
    + Adv_batch-RLWE(narrow source error).
```

Thus a future algorithm may fail on some solvable instances; it only needs negligible failure on
the random instances generated by the reduction. The complete-selector counting theorem remains
useful for proving that the chosen parameter regime contains enough preimages, but it is not part
of the computational requirement.

The asymptotic accounting is also checked. Taking `m = kN + lambda` when `q = 2^k` makes the
selector-failure term negligible for polynomially many levels. If the layout and induced-shift
budgets grow polynomially, the finite sampler-certificate error is negligible, and the certified
Gaussian standard deviation is at least `2^lambda`, then the smudging term is negligible as well.
Under those explicit schedules, ordinary batch-RLWE security proves asymptotic `RGSW_S(-S)`
security as soon as the selector has negligible random-instance failure and its use in the
reduction is polynomial time. This condition is packaged as the named
`EfficientAnchoredBinaryISIS` interface, and the final average-case theorem combines exactly that
interface, Gaussian smudging, and ordinary batch-RLWE security.

For a fixed power-of-two modulus, this search problem now has a checked construction. Write
`q = 2^(d+1)` and use rank slack `lambda`. At one layer, the selector uses `N + lambda` masks as a
binary parity-solving prefix. Each further recursive mask is made from a disjoint block of `N+1`
upper masks: the corresponding `N`-by-`N+1` binary matrix has a nonzero kernel vector, so that
selected block sum is even and may be divided by two. The construction then recurses modulo the
next lower power of two. Its non-anchor source count is

```text
c(0)   = N + lambda
c(j+1) = N + lambda + (N+1)c(j).
```

The formal probability proof is conditional neither on Ring-SIS nor on a random-oracle heuristic.
Conditioned on all previously exposed parities, every compressed lower table is proved exactly
uniform. A rectangular binary-rank bound at each layer and a union bound therefore give

```text
Pr[one RGSW level fails] ≤ (d+1) * 2 / 2^(lambda+1),
Pr[one of L levels fails] ≤ L * (d+1) * 2 / 2^(lambda+1).
```

The production anchoring is exact: mask zero receives coefficient one, and the recursive selector
on the tail targets `g_level - a_0`. Taking coefficients is proved to preserve the native
negacyclic mask combination. Substituting this selector into the genuine finite RGSW reduction
replaces the former abstract failure term by the displayed rank bound. With `m = c(d)`, the checked
finite result is

```text
Adv_RGSW(-S)
  ≤ L*(d+1)*2/2^(lambda+1)
    + L*N*scalarLinearShiftBound(certificate, N²*(m+1)*B_s*eta)
    + Adv_batch-RLWE(narrow source error).
```

For fixed `d`, `c(d)` is bounded by
`(d+1)(N+lambda)(N+1)^d`; hence polynomial ring-degree growth and polynomially many gadget levels
give polynomial source count and negligible selector failure. The corresponding asymptotic
standalone `RGSW_S(-S)` theorem now assumes only the checked Gaussian-smudging conditions,
ordinary batch-RLWE security, and preservation of the chosen PPT classes by the concrete lifting
compiler. It does not assume average-case anchored binary Ring-SIS.

One formal implementation boundary remains. The current Lean selector obtains full-rank solutions
and nonzero kernel vectors by classical finite choice. Replacing those two choices by executable
binary Gaussian elimination and certifying the recursive routine's polynomial running time is
still required before claiming a fully mechanized PPT reduction. This is substantially narrower
than the former average-case Ring-SIS assumption: all algebra, exact distribution preservation,
failure probability, production anchoring, and the finite/asymptotic security composition are
already proved. The fixed-depth construction also does not settle growing modulus exponent:
the displayed recurrence behaves like `(N+1)^d`, so a growing `d` needs a more source-efficient
lifting construction. Finally, the widening-noise schedule must still be made compatible with the
desired TFHE correctness parameters; this section proves security, not correctness.

The compiler analysis has also been strengthened so that it no longer reveals the source errors
when applying the statistical hybrid. The selector is a function only of the public source masks,
so the source challenge is now factored into a mask/secret prefix followed by an independent error
table. For every successful prefix, Lean proves the exact residual identity

```text
residual_l = S * sum_i x_(l,i)(masks) * e_(l,i).
```

The errors on the right remain hidden and random. Consequently the finite theorem does not need
the former worst-case translation cost. It charges the exact mixed distance

```text
TV(residualVector + targetErrorVector, targetErrorVector).
```

When the target error is `centeredBinomial + wideningGaussian`, adding the same independent
centered-binomial vector to both sides is a total-variation contraction. The checked production
endpoint therefore has the cleaner form

```text
Adv_RGSW(-S)
  <= L*(d+1)*2/2^(lambda+1)
     + TV(residualVector + wideningGaussianVector,
          wideningGaussianVector)
     + Adv_batch-RLWE(centered-binomial source error).
```

This is strictly sharper than replacing the hidden residual by its maximum possible norm: it
retains cancellation among the independent centered-binomial source errors and among the selected
rows. It is not, by itself, the desired small-noise theorem. The remaining analytic problem is to
bound this exact random-convolution distance negligibly while keeping the widening noise below the
TFHE decryption margin. Independently, a growing modulus exponent still needs a source-efficient
selector, and the fixed-depth selector still needs executable binary Gaussian elimination for a
completely certified PPT reduction.

For that analytic step the formal endpoint also exposes two standard finite second-moment forms.
An unconditional `L2Loss` is an explicit sum of squared point-mass differences and remains valid
even when a compiled Gaussian ticket table has support holes. A sharper Pearson chi-square form is
available when the mixed law is absolutely continuous with respect to the widening law. The
production theorem can consume a uniform bound on the unconditional `L2Loss` directly. These are
checked reductions of the statistical goal, not an assertion that either finite sum is already
negligible.

There is now a converse for the no-wrap small-noise regime. For any upper row and any centered
real lift, suppose the projected residual `R` and target error `E` have mean zero, the lift obeys
`lift(R+E) = lift(R)+lift(E)` on their joint support, and both `E` and `R+E` lie in the same
interval `[-B,B]`. A clipped-square statistical test gives the checked lower bound

```text
E[lift(R)^2] / (2*B^2)
  <= TV(residualVector + targetErrorVector, targetErrorVector).
```

The production binary selector now has a sharper checked normal form. It reserves source row zero
with coefficient one, so every upper residual is pointwise

```text
S * (e_0 + sum_i b_i*e_(i+1)).
```

The anchor `S*e_0` and selected tail are independent. A generic finite moment theorem proves that
a centered IID weighted sum has second moment equal to the scalar second moment times the sum of
squared weights. For the executable centered-binomial sampler, a no-wrap coefficient has exact
second moment `eta/2`. Consequently, for every nonzero binary `S`, every coefficient of `S*e_0`
has exact moment `(eta/2) * HammingWeight(S)` and hence at least `eta/2`, assuming
`2*eta < q` and `2*N*eta < q`. Adding the centered independent selector tail cannot decrease it.
The complete compiler therefore satisfies the selector-independent lower bound

```text
eta / (4*B^2)
  <= TV(residualVector + targetErrorVector, targetErrorVector)
```

under the displayed centered-support and no-wrap hypotheses. Thus positive centered-binomial
width and a polynomial correctness bound cannot make this particular statistical hop negligible,
regardless of the source-pool size or selector success probability. This is not a universal
insecurity theorem for native `RGSW_S(-S)`: deliberate modular wrap, a computational hybrid that
retains the source-sample/error correlation, or a different native reduction remains possible.

There is now an exact native external-product alternative to statistical absorption. Let `z` be
the public weighted source row used by the compiler. The compiled square row has phase

```text
g*S^2 + e_target + S*phase(z).
```

Externally multiplying `z` by a TGSW control whose intended message is `-S` and adding the result
gives the checked identity

```text
phase(cancelledRow)
  = g*S^2 + e_target + externalProductError(control, digits(z)).
```

Thus the complete `S*phase(z)` term cancels algebraically rather than being hidden by fresh noise.
For every fixed source context, digit table, and control ciphertext, the map from the independent
target row to the cancelled row is bijective, so the uniform target endpoint remains exactly
uniform. With executable base digits, the replacement residual also has the checked rank-one
coefficient bound

```text
B_target + 2*levels*N*(base-1)*B_control.
```

It is independent of the selector-weighted source-error magnitude, so this genuinely bypasses the
moment obstruction at the phase and narrow-noise levels.

The generic upper/lower split now determines whether a different digit representation can turn
this into a fixed-point reduction. For every exact decomposition of `z`, its upper digits recompose
`z.mask = g`. Consequently the upper control-row combination necessarily has phase

```text
phase(upperExternalProduct) = g*S^2 + upperErrorProduct.
```

The complete ciphertext and error split gives

```text
cancelledRow = upperExternalProduct + genericRerandomizationDifference,
phase(genericRerandomizationDifference) = e_target + lowerErrorProduct,
genericRerandomizationDifference = compiledSquareRow + lowerExternalProduct.
```

The right-hand side of the last equality contains no upper control entry. Thus every exact digit
representation retains a square-carrying upper-row combination; changing digits can redistribute
the square among upper rows but cannot move it into the zero-message remainder.

The concrete target-level decomposition sharpens this invariant. Its mask digit is one-hot at the
selected gadget level, while its body uses the ordinary ring digits of `z.body`. Consequently

```text
externalProduct(targetLevelDigits(z), control)
  = selectedUpperControlRow + lowerExternalProduct(z.body, control).
```

The error split retains the selected upper-row error with coefficient one. More strongly, the
cancelled row has the checked normal form

```text
cancelledRow = selectedUpperControlRow + rerandomizationDifference,
phase(rerandomizationDifference) = e_target + lowerRowErrorProduct,
rerandomizationDifference = compiledSquareRow + lowerExternalProduct.
```

Thus, in the canonical specialization, the output contains the original circular upper row
verbatim. In the general case it contains a public linear combination with the same square message.
This rules out the hoped-for self-elimination throughout the exact-decomposition route: the
external-product construction rerandomizes or recombines the square challenge; it does not
construct or remove it from ordinary RLWE. Any distributional use of the zero-message remainder
must still relate its widened error law to the native small-error law, while exposing that remainder
makes the transformation invertible. A genuine proof therefore needs a different computational
hybrid for the retained square row.

This also explains precisely what the Brakerski--Vaikuntanathan polynomial-KDM construction buys,
and that comparison is now formal. Two ordinary rank-one RLWE samples sharing `S` are mapped to

```text
(a1*S + e1, a2*S + e2 - a1, -a2 + g).
```

Evaluation at `(1,S,S^2)` is exactly `g*S^2 + e1 + e2*S`. Retaining `a1` as one unused fiber
coordinate makes the public telescope a bijection, so a uniform two-sample transcript maps exactly
to a uniform three-component ciphertext. The familiar presentation with `g*S^2` visibly added to
the first component is proved distributionally identical by the secret-dependent uniform-mask
translation `(a1,a2) -> (a1+g*S,a2+g)`. Consequently its quadratic-KDM advantage is exactly a
two-sample ordinary-RLWE advantage, with no hybrid loss or error widening.

The theorem also holds jointly over every gadget level under one shared secret. The complete direct
BV gadget batch is exactly reducible to `2*levels` ordinary RLWE samples. Adding one ordinary lower
zero row per level gives a source view that is an exact public image of `3*levels` ordinary samples.
The real upper phases are `g_l*S^2 + e_(l,1) + S*e_(l,2)`, the lower phases are their original
narrow errors, and an explicit retained-fiber bijection proves that the complete source view is
uniform in the ordinary uniform branch.

What remains is therefore a sharply typed native-compression problem, not quadratic KDM security
for the three-component construction. An `ExactNativeCompression` witness must map the joint BV
upper/ordinary-lower real law to fresh native two-component narrow-error square/zero rows and map
the uniform source carrier to the uniform native carrier. Such a witness gives a lossless native
square-security reduction to `3*levels` ordinary RLWE samples. Without exact realization, the
checked quantitative theorem adds only the literal total-variation distance between the compressed
source law and the native law. No witness or negligible distance is claimed.

The obvious candidate cannot supply it: interpreting `(c0,c1)` as a native row and deleting `c2`
removes exactly `c2*S^2` from the phase. On the telescope distribution, the resulting square
coefficient is the uniform second mask `a2`, not the gadget `g`; the residual is exactly
`(a2-g)*S^2`. Thus BV proves that retaining the third component is sufficient, while the native
`RGSW_S(-S)` research question is precisely whether a different public computational compression
can remove it without destroying the small-noise joint distribution.

### Highest two-adic native row

There is one exact native simplification that does not use the BV extra component. Let
`q = 2^(k+1)` and let the gadget weight be `h = 2^k`. For a Boolean-coefficient polynomial
`S = sum_i s_i X^i`, the checked executable-ring identity is

```text
h*S^2 = sum_i s_i * h*X^(2i).
```

Indeed, every cross term occurs with coefficient two and `2h=0 mod q`, while `s_i^2=s_i`.
Consequently the highest-weight upper square row is a fixed coefficient-linear function of the
binary secret vector. The complete one-level stripped native object, consisting of this upper row
and its lower zero row, is exactly the corresponding coefficient-affine circular-RLWE problem.
Its public challenge, binary-secret sampler, narrow error sampler, and uniform endpoint are
literally the ordinary binary-secret RLWE samplers; only the noiseless map contains the named
coefficient operator. There is no noise growth in this normalization.

This does not collapse the row to ordinary rank-one RLWE. In ring degree at least two, evaluating
the map on the Boolean basis polynomials `1` and `X` proves that no fixed public multiplier `C`
can satisfy `h*S^2 = S*C` for every Boolean `S`: the first input forces `C=h`, while the second
would require `h*X^2=h*X`, which the checked coefficient calculation refutes. Thus the usual
public challenge translation for ring-linear messages is unavailable. The result narrows the
first native subproblem to coefficient-affine circular RLWE at the highest two-adic layer; proving
that endpoint computationally, and then treating the lower gadget weights where cross terms
survive, are the next research steps.

The algebraic endpoint is now connected to the genuine native security games as well. Applying
the coefficient equivalence to the full upper-square/lower-zero transcript gives exactly the
named coefficient-affine real distribution, and it maps the uniform transcript to the uniform
endpoint. The checked strip/restore permutation therefore gives, for every native distinguisher,
an exact equality between its real-versus-uniform top-row advantage and the corresponding
coefficient-affine advantage. Independently, the zero-message one-level RGSW game is exactly an
ordinary rank-one binary-secret RLWE problem with two rows. The resulting pointwise bound is

```text
Adv_KDM(RGSW_S(-S), top weight)
  <= Adv_coefficient-affine-top + Adv_binary-secret-RLWE(2 rows).
```

This reduction preserves the supplied narrow error sampler literally. In particular, its
centered-binomial specialization uses the same `eta` in the coefficient-affine premise, the
ordinary RLWE premise, and the native KDM conclusion. There is no smudging, error convolution, or
statistical comparison term. The cryptographic research question has consequently been reduced
to a single explicit premise for the nonzero top row: prove the hardness of the doubling-map
coefficient-affine circular-RLWE problem from a more standard foundation. The theorem does not
silently label that premise ordinary RLWE; the fixed-ring-multiplier obstruction above explains
why such a label would be unjustified.

The coefficient-extraction boundary can now be stated exactly. For any selected output
coefficient, the corresponding negacyclic product coefficient is a scalar dot product against a
signed permutation of the complete public ring mask. That permutation is an involution, so a
uniform ring mask gives a uniform scalar-LWE mask. Projecting the real and uniform top-row games
onto any one body coefficient therefore gives exactly direct affine circular LWE, and the checked
affine challenge translation reduces its advantage losslessly to ordinary binary-secret scalar
LWE. The selected ring-error coefficient is unchanged; for centered-binomial error it has the
one-coefficient centered-binomial law with the same `eta`.

This positive statement is only marginal. If every output coefficient is extracted from the same
ring mask, the resulting scalar challenge columns are not independent: every diagonal entry of
their challenge matrix is the constant coefficient of that one mask. In degree at least two the
checked common-mask map is consequently not surjective onto the full scalar-LWE matrix space.
Thus a coefficient-by-coefficient hybrid cannot simply replace the columns by independent LWE
samples. The remaining top-row research problem is now more specific: prove that this shared
negacyclic-mask coupling remains secure in the presence of the doubling-map affine message, or
give a public compiler that removes the coupling while preserving the complete narrow-noise real
and uniform laws.

There is now also an exact joint reformulation that preserves this coupling. Reveal the complete
value `L(S)=2^kS^2`, subtract it from the upper ciphertext body, and leave the lower row unchanged.
The resulting real transcript is ordinary two-row binary-secret RLWE with the original shared
negacyclic masks and the original narrow errors. Adding `L(S)` back is a body translation and
therefore a permutation of the complete uniform transcript. Consequently the genuine unstripped
top-row circular advantage is exactly an ordinary-RLWE advantage with structured auxiliary
leakage. This endpoint contains no circular ciphertext: its conditional real and zero samplers
are definitionally identical. It is a leakage-resilient RLWE problem, not an assertion that
ordinary RLWE automatically tolerates the leakage.

For the power-of-two cyclotomic dimensions used by TFHE, the leakage itself has an exact simpler
form. Write the even ring dimension as `N=2M`. Since `X^N=-1`, the squared basis monomials at
indices `i` and `i+M` are negatives. Multiplication by the top weight `2^k` identifies those signs
modulo `2^(k+1)`, and the checked identity becomes

```text
2^k*S^2 = sum_(i<M) (s_i xor s_(i+M)) * 2^k*X^(2i).
```

The formal result is exact in both directions. Splitting a secret into its pair-XOR vector and
its first half is an equivalence; the pair-XOR vector is uniformly distributed, and every fixed
value has exactly `2^M` compatible secrets. Conversely, the even output coefficients of the
leaked ring element recover all `M` XOR bits, so the ring value exposes exactly this quotient and
no further secret information. The resulting native security statement is

```text
Adv_KDM(RGSW_S(-S), top weight, N=2M)
  <= Adv_RLWE[reveal (s_i xor s_(i+M))_(i<M)]
     + Adv_binary-secret-RLWE(2 rows).
```

All games use the same narrow error sampler; the centered-binomial specialization keeps the same
`eta`. The standalone research question is therefore sharply stated: prove narrow-noise RLWE
pseudorandomness conditioned on this uniform half-dimensional XOR quotient, or find a reduction
that exploits the affine fiber `s_(i+M)=s_i xor y_i`. This is substantially more specific than
assuming circular security of an RGSW ciphertext, but it is not yet a proof from standard RLWE.

There is also an exact additive secret randomization that is special to this `-S` message
relation and does not widen or shear the error. Write one stripped upper row as

```text
b = a*S + g*S^2 + e.
```

For any public ring element `r`, define

```text
a' = a - 2*g*r,
b' = b + a*r - g*r^2.
```

Then, identically in the coefficient ring,

```text
b' = a'*(S+r) + g*(S+r)^2 + e.
```

For a lower zero row the corresponding map is `a'=a`, `b'=b+a*r`, which again retains `e`
exactly. Lean proves the batch identity, proves that negating `r` is the inverse public map, and
therefore proves exact preservation of uniform challenges and uniform complete ciphertexts.
Conjugating by the checked strip/restore maps gives the genuine-layout law

```text
publicShift_r(RGSW_S(-S)) =dist RGSW_(S+r)(-(S+r))
```

for the same arbitrary narrow error sampler. Sampling `r` uniformly makes `S+r` exactly uniform,
so a fixed-secret or binary-secret challenge can be self-randomized to the uniform-ring-secret
challenge without statistical loss.

This identity is not yet a security reduction in the direction needed to finish the theorem. A
distinguisher for the uniform-secret distribution can be pulled back through the randomization to
one for the source-secret distribution, but an arbitrary distinguisher for the original binary-
secret distribution cannot be pushed to a uniform-secret challenge without knowing that hidden
secret. Thus the result is an exact search-to-decision/self-reducibility tool and a sharper
description of the core problem, not a claim that uniform-secret ring-square security implies the
desired binary-secret circular security. The sample-extracted recovery route below now supplies
the exact guess/check layer. For the anchored centered-binomial compiler, direct statistical
absorption of the hidden-residual convolution is now ruled out in the no-wrap small-noise regime;
eliminating the circular premise therefore requires a computational treatment of the correlated
source samples and residual, or a genuinely different native reduction.

The complete PKC-style pair is checked as well. Ordinary zero-message RLWE test rows use the
usual public body correction `b' = b + a*r`, which transports them from `S` to `S+r` with the
same test errors. The formal joint-view map consequently satisfies both exact branch laws

```text
(RGSW_S(-S), RLWE_S(0))  -> (RGSW_(S+r)(-(S+r)), RLWE_(S+r)(0)),
(RGSW_S(-S), Uniform)    -> (RGSW_(S+r)(-(S+r)), Uniform).
```

Both are packaged as zero-loss instances of the generic auxiliary-input `ViewRandomization`
interface. This is the restricted ring-square counterpart of the secret-randomization lemma used
in the PKC 2024 search-to-decision proof, but here it preserves the original narrow noise exactly:
there is no homomorphic shifted-function evaluation and no flooding factor. The sample-extracted
construction below completes the ring-secret guess/check algebra. The remaining hardness source
for the circular search problem is not implied merely by ordinary search RLWE because the search
solver receives the real `RGSW_S(-S)` auxiliary object.

The evident ring candidate test can now be stated exactly. Given a zero-message test row

```text
b = a*S + e
```

and a public candidate `V`, sample a fresh uniform `u` and publish

```text
a' = a + u,
b' = b + u*V.
```

Its phase under `S` is exactly `e + u*(V-S)`. If `V=S`, the output is a fresh real RLWE row
with the identical narrow error. If `V-S` is a unit, Lean constructs the inverse map from the
output row back to `(a,u)`; therefore the output is exactly uniform, even after conditioning on
an arbitrary error vector. Applying this test to all ordinary rows and then applying the exact
RGSW key shift proves the complete two branches jointly with the randomized hidden secret:

```text
V = S             -> uniform-secret (RGSW_T(-T), RLWE_T(0)),
IsUnit(V-S)       -> uniform-secret (RGSW_T(-T), Uniform).
```

No error widening or modular-Gaussian estimate enters either equality. This supplies the missing
guess/check algebra for any secret space whose distinct candidates always have unit difference.
It does not supply that property for TFHE's binary-polynomial secret space. In the production
power-of-two negacyclic ring, unit status is determined by the `ZMod 2` residue. Consequently,
every pairwise unit-separated candidate family injects into `ZMod 2` and has at most two members.
This is a cardinal obstruction to using the direct test over all `2^N` binary polynomials. It is
also important not to overread the result: selecting two residue representatives does not recover
the parity of an arbitrary ring secret, because the real branch requires literal equality `V=S`,
not merely equal residue. The sample-extraction construction below supplies coefficient tests in
a larger scalar representation; the direct ring-candidate route itself remains limited to two
candidates.

The most direct coefficient action is now ruled out exactly. To imitate the vector-LWE test for
one coefficient, let `M(S)` be the ring polynomial containing that selected Boolean coefficient,
choose a uniform ring pad `u`, add `u*V` to the body, and add some public `L(u)` to the ring mask.
The correct branch would require

```text
S * L(u) = u * M(S)
```

for all binary `S` and all `u`. The formal obstruction permits an arbitrary function `L`; it
does not assume linearity. Evaluating the required identity at `u=1` gives
`M(S)=S*L(1)`, so `M` must be multiplication by one fixed ring element. The previously checked
coefficient-affine theorem proves that even the first coefficient projector is not such a ring
multiplication in degree at least two. The same no-go result is instantiated for the actual first
native diagonal-cross message. Thus the exact vector-LWE coordinate perturbation is unavailable
in rank-one RLWE for structural reasons, not because the right formula has merely not been found.
Approximate noise-changing actions, multi-component challenge representations, and reductions
using a different ring/modulus remain outside this obstruction and are the constructive options
left on the search-to-decision route.

There is, however, an exact way to obtain the needed larger representation from the ordinary
rank-one test rows themselves. TFHE sample extraction sends each positive-degree row

```text
b = a*S + e
```

to one scalar-LWE row under the full coefficient vector `KeyExtract(S)`. The checked challenge
map is an equivalence, its error is exactly the constant coefficient of `e`, and it maps a
uniform ring transcript to a uniform scalar transcript. Applying this deterministic map only to
the ordinary test component while retaining the genuine `RGSW_S(-S)` auxiliary gives the exact
paired-view identities

```text
(RGSW_S(-S), rank-one RLWE_S(0)) -> (RGSW_S(-S), scalar LWE_KeyExtract(S)(0)),
(RGSW_S(-S), uniform ring rows)  -> (RGSW_S(-S), uniform scalar rows).
```

The ordinary binary coordinate transform is now available on the scalar challenge matrix. For
any selected coefficient, adding a fresh vector to that challenge row and the candidate bit times
the vector to all bodies has two exact branches at the original narrow noise law:

```text
candidate = hidden coefficient  -> real extracted view,
candidate != hidden coefficient -> uniform scalar-test view.
```

After averaging over a uniform binary ring secret, Lean proves that the oriented candidate gap
equals the original real-versus-uniform-test decision advantage. Each coefficient is recovered
with probability `(1 + advantage)/2`; running all one-shot tests and applying `KeyUnextract`
recovers the complete ring-key shape with the explicit lower bound

```text
1 - sum_i ofReal((1 - advantage)/2).
```

This resolves the coefficient guess/check algebra and explains precisely how sample extraction
bypasses the direct ring-action no-go theorem: the public test representation now has one scalar
challenge row per secret coefficient. It is not yet a proof of standalone security from ordinary
RLWE. Both decision endpoints, and hence the resulting search problem, retain the genuine
`RGSW_S(-S)` auxiliary. An ordinary search-RLWE solver cannot simulate that auxiliary without
already knowing `S`. Removing this residual circular-search premise is now the central problem;
the one-shot whole-key bound also needs a fresh-view or support-wise gap argument to amplify a
merely inverse-polynomial averaged decision advantage.

## Shared-randomness one-cycle variant

The shared-randomness construction of ePrint 2023/979 suggests a useful change of key geometry.
For a rank-one ring key whose extracted coefficient vector has length `n + r`, choose one uniform
master secret and define

```text
master ring key u = prefix p || suffix z
scalar TLWE key   = p
suffix KSK        = encrypt only z under p
BRK               = encrypt each bit of p under u
```

The checked split equivalence proves that a uniform `u` induces exactly independent uniform
`(p,z)`. Consequently, the suffix KSK contains no encryption of a coordinate already present in
the target scalar key. Its complete correlated batch is exactly the generic affine shared-IKSK
problem and has exactly the advantage of one ordinary binary-secret LWE problem. This removes the
second edge of the original heterogeneous cycle without pretending that the KSK and BRK were
sampled independently.

What remains is one-key native TRGSW circularity. After direct-phase normalization, a mask-block
coordinate contains a self-product of two master-key bits. Boolean idempotence makes the diagonal
case `u_i * u_i = u_i` affine. For distinct coordinates, the formal theorem
`offDiagonalBinarySelfProduct_not_affine` rules out every affine representation in the complete
binary master key whenever the selected gadget value is nonzero. Thus nesting the keys reduces a
two-key cycle to one self-cycle, but it does not turn standard narrow-noise TFHE into an affine-KDM
instance or prove it from ordinary RLWE.

There is an unconditional information-theoretic security endpoint for the one-cycle variant.
With uniform ring-row error, every native TGSW encryption of every fixed message is exactly
uniform. Real and zero-message BRKs therefore have identical laws while retaining the same master
secret and the exact correlated real suffix KSK. The contextual theorem is deliberately stronger
than a cloud-key distinguisher: the common continuation receives the master secret, BRK, and KSK,
so it may generate later challenge ciphertexts or invoke any encryption/evaluation experiment.
Its circular advantage is exactly zero.

For an arbitrary finite executable ring-error sampler `D`, sampler replacement gives the concrete
bound

```text
contextual one-cycle advantage
  <= 2 * (n * TGSW.rowCount 1 levels) * TV(D, Uniform).
```

The factor two pays the real-to-uniform and uniform-to-zero sides; no loss is charged for the
master-secret mixture, the retained KSK, or downstream computation. A centered-binomial or finite
discrete-Gaussian sampler can instantiate this theorem after proving its one-draw distance from
uniform.

The contextual theorem is now instantiated by the concrete one-time left-or-right TFHE
encryption game. For confidentiality there is no need to return from the uniform BRK to an actual
zero-message BRK, so only one sampler-replacement side is paid. Once the BRK is uniform and
independent, the master-key split exposes an independent suffix message key and prefix encryption
key. The entire suffix KSK and the adaptively selected input ciphertext are represented by one
unequal two-block binary-secret LWE transcript. Its uniform branch is proved exactly fair even
after the KSK block is translated by the suffix gadget messages. Consequently,

```text
one-time shared-key TFHE IND advantage
  <= (n * TGSW.rowCount 1 levels) * TV(D, Uniform)
     + Adv_two-block-LWE(suffixRows, oneInputRow).
```

When the KSK and input errors have the same distribution, the final term is exactly conventional
binary-secret batch LWE on `suffixRows + 1` samples. This is an end-to-end confidentiality theorem
for the modified shared-randomness key layout, rather than only a cloud-key replacement statement.

The same argument is checked for reusable-key adaptive encryption. A sequential adversary sees
one shared cloud key, reuses one hidden challenge bit, and may choose each later message pair from
earlier ciphertexts. A public query bound justifies replacing online input sampling by an eager
tape of exactly `queryCount` rows. At the uniform endpoint the complete KSK block and tape are one
two-block LWE transcript, and the online uniform ciphertext oracle is proved independent of the
hidden bit. Therefore the adaptive bound is

```text
adaptive shared-key TFHE IND advantage
  <= BRKrowCount * TV(D, Uniform)
     + Adv_two-block-LWE(suffixRows, queryCount).
```

With equal scalar noises this is ordinary binary-secret batch LWE on
`suffixRows + queryCount` samples. Since public homomorphic evaluation is deterministic from the
cloud key and ciphertext, the existing query-bound-preserving public-evaluation compiler applies
to this adversary type without another cryptographic term.

### Corrected nested ring-key BRK conversion

The shared-randomness construction requested here uses two ring keys, not merely a scalar prefix
of one rank-one ring key. Write

```text
S_target = S_source || S_suffix.
```

The BRK plaintext vector is held fixed while its ring encryption key is changed:

```text
BRK(messages, S_source)
  -> derived BRK(messages, S_target).
```

For an individual TLWE/GLWE row, this conversion is exact and public: append zero mask
coordinates. Its phase under `S_target` is definitionally the original phase under `S_source`.
A full native TGSW layout has an additional issue: enlarging the target key introduces one gadget
block for every coordinate of `S_suffix`. Those rows cannot be filled by zero padding. At suffix
coordinate `j` and level `l`, the required phase is

```text
-(S_suffix[j] * (message * gadget[l])).
```

The checked converter obtains that row by externally multiplying the source TGSW encryption of
`message` with the suffix-only ring-KSK row encrypting
`S_suffix[j] * gadget[l]`, negating the result, and then appending zero masks. With exact gadget
decomposition, the new row error is exactly

```text
-message * KSKRowError[j,l] - ExternalProductError[j,l].
```

The prefix gadget rows and the final body block preserve their source row errors exactly. Thus the
complete derived object has the target TGSW phase semantics, with every new residual exposed.

The security transfer is pure data processing. For the real and zero-message source views,

```text
TV(derived target real view, derived target zero view)
  <= TV(source real BRK + shared KSK, source zero BRK + shared KSK).
```

Consequently the conversion introduces no target-key circular assumption. For the full-key
instantiation requested here, the fixed message vector is `KeyExtract(S_target)` on both sides.
Because `S_source` is literally a prefix of `S_target`, the source view already contains the sole
secret-key cycle. This proves the intended reduction from the target self-BRK to a source-key
one-cycle experiment; it does not yet prove that source experiment from ordinary RLWE.

The checked continuation form permits any common randomized evaluator or distinguisher to consume
the derived target view. Its output distance obeys the same source-view bound, so subsequent FHE
evaluation does not add a separate circular-security term.

The word `derived` is essential. The converted target rows are evaluated ciphertexts whose errors
and masks are correlated through the source BRK and KSK. No equality with a freshly sampled native
`BRK(messages,S_target)` is claimed. Such an equality would need a separate rerandomization or
smoothing theorem. The older coefficient-nesting construction described below is still a valid
conditional model, but it is not this source-ring-to-target-ring conversion.

There is also a ciphertext-format boundary. The completion rows use a ring-valued KSK under
`S_source`, because they are inputs to a TGSW external product. The standard TFHE KSK instead
contains scalar TLWE rows under `KeyExtract(S_source)`. These types are not interchangeable.
Obtaining the converter from only the standard scalar KSK would require an additional checked
LWE-to-GLWE packing or inverse-sample-extraction construction. Without it, the present arrow is a
precise modified evaluation-key design rather than a theorem about the unmodified TFHE cloud key.

### Full-target-message adaptive TFHE security game

The fixed-message instantiation is now explicit. With

```text
S_target = S_source || S_suffix,
s_target = KeyExtract(S_target),
```

key generation constructs

```text
source BRK:   BRK(s_target, S_source)
derived BRK:  BRK(s_target, S_target).
```

Coefficient-level theorems prove that the extracted source key is literally the prefix of
`s_target` and that its remaining coordinates are exactly the extracted suffix key. Thus the
message vector does not change during conversion. The source BRK contains the source encryption
key among its messages, while the other messages come from the independent suffix; the only
directed key cycle is already present at the source boundary.

The final cloud key contains the derived BRK. Because the input scalar key is `s_target`, sample
extraction under `S_target` returns a ciphertext under that same scalar key, so this full-key
variant has no scalar shrinking KSK. The ring-valued extension key is consumed while deriving the
BRK.

For every secret-dependent continuation, the target replacement distance is exactly the source
experiment

```text
BRK(KeyExtract(S_target), S_source)
  versus
BRK(0, S_source),
```

with the suffix and ring-extension key retained as correlated auxiliary input. The adaptive IND
bound has this single source-cycle term plus the explicit zero-BRK endpoint. Public evaluation
adds no term. Uniform source-BRK errors erase the circular term and uniform fresh-input errors make
the endpoint perfectly fair, yielding exact zero adaptive and evaluated advantage for arbitrary
extension errors. This proves confidentiality, not correctness.

The combined source term is now split once more through the exact suffix-only message vector

```text
suffix-only messages = 0_source || KeyExtract(S_suffix).
```

The first hop replaces only `KeyExtract(S_source)` while retaining the suffix messages and ring
extension material. This is the genuine self-key circular term. The second hop replaces the
independent suffix messages by zero after all source-key message coordinates are already zero, so
its dependency graph is acyclic. Lean proves the contextual and adaptive inequalities

```text
source target-message term
  <= source-prefix circular term + independent-suffix term,

|adaptive IND advantage|
  <= source-prefix circular term
     + independent-suffix term
     + |zero-BRK endpoint advantage|.
```

The same three-term statement holds after arbitrary public FHE evaluation. Discharging the
independent-suffix term for narrow noise is now exposed through an exact auxiliary-input problem.
Its real challenge is the suffix-only BRK, its zero challenge is the zero-message BRK, and both
branches retain the same ring-extension table. Lean proves both exact game identifications and

```text
independent-suffix term
  <= auxiliary real/uniform term + auxiliary zero/uniform term.
```

The adaptive and public-evaluation theorems first expand to four terms: the genuine circular
prefix term, the two acyclic auxiliary branches, and the zero-BRK endpoint. The positive-degree
adaptive reduction now closes the formerly missing input-tape step. It packages every suffix-only
BRK row, every ring-extension row, and every query-counted source-ring tape row into one blocked
module-LWE transcript under the same source ring secret. An independent suffix challenge completes
each tape row under `S_target`; sample extraction then gives exactly a scalar TLWE row under
`KeyExtract(S_target)`, with error equal to the constant-coefficient image of the ring error.
Exact fixed-secret real conversion, exact uniform conversion, and a common uniform endpoint prove

```text
independent-suffix adaptive term
  <= joint module-LWE advantage (suffix messages)
     + joint module-LWE advantage (zero messages).
```

Consequently, for one common BRK/extension/tape ring-error sampler, Lean proves the end-to-end
security boundary

```text
|adaptive TFHE IND advantage|
  <= native source-prefix CircRLWE/KDM advantage
     + two ordinary joint module-LWE advantages
     + |zero-BRK encryption endpoint advantage|.
```

The reductions receive neither nested secret. For narrow centered-binomial or discrete-Gaussian
errors, the only nonstandard hardness object in this decomposition is the source-prefix circular
term; the formalization does not rename it as ordinary RLWE or claim that nesting proves it.

A sharper public formulation now avoids both the suffix split and the zero-BRK endpoint. Its
challenge is the complete source BRK, while the real extension table and query-counted target-key
tape are auxiliary input:

```text
challenge:
  BRK(KeyExtract(S_target), S_source) versus UniformBRK

auxiliary:
  (Ext(S_suffix, S_source),
   TLWE_KeyExtract(S_target)(0)^queryCount).
```

The compiled distinguisher sees only this public view and derives the target-ring BRK by the
checked source-to-target conversion. After the circular BRK hop, one blocked module-RLWE
reduction independently resamples the already-uniform BRK and replaces the extension and tape
rows by a fully uniform view. Query boundedness makes that uniform-tape endpoint exactly fair.
The resulting strongest finite theorem is

```text
|adaptive TFHE IND advantage|
  <= public native target-message-BRK CircRLWE advantage
     + one ordinary joint module-RLWE advantage.
```

The first term is now normalized exactly inside this complete public game. Replacing the honest
BRK generator by the explicit degree-two monomial generator preserves the real-game distribution
after sampling the nested keys, correlated extension table, query tape, and arbitrary public
continuation; its uniform branch is definitionally unchanged. Hence Lean also proves

```text
|adaptive TFHE IND advantage|
  <= public degree-two monomial CircRLWE advantage
     + one ordinary joint module-RLWE advantage.
```

This removes an accounting and representation artifact, not the circular assumption: the first
term still contains the native source-bit/ring-bit products.

This monomial advantage is also proved exactly equal to the earlier PKC-style source-prefix
CircRLWE advantage instantiated with the adaptive-tape continuation. Because that continuation
uses the hidden key only to generate the public tape, this equality does not erase the tape from a
future search-to-decision proof. The matching exact recovery problem therefore gives its public
solver the complete `(BRK, extension, tape)` view. Its generic search bound retains the real
extension and tape at the uniform-BRK recovery endpoint rather than assuming that correlated side
information is harmless.

Same-distribution and narrow-search/widened-decision certificates are now wired to this exact
monomial problem. Supplying either certificate gives an end-to-end adaptive TFHE theorem whose
terms are complete-view nested-key recovery, the certificate's explicit shifted-evaluation,
smudging, guessing, and amplification loss, and one ordinary joint module-RLWE advantage. These
composition theorems do not manufacture the certificate; the native degree-two evaluator and its
quantitative loss remain the research step.

The two circular formulations now share the same honest recovery problem exactly. The public
reassociation

```text
(tape, (BRK, extension))  <->  (BRK, (extension, tape))
```

is a bijection, the independent samplers commute, and the honest native BRK has the explicit
monomial law. Lean lifts these facts through every recovery solver and proves equality of success
probabilities plus an iff for real-valued search hardness under the transported solver class. A
heterogeneous-layout reduction interface then lets the BRK-first adaptive theorem use the
existing tape-first nested-key recovery problem directly. The decision endpoints are intentionally
not identified: one uniformizes the BRK and the other uniformizes the tape. Consequently this
removes a duplicate search assumption, not the shifted-evaluation obligation.

This common-search chain is now lifted to the negligible-function security interface. Parameter
families retain separate narrow search noise and widened decision noise, polynomial query-count
witnesses, the exact nested source/target ranks, and the public gadget/decomposition maps. A
family-level reduction compiler produces the tape-first solver and exposes its complete loss as a
separate security game. Lean proves that negligible tape-first recovery, negligible compiler loss,
and ordinary blocked module-RLWE security imply negligible adaptive TFHE advantage. This is the
paper-aligned asymptotic conclusion once a native shifted evaluator has been supplied; it does not
postulate that evaluator or infer it from ordinary RLWE.

The ordinary module-LWE hop is essential rather than cosmetic.  The extension table has one
ring-valued row for each suffix *polynomial* and gadget level, with message
`S_suffix[j] * gadget[l]`; it does not have an independently editable row for every secret
coefficient.  A public negation can complement an entire polynomial by adding the public all-one
gadget row, but an arbitrary coefficientwise XOR mask would require a correction depending on the
hidden suffix polynomial.  Consequently, the simple exact scalar-key XOR transport cannot make
the suffix key fresh inside the native extension table.  Treating the suffix BRK rows, extension
rows, and input tape jointly as an ordinary module-LWE hybrid is the checked acyclic solution.

The source-prefix term is now packaged as the exact one-challenge auxiliary-input CircLWE game
suggested by the PKC 2024 framework. Its real branch is the complete target-message source BRK;
its reference branch zeros only the source-prefix messages while retaining the independent suffix
messages; its uniform branch has the same BRK carrier; and the real ring-extension table remains
correlated auxiliary input in every branch. The existing source-prefix advantage is definitionally
equal to this real/reference KDM advantage and is bounded by the real/uniform CircLWE advantage
plus the reference/uniform acyclic term. For a public FHE continuation, that reference term is
now bounded by two ordinary blocked module-RLWE advantages, so it is not a second circular
premise. For every fixed nested key, the real branch is also proved exactly equal in distribution
to the degree-two monomial presentation. The source
coordinates are same-key monomials, whereas the suffix coordinates involve an independently
sampled suffix coefficient. This is the strongest direct use of the supplied circular-security
references: their transformed KDM-secure constructions do not identify the native TFHE
distribution with ordinary RLWE.

The PKC 2024 result sharpens rather than removes this boundary. Its linear circular-LWE theorem
reduces gadget encryptions of the decomposed secret to ordinary decisional LWE (for its stated
power-of-two/discrete-Gaussian parameters). Its quadratic `circLWE` statement is explicitly a
conjecture; the proved search-to-decision theorem assumes search-circLWE and uses shifted
homomorphic evaluation plus Gaussian noise flooding. The paper also leaves adaptation to Ring-LWE
and ring-specific evaluation material open. Thus that technique supplies the right formal search
and randomization interface, but not a standard-RLWE proof of native TFHE's degree-two prefix
challenge.

The proved linear step now has a checked ring counterpart at every positive power-of-two modulus.
One hidden binary polynomial is used as the ordinary binary-secret RLWE key; independent higher
coefficient bit planes pack with it bijectively into a uniform element of the full negacyclic
ring. For any fixed batch of ring-linear functions of those planes, a triangular public map
subtracts the low-plane coefficient from each challenge, adds the known higher-plane key shift,
and inserts the remaining message. Lean proves that this map is a transcript permutation, maps
real samples exactly, preserves uniform samples exactly, and leaves the error vector unchanged.
The canonical specialization contains every powers-of-two gadget encryption of every bit plane
together with any desired number of zero-message rows. Its advantage is exactly one ordinary
binary-secret RLWE advantage; the algebraic step works for any finite error sampler.

This positive theorem deliberately stops at the same line as the paper's linear result. It does
not derive binary-secret RLWE from foundational ideal-lattice hardness, and it does not identify
the packed uniform ring key with TFHE's native binary ring key. Most importantly, a native TRGSW
mask-block message contains the product of a target scalar-key bit and a ring-key coefficient.
That degree-two term is not ring-linear in the packed bit planes, so the theorem does not discharge
the native source-prefix CircRLWE/KDM premise or the nonlinear shifted-view evaluator.

### Direct public FHE CircLWE statement

The BRK-replacement/KDM path above is a useful sufficient decomposition, but the circular
assumption used most directly in an FHE IND proof has the PKC public-information orientation. Lean
now also fixes that exact distribution. The nested secret is

```text
(S_source, S_suffix),     S_target = S_source || S_suffix,
```

the retained public information is

```text
Pub(S_source, S_suffix)
  = (BRK(KeyExtract(S_target), S_source), Ext(S_suffix, S_source)),
```

and the decision challenge is

```text
TLWE_KeyExtract(S_target)(0)^queryCount
  versus
UniformTape.
```

The extension table deterministically converts the source BRK to the derived target BRK used by
the adversary. The compiled decision distinguisher receives only `(tape, BRK, extension)`, not
either secret. Lean proves exact real-game and uniform-game identities. The uniform tape remains
perfectly fair even in the presence of the complete real circular evaluation key, so every
query-bounded adversary satisfies

```text
|honest adaptive TFHE IND advantage|
  = direct public auxiliary-input CircLWE advantage.
```

This is the real FHE circular-security statement; it does not require first replacing the BRK by
zero. It is complementary to the stronger prefix-KDM-plus-two-module-LWE decomposition.

The PKC randomization program is specialized to this corrected nested-key view. Independent
coefficientwise XOR masks send every fixed `(S_source,S_suffix)` to an exactly fresh pair. A
`ShiftedViewEvaluator` certificate must then publicly transform the complete narrow
`(tape, BRK, extension)` view to the widened view for the masked pair. Its pointwise TV error is
proved to be paid only once after the full mask is sampled. The associated exact-recovery search
problem asks for both nested key blocks. Same-distribution and cross-distribution theorems show

```text
TFHE advantage
  <= narrow exact-recovery success + shifted/guess-and-check loss.
```

This cleanly isolates what the PKC paper does and does not provide. Its secret-randomization idea
is valid here, but constructing the native ring-specific shifted evaluator remains the research
obligation.  The candidate-dependent one-coordinate guess-and-check implication is instantiated
below, conditional on that evaluator.

The complete-view obligation has now been reduced further.  Coefficientwise XOR of the nested
ring masks induces exactly the corresponding XOR of `KeyExtract(S_target)`, so every row of the
query-counted target-key tape has an exact public scalar-key transport.  This works for an
arbitrary scalar error sampler and contributes zero TV loss.  Therefore a shifted evaluator for
only `(BRK, extension)` lifts mechanically to the complete `(tape, BRK, extension)` view with the
same error; input-ciphertext flooding is not part of the remaining problem.  For
centered-binomial BRK noise, the target-message update inside the BRK is also exact before its ring
encryption key is shifted.

For rank-one source GLWE, the global-complement part of that ring-key shift is now concrete.  A
public row-message complement followed by the affine ring-key map `s -> 1-vector - s` transports
the complete ring-extension table exactly under any negation-symmetric noise, including the
centered-binomial sampler.  Composing this with exact tape transport and the existing rank-one BRK
complement action proves a bound for the complete adaptive public view:

```text
TV(global-complemented complete view, fresh complemented-key view)
  <= targetScalarDimension * rankOneBRKComplementShearDistance.
```

The extension table and tape add no term.  A certified discrete-Gaussian corollary replaces the
remaining shear distance by the explicit `levels * degree * scalarLinearShiftBound` envelope.
Thus the anchor/global-complement half of fresh-key randomization is no longer an opaque
full-view certificate.  The unresolved step is the normalized nonconstant (relative)
coefficient-mask evaluator; claiming that arbitrary masks have the same affine transport would
be false for the native ring format.  The candidate and one-coordinate guess/check reduction
around an evaluator is checked below.

The normalization itself and its compiler are now checked.  A complete nested mask has a unique
decomposition into (i) a relative mask whose first source-ring coefficient is fixed to zero and
(ii) one global anchor bit.  The encode/decode maps are inverse equivalences, their sequential
actions equal the original coefficientwise action, and independent uniform sampling of the two
pieces maps every fixed nested key to the exact fresh nested-key distribution.  A
`RelativeEvaluationMaterialEvaluator` therefore needs to handle only the normalized nonconstant
mask on `(BRK, extension)`.  Lean transports the complete target tape exactly, then composes the
result with the checked anchor transform and packages the output as the PKC-style
`ViewRandomization`.  The total pointwise loss is

```text
relativeEvaluatorError + globalComplementViewError,
```

where the second term is the explicit rank-one BRK shear bound above.  This compiler is
conditional: it removes ambiguity about the missing object but does not construct the nonlinear
relative evaluator.  Its real- and uniform-branch candidate consequences are developed below.

The failure of the direct vector-LWE instantiation is also formal rather than heuristic.  The PKC
rerandomization map changes an additive secret by a public affine shift.  For the native binary
ring key at modulus greater than two, Lean proves that the source part of a normalized relative
XOR mask admits such a scalar-affine ring-key transport if and only if every retained source
coefficient is false.  Thus any genuinely nonconstant source-relative mask requires a richer
homomorphic/key-changing operation.  This matches the paper's explicit statement that its results
do not directly cover Ring-LWE and that the ring adaptation is open.

The additive route is now checked all the way through the native rank-one TGSW layout, so this
negative conclusion is not caused by an untreated gadget phase.  Starting from a ciphertext under
`s`, public LWE body translation changes the key to `s + delta`; then, at every gadget level, the
public row operation

```text
(row_mask, row_body) -> (row_mask - delta * row_body, row_body)
```

changes the old mask-row phase into the correct phase for the same TGSW message under
`s + delta`.  Uniform challenges are preserved bijectively.  The only distributional change is

```text
(e_mask, e_body) -> (e_mask - delta * e_body, e_body).
```

Lean proves both exact transport under invariance of this error shear and a quantitative TV bound
equal to its explicit defect; independent BRK entries sum this loss.  At coefficient modulus two,
binary XOR is addition and the theorem specializes to arbitrary binary ring masks.  This is a
useful exact boundary case, but modulus two with invariant or uniform row noise is not the
correctness-bearing TFHE regime.  For ordinary TFHE moduli, a nonconstant coefficientwise XOR is
still not an additive ring shift, so the normalized relative evaluator remains open.

The BRK message function is no longer bundled into that open operation.  With centered-binomial
BRK noise, a public exact transformation first changes the encrypted scalar vector from
`KeyExtract(S)` to `KeyExtract(S')`, retaining the old source ring encryption key and the old
extension table.  The remaining `RelativeKeyShiftMaterialEvaluator` has precisely the fixed-key
source and target distributions

```text
(BRK(KeyExtract(S'), S_source),  Ext(S_suffix,  S_source))
    ->
(BRK(KeyExtract(S'), S'_source), Ext(S'_suffix, S'_source)).
```

Here `S'` is the normalized-relative XOR of the complete nested key.  Lean proves the exact first
distributional identity and compiles any certificate for the displayed arrow into the earlier
relative evaluator with no additional error.  Exact tape transport and the global anchor then
produce the full fresh-key randomizer with budget
`keyShiftError + globalComplementViewError`.  The displayed arrow remains the nonlinear
ring-specific research obligation; it is not the original TFHE source-to-target BRK conversion.

The candidate-dependent part of the PKC argument is now explicit.  For any extracted coordinate
of `KeyExtract(S_target)`, fresh public row shifts parameterized by a candidate bit have exact
fixed-key endpoints:

```text
correct candidate  -> real target-key tape + unchanged real evaluation material,
wrong candidate    -> independent uniform tape + unchanged real evaluation material.
```

Uniform tapes remain uniform under every later relative/anchor key action.  Consequently the
same compiled evaluator maps the two candidate endpoints respectively within

```text
epsilon = keyShiftError + globalComplementViewError
```

of the fresh real and fresh uniform-tape public views.  Data processing through an arbitrary
public direct-CircLWE distinguisher and the checked binary guess/check theorem then yields an
executable predictor for that target-key coordinate with success probability at least

```text
(1 + direct public CircLWE advantage - 2 * epsilon) / 2.
```

This is a genuine one-coordinate search-to-decision statement and no longer an uninstantiated
"subsequent guess-and-check" placeholder.  It does not solve the research-level step hidden in
`epsilon`: the current-to-shifted native ring-key evaluator above still has to be constructed or
assumed explicitly.

The finite-coordinate assembly is checked too.  Native key extraction is packaged as an explicit
equivalence between `(S_source,S_suffix)` and the complete Boolean target-message vector.  The
one-shot tester runs once for every coordinate on the same supplied view, reassembles both ring
keys, and uses a union bound on the coordinate marginals; it never assumes that their success
events are independent.  If `delta` denotes the one-shot coordinate error above and `d` is the
target scalar dimension, the resulting exact-recovery statement has the form

```text
1 - sum_(i < d) delta_i <= Pr[recover (S_source,S_suffix)].
```

This solver and the summed error are packaged as a checked narrow-search/wide-decision reduction,
and the direct adaptive TFHE inequality consumes that concrete certificate.  The one-shot sum is
typically vacuous at cryptographic dimensions.  Repeated shared-view amplification still needs a
conditional-fiber law (or a sound threshold/bad-fiber analysis) and cannot be inferred from the
averaged candidate gap alone.

### Prefix-message nested-ring adaptive variant

The converter is also integrated into a distinct optimization whose private
scalar encryption key is

```text
s = KeyExtract(S_source),
```

and key generation constructs

```text
source BRK:   BRK(s, S_source)
derived BRK:  BRK(s, S_source || S_suffix).
```

The final cloud key contains the derived BRK and a scalar suffix-only KSK encrypting
`KeyExtract(S_suffix)` under `s`. The ring-valued extension key is used while deriving the BRK and
then discarded. Coefficient-level lemmas prove that `KeyExtract(S_source)` is literally the
prefix block of the extracted target key and that the remaining coordinates are exactly
`KeyExtract(S_suffix)`.

For every secret-dependent continuation, including adaptive encryption and public homomorphic
evaluation, the derived-BRK real/zero replacement distance is exactly the distance of the source
game

```text
BRK(KeyExtract(S_source), S_source)
  versus
BRK(0, S_source),
```

with the extension process and scalar suffix KSK generation placed inside the continuation. Thus
this prefix-message construction has one source self-cycle, not the earlier heterogeneous two-key
cycle. The resulting adaptive security inequality is

```text
|IND advantage of derived nested-ring TFHE|
  <= source one-circular continuation advantage
     + |IND advantage in the source-BRK-zero endpoint|.
```

Public evaluation adds no term and preserves the encryption query bound. The source circular term
also has the exact statistical bound

```text
2 * sourceBRKRowCount * TV(source BRK error, uniform).
```

Consequently, uniform source-BRK row errors erase the only circular hop, and uniform fresh-input
errors make the BRK-zero adaptive game perfectly fair. The formal zero-advantage theorem permits
arbitrary ring-extension and scalar-KSK errors and survives arbitrary public FHE evaluation. This
is a complete confidentiality theorem but not a usable TFHE parameter theorem: uniform BRK and
input errors destroy the correctness margin.

For narrow centered-binomial or discrete-Gaussian errors, two tasks remain. First, the source
self-BRK must be proved computationally secure. Second, after that BRK is zeroed, ring rows and
scalar rows still share the source secret through coefficient extraction. Splitting them into
independent RLWE and LWE assumptions would be invalid. The appropriate next reduction must use
checked sample extraction to place both presentations inside one ordinary binary-secret
module/RLWE experiment, or state the residual joint assumption explicitly.

For narrow noise, the development now uses a separate exact auxiliary-input CircLWE
classification instead of a vacuous distance-to-uniform estimate. Its only secret is the master
ring key `u`; its real challenge is the native BRK, its zero challenge is the native zero-message
BRK, its uniform challenge has the same BRK carrier, and its retained auxiliary input is the real
suffix KSK. The real branch is proved equal in distribution to the explicit degree-two
self-monomial presentation. The generic real/zero KDM advantage is definitionally the native
one-cycle secret-continuation advantage, and KDM versus CircLWE differs only by the explicit
zero-BRK-versus-uniform side-information term.

Directly using the real-versus-uniform formulation gives the narrow-noise adaptive theorem

```text
adaptive shared-key TFHE IND advantage
  <= Adv_one-cycle-auxiliary-CircLWE(real BRK, real suffix KSK)
     + Adv_batch-LWE(suffixRows + queryCount).
```

The end-to-end theorem is also stated with the literal one-circular KDM game as its first term:

```text
adaptive shared-key TFHE IND advantage
  <= Adv_KDM(BRK_S(prefix(S)), BRK_S(0))
     + Adv_zero-BRK-versus-uniform-with-retained-context
     + Adv_batch-LWE(suffixRows + queryCount).
```

Here `prefix(S)` is the TFHE source scalar key and `S` is the target ring encryption key.  The
second term has only zero plaintexts and is therefore a separate encryption/side-information
obligation, not another circular edge.  The finite, negligible-function, and publicly evaluated
forms are all checked.  This is also why a current-to-shifted master-key transformation appearing
inside a search-to-decision compiler is not used as the definition of one-circular security.

This theorem is valid for any finite executable ring-error sampler and therefore accepts the
centered-binomial and discrete-Gaussian samplers without requiring either to be close to uniform.
It also survives public deterministic FHE evaluation with the same query count and the same two
terms. The first term is precisely the remaining native self-quadratic research premise; the
theorem names it rather than replacing it with ordinary RLWE.

The same statement is now lifted to the negligible-function interface for arbitrary executable
ring-error families. The formal theorem says that negligible induced one-cycle CircLWE advantage
and negligible ordinary query-counted batch-LWE advantage imply negligible complete adaptive
TFHE advantage. Explicit family constructors instantiate the BRK errors with coefficientwise
centered binomial or with certified finite discrete-Gaussian ticket samplers. A separate evaluated
security game compiles public deterministic homomorphic evaluation into the base adversary and
inherits the same asymptotic theorem without another loss.

The corresponding search distribution is now exact as well. A public solver receives the real
self-circular BRK and the real suffix KSK and returns a complete rank-one master-key candidate.
The experiment alone performs the equality check. Its real game is proved equal to the native
secret-continuation game, and every fixed-secret challenge has the explicit degree-two
self-monomial BRK law.

At the uniform-BRK endpoint, the remaining recovery problem is proved exactly equal to search LWE
for the affine shared-KSK problem. A second checked reduction samples the independent suffix and
uniform BRK internally and shows that recovering the whole `(prefix,suffix)` pair is bounded by
ordinary binary-secret batch search LWE for the prefix. If both BRK and KSK are uniform, the
public view is independent of the master secret and every solver succeeds with probability
exactly

```text
2^-(prefixDimension + suffixDimension).
```

Thus the missing search-to-decision construction is no longer entangled with KSK recovery or
uniform guessing. It must transform the real one-key quadratic BRK into a fresh shifted-function
view with a controlled error law. The supplied PKC 2024 result provides the abstract strategy but
does not by itself construct that native ring/TGSW evaluator.

The full secret-randomization boundary is now formalized. Coefficientwise XOR of the complete
binary master key by a uniform binary mask has exactly the fresh master-key law, and it preserves
the shared prefix/suffix relation. Separately, adding the public inner-product correction to an
LWE or RLWE body exactly transports the encryption key by ring addition, matching the additive
step in the PKC 2024 argument. These two operations coincide at coefficient modulus two. For
every `q > 2`, however, a checked characterization shows that a mask-only additive ring
correction implements binary XOR for every source key if and only if every mask coefficient is
false. Hence any mask that randomizes even one native master coefficient cannot use the direct
additive transport.

For rank-one TGSW ciphertexts, that additive transport now includes the necessary gadget-row
repair.  A public mask/body shear maps the same plaintext from key `s` to key `s + delta`, preserves
the uniform challenge law, and changes only the explicit paired error vector.  The theorem lifts
to the complete BRK, with either exact shear-invariant noise or a dimension-summed TV defect.
Consequently the remaining obstruction at `q > 2` is specifically the mismatch between binary
coefficientwise XOR and ring addition—not a missing treatment of TGSW gadget rows.  At `q = 2`
the mismatch disappears and arbitrary-XOR BRK transport is checked exactly, but this degenerate
security-only boundary does not model practical TFHE correctness parameters.

The modulus-two diagnostic is now complete rather than BRK-only. A distinguished positive coin
shows that a centered-binomial coefficient of any positive width is exactly uniform in `ZMod 2`;
independence lifts this to an exactly uniform native ring error. Therefore both the additive TGSW
row shear and the global-complement shear preserve the centered-binomial error vector exactly.
For the ring-extension table, characteristic-two XOR gives two public additive corrections: shift
the rank-one encryption key by the embedded source mask, then add the embedded suffix-mask gadget
messages to the bodies. Lean proves the resulting sampler identity for every extension-error law.
After the BRK messages have been normalized, the complete checked arrow is

```text
(BRK(KeyExtract(S'), S_source), Ext(S_suffix, S_source))
  ->
(BRK(KeyExtract(S'), S'_source), Ext(S'_suffix, S'_source)).
```

It instantiates `RelativeKeyShiftMaterialEvaluator` with error zero, and the existing exact tape
and anchor compiler yields a full fresh-nested-key view randomizer with error zero. This is useful
as an end-to-end consistency test of the reduction interfaces. It is not a usable TFHE security
parameter theorem: positive-width centered-binomial noise modulo two is uniform, so correctness
is lost, while the practical-modulus XOR/addition obstruction remains unchanged.

The executable CMux candidate evaluator does not directly upgrade this result to practical
moduli. Its transform is a coordinate guess tester: the correct guess retains a real view and the
complementary guess aims at a uniform branch. The relative-key interface instead requires one
public transform of the entire correlated BRK-plus-extension material into an honestly generated
view under the XOR-shifted nested key. Its exact phase normal forms and fiber bounds remain useful
inside decision-to-search, but they do not constitute that whole-material key-shift law.

This mismatch is now a checked row identity rather than only a typing observation. For any fixed
TGSW ciphertext, changing its interpretation from a source ring secret to a target ring secret
changes each declared row error by exactly

```text
dot(sourceSecret - targetSecret, ciphertextMask - declaredGadgetMask).
```

For the concrete correct-candidate CMux, Lean proves that the target-key row error is exactly its
existing computed same-key residual plus this `tgswKeyChangeDefect`. Equality with the claimed
shifted-key residual is equivalent to the defect being zero. The theorem is also lifted to an
arbitrary finite sequence of correct-coordinate CMux calls: composition can change the final
public mask, but it does not erase the need to prove that the final defect vanishes or is
statistically absorbed. A separate rank-one diagnostic proves that merely reinterpreting an
honestly assembled source-key row under another key gives a uniform target phase whenever
multiplication by the key difference is bijective and the source mask is uniform. Multiplication
by every executable signed negacyclic monomial is proved bijective, so the result applies directly
to the `+X^i` or `-X^i` key difference induced by flipping one binary coefficient.
`rankOneTargetPhaseVector_uniform_after_binaryCoefficientFlip` strengthens this to an arbitrary
complete vector of independently masked rows: their target phases are jointly uniform, without a
row union bound. The public-view caveat is also checked rather than left implicit.
`rankOneMaskPhaseView_not_surjective` proves that, with any retained row over a nontrivial ring,
the mask/phase pair lies on a proper deterministic graph. Joint phase uniformity therefore does
not imply that the public mask/body ciphertext is uniform; ordinary RLWE or another computational
argument is still needed for that correlation.

The current candidate reduction does not yet supply that missing argument from an ordinary RLWE
challenge. `coordinateSource_context_evalDist_eq_realPublicView` proves that after forgetting the
tested hidden bit, the source averaged by the augmented transformer is exactly the real public
native CircLWE view, including its monomial BRK, real KSK, and bounded input tape. Consequently the
checked chain is genuinely a CircLWE search-to-decision reduction, but it presupposes the real
circular source whose standard-assumption simulation remains the research problem. These results
do not rule out a nonlinear cancellation construction; they state exactly what such a
construction must construct or hide before it can instantiate the relative-key evaluator.

The larger natural scalar-affine route is checked as well. Multiplying each public RLWE challenge
by a unit inverse and applying the corresponding public body correction exactly transports
`s` to `u*s+d` without changing the message or error. At `q > 2`, a complete classification proves
that this realizes coefficientwise binary XOR only for two masks: identity and global complement
`s ↦ -s + 1⃗`. Those two maps are genuine public transports, but they form only a two-element
orbit. For every key with at least two coefficients, Lean proves that any randomness distribution
whose selected scalar-affine masks are valid has an output law different from a fresh uniform
binary key. Thus the direct PKC-style fresh-key step cannot be obtained from additive or
scalar-affine native RLWE algebra. This remains a scoped no-go result: a nonlinear homomorphic
shifted-function evaluator, a transformed secret representation, or circular security by another
argument is not ruled out.

The exact residual invariant is also checked, rather than inferred only from the two-point support
argument. Every positive-length binary master key has a bijective decomposition into its
coefficient-zero anchor and the XOR of every remaining coefficient with that anchor. A uniform
master key maps to a uniform product of the relative key and anchor. Identity/global complement
leaves the complete relative key fixed and refreshes exactly the anchor bit. Consequently, for two
or more coefficients, no generic CircLWE `ViewRandomization` whose key actions all admit the
classified scalar-affine RLWE transport can satisfy its required uniform fresh-secret law. This
identifies the precise target of a future nonlinear evaluator: it must randomize the relative key,
not merely hide or refresh the global complement choice.

There is also a constructive factorization of the desired action. Every complete XOR mask is the
composition of its unique anchor-zero relative-mask lift and its global-complement bit. Applying
those two actions in sequence is exactly equal to applying the original mask. Sampling the
relative mask and anchor independently and uniformly gives the exact full fresh-key law. Therefore
the unresolved native evaluator need not rediscover the entire key action: it must implement the
normalized relative-mask shift on `N-1` bits, after which the checked scalar-affine complement
transport supplies the last secret bit.

That last action is now checked on the evaluation-key objects rather than only on secret algebra.
For the suffix-only KSK, a public row negation plus the all-one gadget table complements every
source bit, and the existing target-key XOR transport complements the shared prefix. For every
negation-symmetric scalar error law, their composition maps the real KSK distribution under the
old master key exactly to the real KSK distribution under its global complement. Thus the KSK
introduces no additional complement obstruction; centered-binomial and certified symmetric
discrete-Gaussian scalar samplers provide the required ordinary negation symmetry.

The rank-one TGSW calculation has a stronger and previously implicit requirement. The public
extended-row conjugation maps a matched mask/body error pair by

```text
(e_mask, e_body) -> (e_mask + d * e_body, -e_body),
```

where `d` is the all-one polynomial offset. Lean proves the deterministic ciphertext identity,
bijectivity of the corresponding challenge action, the complete native TGSW and BRK distribution
laws conditional on invariance under this shear, and the joint BRK+KSK law. Uniform ring-row errors
satisfy the shear law because it is a permutation of the full error vector.

There is now also a quantitative comparison, so exact shear invariance is no longer an interface
requirement. Let `delta_shear` be the total-variation distance between an IID TGSW error vector and
its image under the displayed shear. The public conjugation changes one TGSW distribution by at
most `delta_shear`, and changes the complete BRK, or the joint BRK+KSK, by at most
`lweDimension * delta_shear`. The KSK contributes zero because its complement transport remains
an exact distributional identity. If the ring noise is negation symmetric and every conditional
translation by `d * e_body` costs at most `delta_shift`, Lean proves

```text
delta_shear <= levels * delta_shift.
```

For the repository's exactly negation-symmetric certified discrete-Gaussian sampler, the existing
coefficientwise shift theorem and the universal centered-norm estimate give the concrete endpoint

```text
delta_shear
  <= levels * degree * scalarLinearShiftBound(certificate, q / 2).
```

This is an unconditional finite theorem for every symmetric certificate. It is deliberately
conservative: the worst-case `q / 2` translation need not be negligible for standard narrow TFHE
parameters. In particular, mere centered-binomial or discrete-Gaussian negation symmetry still
does not make the shear free.

The correlated-error alternative is now constructed rather than left as a suggestion. Given any
complete rank-one TGSW error-vector sampler `D`, sample a hidden uniform bit and return either an
error vector from `D` or its image under the shear. Since the shear is an involution, applying it
to this two-point orbit average merely swaps the two branches. Lean proves exact invariance for
every finite base sampler. The native structured TGSW sampler is generalized to consume the
complete correlated vector, and challenge translation still proves exact equivalence with the
direct gadget-phase presentation. Consequently global complement transports one TGSW, the full
BRK, and the joint BRK plus suffix KSK with zero statistical loss.

For an IID centered-binomial base sampler of width `eta`, the construction has a checked
coefficient bound. Every untouched or sheared row satisfies

```text
cInfNorm(row error) <= eta + ringDegree * eta.
```

Thus this shared-randomness variant obtains exact complement symmetry with polynomially narrow,
nonuniform error, rather than the unusable uniform-error endpoint. It modifies the standard IID
TFHE error geometry, so it is not a proof about the unmodified parameter distribution. For the
modified one-cycle scheme the shear task is closed; the central remaining step is a nonlinear
shifted-function evaluator that randomizes the `N-1` relative key bits, followed by a reduction of
the resulting widened correlated-noise decision view to an ordinary hardness assumption.

The exact composition theorem is now checked as well. A `RelativeThenComplementEvaluator`
records the normalized relative-mask evaluator and the final complement evaluator separately;
sequential data processing and the triangle inequality charge each error once. Its output is the
complete search-to-decision `ViewRandomization`, whose mask is a uniform relative key paired with
a uniform complement bit and whose resulting master key is exactly fresh. For the concrete
centered-binomial shear view, Lean instantiates the complement evaluator by a deterministic public
BRK-plus-KSK transform and proves its distributional error is zero. Hence a relative evaluator
with error `epsilon` gives the full fresh-master-key interface with error exactly `epsilon`, not
`epsilon` plus another BRK or KSK term. This is a conditional reduction theorem, not a hidden
construction of the nonlinear relative evaluator.

The KSK can in fact be removed from the relative evaluator obligation as well. For an arbitrary
source-key mask, the public transform leaves an unselected KSK row unchanged and maps a selected
row `(a,b)` to `(-a, g-b)`. Its message changes from `s_i g` to `(s_i XOR 1) g`, while its error is
negated. A coordinatewise-negation theorem proves that every fixed pattern of such signs preserves
an IID negation-symmetric error vector. Composing this source action with the existing target-key
XOR transport gives an exact KSK law for every complete master mask; centered binomial supplies
the symmetry unconditionally.

For a fixed one-cycle master key, the BRK and KSK samplers are independent. Lean factors the
concrete correlated centered-binomial evaluation-key view into those two marginals, applies the
standard independent-product total-variation bound, and substitutes zero for the exact KSK term.
Consequently a BRK-only relative evaluator with error `epsilon` induces the complete relative
view and final fresh-master-key `ViewRandomization` with exactly the same error. The unresolved
nonlinear object is therefore only the self-encrypted BRK marginal; the shared KSK is no longer
part of either the relative or complement circular obligation.

The plaintext component of that BRK obligation is now eliminated too. The shear action commutes
with complete vector negation, and the IID centered-binomial base vector is negation invariant;
therefore their orbit average is exactly negation invariant. Lean lifts the usual public TGSW
message toggle to this correlated-error sampler and then pointwise through the complete BRK. For
every normalized relative mask, let `S` be the current full master and `S'` its shifted value.
This deterministic transform changes the encrypted prefix from `prefix(S)` to `prefix(S')` while
deliberately retaining `S` as the ring encryption key, with zero distributional error.

The remaining internal randomization certificate consequently has the following form:

```text
BRK_S(prefix(S'))
  -- public nonlinear evaluator -->
BRK_S'(prefix(S')).
```

`centeredBinomialShearViewRandomizationOfRelativeMasterShift` composes such a certificate with the
exact BRK-message transform, arbitrary-mask KSK transform, and final complement transform. Its
full fresh-master-key error is exactly the supplied master-shift certificate error. The symbols
`S` and `S'` denote two same-size states of the randomizer; they must not be confused with TFHE's
source scalar key and target ring key.

In the separate coefficient-nesting model, the one-circular statement is

```text
BRK_S(prefix(S))  versus  BRK_S(0),
```

with the suffix-only KSK retained as non-circular auxiliary information. The named theorem
`generateBootstrappingKey_eq_native_prefix_under_master` records the source-prefix/target-ring
relation, while `oneCircularAdvantage_le_circularLwe_add_zeroLwe` states the real one-circular
advantage directly. The master-shift compiler is only one ingredient in a possible
search-to-decision proof of this game; it does not redefine the game or prove it by itself.

This must not be conflated with the nested ring-key construction above. There the checked public
arrow holds the messages fixed and changes the encryption key from `S_source` to
`S_target = S_source || S_suffix`; its security endpoint is the source BRK-plus-KSK real/zero
distance, and its output is a derived target BRK.

At exactly uniform BRK error, the statistical term vanishes and the formal result is the exact
equality

```text
adaptive shared-key TFHE IND advantage
  = Adv_batch-LWE(suffixRows + queryCount).
```

The corresponding adversary-class theorem quantifies over every allowed query-bounded adaptive
adversary and transfers an ordinary batch-LWE hardness bound directly to the full reusable-key
experiment. Thus this wide-noise shared-randomness construction has a checked real circular-FHE
security statement with no circular/KDM assumption. A near-uniform theorem adds precisely
`BRKrowCount * distanceBound` to the assumed batch-LWE bound.

There is now also a concrete executable realization of this endpoint. At coefficient modulus
two, every positive-width centered-binomial coefficient is exactly uniform; the IID coefficient
sampler is consequently uniform on the complete native ring. The checked theorem substitutes
that sampler into the reusable-key adaptive game and bounds the resulting advantage by the one
ordinary query-counted binary-secret batch-LWE advantage, with no circular/KDM term. The same
bound survives arbitrary deterministic public evaluation. This is a security theorem rather
than a correctness theorem: uniform error modulo two destroys the TFHE decryption-noise margin.

This is also lifted to the standard asymptotic interface. Polynomial-query adversary families
have pointwise advantage exactly equal to the associated query-counted batch-LWE family, so
ordinary batch-LWE security implies negligible full advantage. The theorem survives arbitrary
efficient deterministic public homomorphic evaluation. For an executable near-uniform error
family, polynomial BRK growth absorbs a negligible one-draw distance from uniform, again leaving
ordinary batch LWE as the only cryptographic hardness premise.

This endpoint is security-only. Uniform, and normally any distribution close enough to uniform
for the displayed bound to be useful, destroys the decryption-noise margin needed by TFHE
correctness. It therefore proves real contextual circular security for a deliberately wide-noise
shared-key variant, not security and correctness of standard narrow-Gaussian TFHE. Closing the
latter still requires a construction-specific one-key quadratic-KDM/CircLWE theorem or a further
change of encryption/key geometry.

## Paper-aligned intact-cycle assumption interface

The circular/KDM papers define security by comparing encryptions of selected secret-key functions
with encryptions of zero. Their positive theorems are construction-specific: ACPS modifies the
LWE encryption distribution, Brakerski--Vaikuntanathan uses a telescoping Ring-LWE ciphertext,
and Brakerski--Goldwasser--Kalai transforms the secret-key geometry. None of those ciphertext
generators is definitionally the native TFHE cloud-key generator.

The Lean interface therefore records the implication that can be used without changing schemes:

```text
Circular.KeySwitchFirstHardAgainst
  = hardness of (real BRK, real KSK) versus (real BRK, zero-message KSK)
    for a selected class of complete secret-dependent continuations.

Encryption.CutCycleSecurity.NativeIntactCycleKDMHardAgainst
  = its exact adaptive one-time native-TFHE specialization.
```

`oneTimeKeySwitchFirstReplacementAdvantage_eq_abstract` proves the two game presentations equal,
and `nativeIntactCycleKDMHardAgainst_of_continuation` transfers any bound for the generic
fixed-hint game to the induced native one-time adversary class. This is an exact specialization,
not a claim that a cited construction theorem applies to TFHE.

Finally,

```text
oneTimeHardAgainst_of_nativeIntactCycleKDM_and_batchLwe
```

is the adversary-class conditional security theorem. It consumes:

1. one `NativeIntactCycleKDMHardAgainst` bound;
2. one ordinary binary-secret ring batch-LWE bound for the real-message post-cut reduction;
3. one ordinary binary-secret ring batch-LWE bound for the zero-message post-cut reduction; and
4. one joint binary-LWE bound for the zero-cloud KSK-plus-challenge transcript.

Subject to the explicit closure maps for those reductions, their four bounds add to
`Encryption.Security.OneTimeHardAgainst`. Thus the checked development now connects the standard
paper-style real-versus-zero KDM comparison to the exact native fixed-hint game and to the final
TFHE theorem, while leaving the construction-specific hardness claim as an honest assumption.

When KSK and input-ciphertext errors use the same sampler,

```text
oneTimeHardAgainst_of_nativeIntactCycleKDM_and_standardBatchLwe_same_noise
```

replaces the joint scalar problem by a conventional binary-secret batch-LWE problem with
`keySwitchSamples + 1` rows. Its only nonstandard premise is then
`NativeIntactCycleKDMHardAgainst`; the other three premises are conventional batch LWE.

The sequential analogue

```text
Encryption.Adaptive.CutCycleSecurity.hardAgainst_of_nativeIntactCycleKDM_and_batchLwe
```

proves the same four-term composition for an explicitly query-bounded adaptive adversary class.
`TFHE/AsymptoticCutCycleSecurity.lean` then lifts the exact finite inequality into VCVio's
negligible-function framework. In particular,

```text
secureAgainst_of_keySwitchFirst_and_two_ringBatchLWE_and_jointLWE
secureAgainst_of_keySwitchFirst_and_three_batchLWE
```

show that negligible native KSK-first intact-cycle advantage plus negligible post-cut LWE
advantages implies negligible honest adaptive TFHE advantage. The second theorem is the
equal-noise form in which every non-circular premise is an ordinary binary-secret batch-LWE game.

## Remaining circular-security boundary

The nonstandard cryptographic content in the current end-to-end hybrids is confined to the first
native degree-two replacement. It now has three equivalent-purpose presentations: direct
bilinear cross-key module-LWE KDM security for the exact gadget-phase messages in the full
downstream context, native one-challenge auxiliary-input CircLWE, and the public BRK challenge
that retains the real extension table and bounded target-key tape. The complete real branch of
the last presentation is exactly equal to its explicit degree-two monomial law, with the same
auxiliary input and public distinguisher. It gives the compact finite bound “one monomial
CircRLWE advantage plus one ordinary joint module-RLWE advantage.” In the polynomial-view
route, the formerly stronger same-secret BRK batch is reduced exactly to that one challenge and
the KSK/input remainder is ordinary scalar search LWE (one combined batch for the equal-noise
exact-rotation family). The native TRGSW-to-direct distribution-preservation obligation and every
post-cut replacement are proved. What remains is to justify native CircLWE or direct bilinear KDM
from a construction-specific assumption, or to retain it as the named circular-security
assumption.

Direct-LWE affine KDM security does not discharge this premise because a mask-block message
contains the product of a scalar-key bit and a ring-key component. Ordinary decisional LWE/RLWE
also does not generically imply KDM or circular security.

The supplied circular-security references clarify why no automatic theorem is claimed:

- Applebaum--Cash--Peikert--Sahai construct LWE schemes designed for affine KDM and circular
  security. Their result applies to those modified schemes, not automatically to TFHE's native
  TRGSW format.
- Brakerski--Vaikuntanathan prove polynomial KDM security for their Ring-LWE homomorphic scheme,
  whose ciphertext and key distributions differ from TFHE's cloud key.
- Brakerski--Goldwasser--Kalai give transformations beyond affine KDM, but their transformed key
  geometry is not TFHE's native bilinear gadget-phase distribution.
- Micciancio--Vaikuntanathan systematize CircLWE as a named real-versus-uniform assumption and
  give reductions between circular-LWE formulations, including search-to-decision results. Their
  framework does not prove the exact native TFHE auxiliary-input distribution from ordinary LWE.

Accordingly, the distribution-preserving normalization and the final conditional security theorem
are checked. The direct and KSK-first intact first-hop formulations are proved equivalent at the
one-time, sequential adaptive, and asymptotic levels modulo ordinary post-cut LWE terms. The
finite-view reduction gives a separate bounded conditional route with an explicit view count and
fixed-schedule amplification loss; its universal polynomial-schedule lift proves that loss
negligible internally at the asymptotic endpoint. Their nonstandard circular/KDM content remains
explicit and named; the library does not claim that standard LWE or RLWE alone proves it.

Sources used for this mapping include the original TFHE paper; the circular/KDM works of
Applebaum--Cash--Peikert--Sahai, Brakerski--Vaikuntanathan, and
Brakerski--Goldwasser--Kalai; and Micciancio--Vaikuntanathan, *SoK: Learning with Errors,
Circular Security, and Fully Homomorphic Encryption*, PKC 2024,
DOI `10.1007/978-3-031-57728-4_10`.

## Next milestones

1. Focus first on standalone native `RGSW_S(-S)`. The exact strip/restore games, additive secret
   randomization, sample-extracted guess/check layer, hidden-source-error compiler, and production
   binary selector normal form are checked. The anchored centered-binomial theorem now rules out
   closing that compiler by unconditional statistical absorption in the correctness-compatible
   no-wrap regime: every nonzero binary secret leaves anchor variance at least `eta/2`, yielding
   distance at least `eta/(4*B^2)`. Exact external-product cancellation removes this residual while
   preserving the uniform target endpoint, but the generic upper/lower theorem proves that every
   exact digit decomposition retains an upper-row combination with square phase `g*S^2`; only the
   complementary remainder is a zero-message row built from the compiler and lower control block.
   The one-hot specialization retains one original circular upper row with coefficient one. The
   highest two-adic gadget row is now normalized further, without noise growth, to an explicit
   coefficient-affine circular-RLWE operator; a separate no-go theorem proves that this operator
   is not a fixed ring multiplication and therefore is not covered by the ordinary rank-one RLWE
   shift. That endpoint is now exactly reparameterized, in even dimension, as ordinary narrow-noise
   RLWE with the uniform half-dimensional quotient `(s_i xor s_(i+N/2))` exposed. The next target is
   a computational proof of this explicit leakage-resilient RLWE statement, exploiting its affine
   `2^(N/2)`-point fibers, followed by a lifting argument for lower gadget weights where
   off-diagonal square terms survive.
   More generally, a genuinely different computational hybrid may still be needed for a retained
   `g*S^2` row at the native small-error law.
   Merely naming the dependence as a new circular or auxiliary-input assumption is not a
   completion. The broader TFHE degree-two monomial term remains downstream of this standalone
   research problem; extra-component telescoping constructions are retained only as diagnostic
   comparisons unless they can be compressed to the native two-component RGSW law.
2. Continue the now-explicit auxiliary-input CircLWE route. The exact native real, zero, and
   uniform endpoints, the asymptotic equivalence, the reduction of the induced
   `adaptiveZeroLWESecurityGame` to two ordinary scalar batch-LWE games, exact sampled-mask
   scalar-key randomization of both the real and uniform evaluation-key views, and the matching
   native paired-secret recovery experiment, the exact scalar-mask candidate-view audit (real
   endpoint preservation, its averaged transformer, and the theorem that scalar masking alone has
   candidate gap zero), the exact KSK-first candidate permutation and its real-KSK/uniform-KSK
   endpoint laws, candidate-gap equality, scalar union bound, paired-secret recovery theorem,
   swapped auxiliary-input public/search game equalities, the checked one-shot KSK-first
   reduction, its native paired-search hardness transfer with explicit loss, the whole-vector
   one-bad-fiber amplification theorem, the fresh-view centered-binomial paired-key reduction,
   and its exact finite-batch compiler with view count `lweDimension * 3^r + 1`,
   the quantitative shifted-evaluation/smudging
   interface, the final search-hardness transfer theorem, and exact scalar-to-paired completion via
   centered-binomial KSK decoding, standalone-coordinate marginal identities, the whole-key
   coordinate union bound, the executable signed guess-and-check tester and its exact one-shot
   error theorem, and a sound shared-context majority tree with its exact iterated error recurrence
   are formalized. `PointwiseGapAmplificationReduction` connects the amplifier to scalar recovery
   under a support-wise conditional gap. Conditional TLWE/TGSW body smudging, its complete native
   BRK+KSK lift, certified discrete-Gaussian translation bounds, the residual-normal-form adapter,
   narrow-to-wide global decision-to-search accounting, and native TGSW internal-product/CMux
   phase-residual identities are also formalized. The complete bounded input tape is now carried
   by a public augmented CircLWE view, exact scalar XOR transport covers every tape row, the honest
   adaptive BRK replacement is identified exactly with the corresponding public KDM game, and its
   zero branch is discharged by ordinary joint LWE. Augmented averaged candidate recovery now
   includes the threshold/bad-context accounting, scalar union bound, residual-smudging adapter,
   lossless completion to the paired key, and an asymptotic growing-family composition that
   discharges public CircLWE from search plus evaluator loss. The one-shot alternative is also
   formalized: it turns the exact candidate gap into an executable selected-coordinate predictor
   and composes prediction bias plus correct/freshness error with the three ordinary joint-LWE
   terms, without amplification, paired recovery, or correctness. The construction-specific
   native shifted-function evaluator and its complete-context coin sampler are executable, with
   exact candidate transport and CMux phase laws. For the discrete-Gaussian target family, the
   finite-table approximation, wrong-view polynomial layout accounting, selected-diagonal
   reduction, generated-control off-diagonal averaging, and reduction of the off-diagonal
   ciphertext hop to the effective residual-vector `L²` mass expression are now internal. Exact
   structured/direct control equivalence removes the public masks, secrets, and gadget message.
   Negation symmetry removes the Boolean branch, and an exact-capacity equivalence replaces the
   remaining uniform difference ciphertext by IID coefficient digits. Uniform digit/coin/ticket
   presentations turn the `L²` term into an explicit finite fiber-count average. A deterministic
   centered-norm bound and norm-threshold TV lower bound then show why the exponentially wide
   Gaussian is not a plausible statistical target for this polynomially bounded real residual.
   On the selected diagonal, the exact Pearson loss is now split into retained-fiber self and
   distinct contributions. Their finite certificates bound the two Pearson excesses by
   `B_self / |Challenge|` and `B_distinct / |Challenge|`; both confidentiality endpoints consume
   the sum of the corresponding square-root losses. The self contribution now has an exact
   denominator-preserving row-moment form. Its checked good/bad estimate bounds every row by
   `min(1, A/K)`, retains the exact binary-dependent tuple count, subtracts one zero-tuple
   baseline for every nonempty fiber, and divides by the full ciphertext space. The next diagonal
   target is therefore a negligible bound for this explicit inverse-fiber profile, together with
   the parallel distinct-cokernel estimate; no replacement of `K_t` by one is needed.
   The next security target is therefore a computational RLWE/native-circular off-diagonal hybrid,
   while the sharp diagonal and message-one fiber analyses remain explicit. The preferred
   one-shot endpoint also retains explicit native coordinate-prediction hardness and ordinary
   joint LWE, but no correctness premise. The stronger whole-key search route additionally needs
   its visible thresholded amplification loss to be negligible.
   Alternatively, the remaining real-versus-uniform
   problem can be instantiated by a named KDM-secure construction or removed by a clearly labeled
   construction change. A reduction from ordinary RLWE alone is not currently known and must not
   be postulated as a theorem.
   The cut-cycle theorem shows that the nonstandard premise is needed only for the first edge, not
   for the post-cut BRK distribution.
   The direct multi-key affine master-mask theorem is now complete and rules out the logical cycle
   itself as the missing step. The older paired-key KSK-first route still exposes a concrete
   bounded multi-view paired-search premise. For the adaptive scalar-recovery route, that augmented
   premise has now been factored into conventional scalar search LWE plus native one-challenge
   auxiliary-input CircLWE. For the exact-rotation equal-noise family, the scalar rows are one
   ordinary combined batch; the formerly missing polynomial same-secret BRK bridge is the exact
   randomized-hybrid theorem above. The next assumption-reduction target is therefore
   the public augmented native CircLWE premise itself: instantiate it with a genuinely matching KDM-secure
   construction, make a clearly labeled construction change, or retain it as the standard native
   circular assumption, since the supplied references do not derive it from ordinary RLWE. Within the original
   BRK-first route, the remaining
   target is the concrete scalar-coordinate shifted evaluator while the fixed hidden ring key
   still occurs in the bilinear ring/vector BRK phase, or a construction change that removes that
   coupling.
3. Continue the separate TFHE functional-correctness layer. Exact and residual-aware
   external-product identities are checked in `TFHE/Evaluation.lean`, while
   `TFHE/GadgetDecomposition.lean` supplies checked fixed-length base decomposition for both
   `ZMod q` and coefficientwise `Rq`. `TFHE/BlindRotation.lean` now gives the public evaluator and
   its exact binary factor-product/accumulated-error invariant, and `TFHE/SampleExtraction.lean`
   proves constant-coefficient phase preservation for executable negacyclic convolution.
   `TFHE/NoiseBounds.lean` and `TFHE/BootstrappingCorrectness.lean` check deterministic
   centered-noise growth through the full native trace. `TFHE/RotationLookup.lean` now proves the
   missing signed-monomial product law, collapses native controls to one rounded phase, constructs
   executable anti-periodic test vectors from arbitrary first-half tables, and closes the lookup
   equation at the exact finite instance `q = 2N`. Its theorem
   `decode_nativeBlindRotate_apply_bitTable` has no lookup or rounding premise.
   `TFHE/SharpRotationNoise.lean` now proves the executable linear convolution bound and exact
   signed-permutation norm preservation, the sparse `(X^a - 1)` bound, and the corresponding sharp
   one-step external-product estimate. Moreover,
   `decode_nativeBlindRotate_apply_bitTable_linear` removes geometric propagation through the
   native trace. The exact `q = 2N` nonzero-noise obstruction is formalized, rather than left as a
   parameter search problem.
   `TFHE/CenteredBinomialCorrectness.lean` now closes the row-bound obligation for the executable
   centered-binomial family: it projects sampler support through native BRK generation and proves
   the exact finite Boolean-table correctness event with probability one. Torus-Gaussian or
   truncated variants still need sampler-specific tail and model-alignment bounds.
   `TFHE/CenteredBinomialRefresh.lean` additionally closes the fresh-input classification gap for
   this exact finite family. It proves that antipodal phases `0` and `N` plus every supported
   scalar input error remain in the intended anti-periodic Boolean region when
   `2 * inputEta < N`, then composes that result with BRK correctness. The joint fresh-input/BRK
   experiment refreshes the source bit with probability one under the separate input and output
   margins. `TFHE/DivisibleModulusRotation.lean` and
   `TFHE/CenteredBinomialDivisibleRefresh.lean` lift the exact lookup and full fresh-refresh proof
   to every larger coefficient modulus divisible by `2N`. Finally,
   `TFHE/CenteredBinomialLargeModulusEndToEnd.lean` gives a concrete nonzero-noise family with
   `q = 16N^4`, centered-binomial width one, and probability-one refresh for every `λ ≥ 7`.
   `TFHE/CenteredBinomialGrowingNoiseEndToEnd.lean` strengthens it to width `λ + 1`, dimensions
   equal to the least power of two at least `8(λ + 1)`, polynomially bounded modulus `64N^6`, and
   probability-one refresh for every `λ`. The companion growing-noise circular-search module
   proves the level-one KSK distance and recovery margin and specializes the averaged residual
   search-to-decision theorem to its public CircLWE game. The public augmented adaptive theorem now
   pairs probability-one refresh with adaptive confidentiality under public augmented CircLWE and
   ordinary joint LWE; it does not retain a secret-aware continuation premise.
   Remaining correctness work is now
   alignment with the original paper: non-divisible approximate modulus switching and concrete
   torus-Gaussian discretization/truncation and tail bounds, rather than feasibility of a finite
   nonzero-noise construction.
4. Instantiate the checked finite and asymptotic sampler-replacement theorems for the original paper's
   torus-Gaussian notation: define a concrete rounded/truncated executable sampler and prove its
   one-draw ring, KSK, and input TV bounds, including negligibility as parameters grow. The generic
   theorems already multiply those bounds by every polynomially many BRK, KSK, and adaptive-query
   draw and compose the result with circular/KDM plus LWE security. The remaining model-alignment
   work is therefore the concrete torus
   discretization/truncation and the approximate-gadget security/correctness bridge. The existing
   centered-binomial exact-gadget family is a distinct finite variant; either family must still
   supply ordinary LWE and native circular/KDM hardness assumptions.

Security of the cloud-key distribution and functional correctness are independent obligations.
The current structure localizes the remaining circular premise so neither is hidden inside the
other.
