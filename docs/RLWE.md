# RLWE formalization scope and roadmap

## Checked foundation

`FormalProof4FHE.RLWE.Basic` defines the finite negacyclic ring

```text
R_q = (Z/qZ)[X] / (X^N + 1)
```

using VCVio's executable coefficient-vector backend. For positive `N` and nontrivial `ZMod q`,
`quotientOf_bijective` proves that this carrier covers Mathlib's polynomial quotient exactly: the
surjectivity proof reduces every polynomial modulo the monic polynomial `X^N + 1` and reconstructs
its unique degree-`<N` coefficient vector. `quotientOf_mul` checks that executable negacyclic
multiplication has the intended quotient-ring meaning.

`FormalProof4FHE.RLWE.PowerOfTwoCyclotomic` closes the next algebraic identification needed by
power-of-two-cyclotomic hardness statements. It proves, over every commutative coefficient ring,

```text
Φ_(2^(k+1))(X) = X^(2^k) + 1,
```

shows that the two generator ideals are equal, and packages the corresponding quotient-ring
equivalence. `executableToCyclotomic_bijective` and `executableToCyclotomic_mul` compose this with
the checked coefficient backend, so the executable degree-`2^k` carrier is bijective and
multiplicative with the exact order-`2^(k+1)` cyclotomic quotient.

`FormalProof4FHE.RLWE.PowerOfTwoCyclotomicGame` lifts that algebra to the complete decisional
RLWE experiment. It equips the exact quotient with the finite sampling structure transported
from the executable carrier, pushes an arbitrary executable secret law and error law through the
equivalence, and proves `real_evalDist` and `uniform_evalDist`: mapping either complete transcript
produces exactly the corresponding quotient-ring distribution. The inverse adversary maps are
checked on both games, so `reduction_advantage_eq` and
`ofExecutableAdversary_advantage_eq` preserve advantage exactly. The resulting hardness transfers
work in both directions for any adversary classes closed under the displayed public transport.

This is an exact representation theorem. It does not identify coefficient error with a
canonical-embedding spherical Gaussian, establish a number-field ring-of-integers bridge beyond
this monogenic quotient presentation, or prove hardness of a chosen secret/error distribution.

The finite decisional problem samples a shared secret `s`, independent uniform public elements
`a_j`, and independent errors `e_j`. Its real branch gives the adversary
`(a_j, s * a_j + e_j)`; its ideal branch replaces the right-hand sides by independent uniform ring
elements. A one-row matrix represents the public vector, so the following connections are exact:

- `problem_eq_batchProblem`: explicit-secret RLWE is rank-one batch LWE over `R_q`;
- `uniformSecretProblem_eq_moduleProblem_one`: uniform-secret RLWE is rank-one module-LWE;
- `uniformAdvantage_eq_moduleRankOne`: the two distinguishing advantages are equal, with no
  reduction loss.

This is the finite quotient-ring problem used as a cryptographic assumption in scheme-level
reductions. The problem keeps the error sampler abstract, while the following modules provide a
checked concrete instantiation and a base encryption reduction.

## Concrete finite errors

`FormalProof4FHE.RLWE.CenteredBinomial` samples `eta` independent pairs of uniform bits for every
coefficient and returns the difference of their Hamming weights modulo `q`. It proves:

- `coeffBounded_of_mem_support`: every sampled coefficient has an integer representative in
  `[-eta, eta]`;
- `probOutput_neg`: the complete polynomial distribution is invariant under ring negation, proved
  by the explicit permutation that swaps the two bits in every pair.

This is an exact statement about the executable finite sampler. It is not identified with an ideal
Gaussian distribution.

## Base ring-encryption security

`FormalProof4FHE.RLWE.RingRegev` lifts Regev's binary subset-sum construction to arbitrary finite
commutative rings and specializes it to rank one over `Rq q degree`. A public key contains
`sampleCount` RLWE samples. The checked one-time IND-CPA theorem is

```text
Adv_IND-CPA(A)
  <= Adv_RLWE(reduction(A))
     + sqrt(q^(2 * degree) / 2^sampleCount) / 2.
```

The first term is stated directly against `uniformSecretProblem`; the public-key replacement is
therefore an exact decisional-RLWE hop. The second term is the checked finite leftover-hash bound
for the binary subset sum. `oneTime_abs_signedAdvantage_le_of_uniformHardAgainst` packages the
result against an allowed-adversary hardness premise, and
`centeredBinomial_oneTime_abs_signedAdvantage_le_rlwe_add_leftover` instantiates the errors with the
sampler above.

This establishes a useful base-encryption security layer, but it is not yet a security proof for a
complete FHE scheme. In particular, it does not cover BFV/BGV-style ciphertext arithmetic,
correctness/noise growth, evaluation or relinearization keys, key switching, chosen-ciphertext
security, or circular/KDM security. Ring-Regev also uses many public RLWE samples and binary
subset-sum randomness; matching a particular FHE scheme requires a separate scheme-specific
encryption reduction.

## Error-leakage reduction for one unscaled square ciphertext

`FormalProof4FHE.RLWE.LeakyCircular` checks the algebraic and finite-game part of the candidate
argument in `../rlwecircular.md`. Over any finite commutative ring, let four source errors and two
leakage errors be independent and define

```text
S = e₂ + ρ₂,
E = e₃ - e₀(e₁ + ρ₁).
```

The two laws are independent because the sampler is explicitly factored into disjoint random
blocks. The module verifies the error-only leakage matrix

```text
L = [[-1,-1], [1,0], [0,1], [0,0]],
```

its integer Gram matrix `LᵀL = [[2,1],[1,2]]`, and the sharp Rayleigh bound `3`. It then models the
complete four-sample Leaky-RLWE view. The first public mask is sampled as a unit, making its inverse
part of the transcript. This directly captures a source matrix distribution supported on units;
the selection/abort reduction needed to start from unconditioned uniform masks is not included.

For the public secant transform, `transform_real` proves the exact phase identity

```text
B = A*S + S^2 + E.
```

`randomOutputMap_bijective` proves that the same transform sends the random Leaky-RLWE branch
exactly to the uniform law on pairs. The zero-message transform independently samples the product
part of `E` and proves the corresponding exact real and uniform laws. Consequently,
`squareAdvantage_eq_fullLeaky` and `zeroAdvantage_eq_fullLeaky` identify both target advantages
with concrete full-view error-only Leaky-RLWE advantages, and
`kdmAdvantage_le_two_fullLeaky_probComp` proves the real-square versus real-zero bound by their
sum. The hardness-transfer theorem `kdmHardAgainst_of_fullLeaky_probComp` packages the usual
factor-two corollary. No unproved axiom represents Leaky-RLWE hardness.

The module also checks the deterministic bounds

```text
size(S) <= B + Bρ,
size(E) <= B + γ*B*(B + Bρ),
```

and the phase identity for an additional ordinary public-key sample. These are generic algebraic
bounds; specializing `γ` to a concrete negacyclic coefficient norm remains separate. Finally,
`weighted_intermediate_phase_real` confirms the limitation from the candidate note: a public
weight `g` changes the product error to `e₃ - g*e₀(e₁+ρ₁)`. The development therefore proves one
unscaled two-component square ciphertext, not a joint gadget-weighted relinearization key with
weight-independent narrow errors.

`FormalProof4FHE.LWE.Leaky` now formalizes the finite-game part of Lai--Swarnakar--Woo,
Definition 3 and Theorem 3. Given a statistical simulator certificate at branch distance
`2ε/(1-ε)`, `advantage_le_lwe_add_paperLoss` constructs the ordinary-LWE reduction and proves

```text
Adv_LLWE(A) <= Adv_LWE(B) + 4ε/(1-ε).
```

The companion `errorOnly_advantage_le_lwe_add_paperLoss` formalizes Condition 2: the secret law may
be arbitrary provided source and target use the same law, while leakage depends only on the error.
The module also supplies the standard batch-matrix LWE additivity and uniform-translation facts and
the secret/error leakage-matrix interface used by Definition 3.

The preceding analytic discrete-Gaussian theorem that *constructs* the statistical certificate is
not re-proved. Its smoothing, covariance, embedding, leakage-norm, and polynomial-time hypotheses
still require new analytic infrastructure, as does a matching structured source-matrix distribution
(including the unit anchor). Remark 2 explains the ring-valued leakage codomain used by this
application. The local paper is `../refs/leakeylwe.pdf` (with that spelling).

## Interval-masked quadratic KDM security

`FormalProof4FHE.RLWE.IntervalMaskedQuadratic` formalizes the polynomial-loss completion in the
final section of `../rlwecircular.md`. For a binary or ternary coefficient secret `S`, it samples
an independent interval mask `Z ∈ {0,…,M-1}^N` and publishes the finite code for `H=S-Z`.
The checked affine transformation

```text
A = C - 2H,
B = Y - H²
```

sends a real hinted sample `Y=CS+E` exactly to
`B=AS+S²+E-Z²`. For every fixed hint, the same map is a bijection on a uniform pair. The zero
endpoint `(A,AS+E-Z²)` is an exact one-sample short-secret RLWE reduction: sample `Z`
independently and subtract `Z²` from the challenge body.

The hinted hop uses a checked two-copy Boolean product test. Its true-output probability is
exactly one half plus one half of the squared conditional signed gap. The map
`(S,Z) ↦ (hint(S,Z),S)` is proved injective, and a finite Cauchy--Schwarz argument gives the
exact source/target cardinality ratio. Consequently:

```text
binary:  Adv_KDM ≤ sqrt(2 ((M+1)/M)^N Adv_2-RLWE) + Adv_1-RLWE,
ternary: Adv_KDM ≤ sqrt(2 ((M+2)/M)^N Adv_2-RLWE) + Adv_1-RLWE.
```

The ternary factor is slightly sharper than the loose `(1+4/M)^N` guessing estimate in the note.
The conclusion is precisely `RLWE_S(S²) ≈ RLWE_S(0)` for the modified error law
`E∘=E-Z²`. It does not turn this into a gadget-weighted relinearization theorem: applying the
same map to `gS²` produces the larger term `-gZ²`.

## Conditional narrow-error binary/ternary extension

`FormalProof4FHE.RLWE.QuadraticKDMBinaryTernary` formalizes
`../rlwe_quadratic_kdm_binary_ternary_extension.tex`. It recenters the interval mask to
`Z ∈ {-r,…,r}^N`, proves that the public hint has exact average conditional min-entropy

```text
N log₂(dM/(M+d-1)),   d ∈ {2,3}, M=2r+1,
```

and uses the corrected correlated HNF source rows

```text
b₀ = X-S,   dⱼ = cⱼX + gⱼZ² + Eⱼ.
```

The public compiler `Aⱼ=cⱼ-2gⱼT`, `Bⱼ=dⱼ-cⱼb₀-gⱼT²` is checked to produce exactly
`Bⱼ=AⱼS+gⱼS²+Eⱼ`; its random map has an explicit inverse. The module also proves the conditioned
source-error change of variables is bijective, centered ternary and mask signed-permutation laws,
the binary affine complement law and corresponding real/random source transcript symmetry, the
relevant `gⱼ`-dependent source bound, and the complementary direct identity whose error is instead
`W-gⱼZ²`.

The binary and ternary security conclusions are conditional finite-game theorems. They require a
`SplitSearchToDecisionCertificate`, a search-success bound for the masked correlated HNF problem,
and a zero-message RLWE bound for the exact small-secret law. The certificate is where a concrete
application must discharge the external general-distribution HNF theorem's boundedness,
residual-entropy, sample-count, CRT-transitivity, automorphism, and lattice conditions. Those
analytic hypotheses are not inferred from ordinary decisional RLWE inside Lean.

## Correlated RNS-limb/NTT search-to-decision

`FormalProof4FHE.RLWE.RNSSplitSearchToDecisionCorrelated` formalizes
`../rns_split_search_to_decision_correlated.tex` over a heterogeneous dependent product

```text
R_Q = (i : Limb) -> Slot -> K_i.
```

The limb fields need not be identified with one common type. Projection of a coherent HNF block
to one `(limb,slot)` is checked exactly. For a wrong field candidate, the module proves the
candidate map is uniform after conditioning on an arbitrary state, then lifts this equality
through an arbitrary state sampler. That state can contain every other limb and slot, the whole
coherent error polynomial, and arbitrary correlated leakage; no independent-limb error sampler is
introduced. The correct-candidate and non-target secret-shift laws preserve the original error
state exactly.

The anchor layer proves that one recovered limb determines the complete RNS auxiliary secret
whenever the common small anchor has a valid lift. Binary and centered-ternary liftability is
constructed for every `ZMod q_i` limb with `q_i>2`. This construction explicitly passes from
coefficient digits through a supplied per-limb NTT equivalence, so it does not confuse small
coefficient vectors with NTT-slot values.

For `s` limbs and `N` slots, the limb-major hybrid has checked real and random endpoints, adjacent
hybrids differ at exactly one coordinate, and `exists_rns_ntt_adjacent_gap` proves the precise
`epsilon/(s*N)` telescoping gap. Slot automorphisms act diagonally on every limb and on leakage;
the joint-law equivariance premise is represented as one distributional equality, preserving all
cross-limb correlations. `affineActBlock_realBlock` separately checks the affine-complement action
needed by binary coefficient secrets: `X` changes to `sigma(X)+tau`, the anchor error changes to
`sigma(e0)-tau`, and terminal errors keep the diagonal action. The coherent source problem
enforces independence from the auxiliary secret and public coefficients by sampler order.

Finally, the masked source

```text
b0 = X-S,  d_j = c_j X + g_j Z^2 + E_j,  T = S-Z
```

is compiled exactly to `B_j=A_j S+g_j S^2+E_j`, and the conditioned random compiler is an affine
permutation. The complete KDM-to-source game correspondence and the bound
`Adv_KDM <= searchBound + lossBound + zeroBound` are checked for the heterogeneous RNS carrier.
The finite `lossBound` remains supplied by a `SearchToDecisionCertificate`: it records candidate
acceptance estimation, amplification, anchor failure, and query accounting. Lean's current
finite-game layer has no oracle-cost semantics, so the TeX file's asymptotic
`O-tilde(q_max (sN)^3 epsilon^-2 log(1/eta))` running-time claim is not disguised as a proved
executable-cost theorem.

## Rank-one HNF lossiness from small polynomial ratios

`FormalProof4FHE.RLWE.RankOneHNFLossinessRLWENTRU` formalizes the finite algebraic and game-based
content of `../sketch/rank_one_hnf_lossiness_rlwe_ntru.tex`. For the source

```text
b₀ = X-S,   dⱼ = aⱼX+Eⱼ,
```

`eliminateHNF` is given an explicit inverse and proves the pointwise identity
`dⱼ-aⱼb₀=aⱼS+Eⱼ`. At sampler level, translating uniform `X` by the arbitrarily
correlated source secret proves exact equality with a fresh uniform anchor independent of the
entropic RLWE view. The source sampler itself may correlate `S`, every `Eⱼ`, and arbitrary
public leakage.

The module defines conditional guessing probability operationally as the supremum of success
probabilities over all finite probabilistic estimators. A lossy coefficient family retains its
hidden descriptor while publishing only its coefficient vector. The main theorem then proves
exactly

```text
Pr[uniform-coefficient HNF recovery]
  ≤ ofReal(coefficient distinguishing advantage)
    + average conditional P_guess(S | leakage, descriptor, a, aS+E).
```

`SometimesLossyCertificate` exposes smoothing error, good-event probability, and good-event
guessing mass. `RerandomizationCertificate` separately exposes the sample-rerandomization
overhead and solver-class closure needed to turn mild hardness into the target search statement.

For small ratios, `SmallRatioWitness` represents a common invertible denominator and all short
numerators. The Brakerski--Döttling construction is checked algebraically:

```text
zⱼ = g uⱼ + f vⱼ,
f⁻¹ zⱼ = (f⁻¹g)uⱼ + vⱼ.
```

The public-vector advantage is proved to be at most one common-ratio replacement advantage plus
one Hermite-RLWE masked-vector advantage. Data processing bounds the former by the statistical
distance of the ratio itself. This yields named direct joint-NTRU/DSPR, DSPR-plus-Hermite, and
RLWE-only wide-ratio HNF theorems. The wide theorem deliberately carries a reference ratio
sampler, because the analytic Stehlé--Steinfeld statement may be uniform on the unit group rather
than on the whole ring; the Hermite premise must use the same law.

The heterogeneous-RNS theorem applies the same reduction to one complete joint source state. It
does not split coherent error residues into independent limbs. Finally,
`productCancellationSourceState` instantiates the exact quadratic-KDM leakage
`(αS+F,βS+G)` and terminal channel `aⱼS+∑ᵣFⱼᵣGⱼᵣ+Hⱼ`. The resulting security theorem
requires precisely the actual joint guessing bound for that channel. It does not apply Gaussian
small-ratio lossiness to this non-Gaussian leakage-conditioned error without a separate proof.

The number-field Gaussian decomposition, smoothing lemma, singular-value tail estimates,
joint-NTRU/DSPR and Hermite-RLWE hardness statements, and wide Gaussian ratio-uniformity theorem
are not part of the current finite probability library. `SmallRatioGaussianCertificate`,
`MaskedRatioHybridCertificate`, and `WideGaussianRatioUniformityCertificate` retain their numeric
hypotheses and exact game conclusions as explicit proof inputs. No `axiom` or `sorry` is used to
hide those imports.

## Refined product channel and finite-support certificates

`FormalProof4FHE.RLWE.RankOneHNFLossinessRefined` formalizes
`../sketch/rank_one_hnf_lossiness_refined.tex`. For complete leakage
`L=alpha*S+F`, `M=beta*S+G`, it proves the exact identity

```text
sum F*G = P-K*S+g*S^2,
(A,B) = (a-K,Y-P),
B = A*S+g*S^2+H.
```

The affine normalization is an explicit equivalence on the complete public side information, so
operational conditional guessing probability is preserved exactly. The contextual coefficient
game also proves that choosing `a=K(Lambda)+aTilde` preserves the base family's distinguishing
advantage and leaves normalized coefficient `A=aTilde`. Multiplication by a hidden inverse
denominator is checked algebraically and retains the required quadratic term
`z*S+f*g*S^2+f*H`.

For finite secret and output alphabets, the module proves the exact maximum-likelihood identity

```text
P_guess(S | Y) = sum_y sup_s Pr[(s,y)].
```

From this it derives the fixed-context and context-averaged maximal-leakage inequalities, the
exact translated-noise formula for additive channels, and an exact expectation rule for
descriptor-conditioned guessing masses. `extendJointObservation_maximalLeakage` permits each new
RNS limb to depend on the secret and the complete observed prefix; iterating it yields
`jointRNSMaximalLeakageComposition` without assuming independent coherent-error residues.

The numeric Fano step, its uniform-support specialization, the canonical-coordinate formulas,
and the covariance residual sum are checked in Lean. Mathlib/VCVio does not currently provide the
needed discrete/differential entropy bridge, covariance-form lattice Gaussian convolution,
canonical inverse-Gaussian tails, or Stehle--Steinfeld theorem. Their exact conclusions are
therefore represented by `IntegerEntropyCovarianceCertificate`,
`FiniteSupportAdditiveChannelCertificate`, `AveragedGaussianLossinessCertificate`,
`SubgaussianMaskedRatioCertificate`, and `ContinuousGaussianDecompositionCertificate`. These are
ordinary structures containing proof fields, not new axioms.

## Boundary with the foundational papers

The current development does **not** yet formalize the worst-case hardness theorem from
Lyubashevsky--Peikert--Regev (LPR). In particular, the paper's Definition 3.1 uses the ring of
integers of a number field, the dual ideal, the real canonical embedding, a continuous torus, and
an error distribution over that real space. Its Theorems 4.1 and 5.1--5.3 additionally require
ideal lattices, smoothing parameters, discrete/continuous Gaussian analysis, search-to-decision
hybrids, polynomial-time reductions, and a quantum sampling step.

The finite `ProbComp` model cannot represent an ideal Gaussian exactly because every `ProbComp`
has finite support. As in `FormalProof4FHE.Probability.ModularGaussian`, an ideal infinite-support
distribution should be specified as a `PMF`; a separate statistical-distance theorem must connect
it to a concrete truncated or bounded sampler. Equating the two by definition would introduce a
false sampler claim.

Relevant workspace references are:

- LPR, *On Ideal Lattices and Learning with Errors Over Rings*, at
  `../refs/rlwe/ideal-lwe.pdf` relative to the repository root, especially Definitions 3.1--3.3
  and Theorems 4.1 and 5.1--5.3;
- Peikert--Regev--Stephens-Davidowitz, *Pseudorandomness of Ring-LWE for Any Ring and Modulus*,
  at `../refs/rlwe/2017-258.pdf`, especially Definition 2.15 and Theorem 6.2;
- Brakerski--Döttling, *Lossiness and Entropic Hardness for Ring-LWE*, at
  `../refs/rlwe/2020-1185.pdf`, especially Theorem 6.9 and the discussion following Theorem 1.1;
- Boudgoust--Jeudy--Roux-Langlois--Wen, *On the Hardness of Module-LWE with Binary Secret*, at
  `../refs/rlwe/Boudgoust2021_Chapter_OnTheHardnessOfModule-LWEWithB.pdf`, especially the module-rank
  condition and the explicit bin-RLWE open problem;
- Bolboceanu--Brakerski--Perlman--Sharma, *Order-LWE and the Hardness of Ring-LWE with Entropic
  Secrets*, at `../refs/rlwe/Bolboceanu2019_Chapter_Order-LWEAndTheHardnessOfRing-.pdf`;
- Peikert--Pepin, *Algebraically Structured LWE, Revisited*, at
  `../refs/rlwe/structured-lwe.pdf`, for a modern common algebraic interface and reductions among
  structured LWE variants.

## What the Isabelle Kyber entry contributes

The local Isabelle development is useful for specification and arithmetic cross-checking, but it
does not contain a Kyber security reduction. Its own document states that it proves key generation,
encryption/decryption correctness under a high-probability condition, and NTT/convolution facts.
The closest reusable ideas are therefore:

- `../Isabelle/CRYSTALS-Kyber/Kyber_spec.thy`: quotient-polynomial and scheme definitions;
- `../Isabelle/CRYSTALS-Kyber/NTT_Scheme.thy`: NTT algebra;
- `../Isabelle/CRYSTALS-Kyber/Crypto_Scheme.thy` and
  `../Isabelle/CRYSTALS-Kyber/Compress.thy`: correctness and error bounds.

VCVio already supplies analogous Lean-side negacyclic-ring and ML-KEM specification layers. The
Isabelle theories can guide statement comparison, but no game-based security theorem can be
ported from them.

## Recommended next milestones

The first four TFHE milestones formerly listed here are now checked: native TLWE/TRLWE/TGSW
syntax and phase identities, adaptive encryption games, exact evaluation-key hybrids, ordinary
post-cut LWE reductions, asymptotic composition, sharp blind-rotation correctness, and concrete
centered-binomial refresh families are formalized. The strongest current family has ring degree
equal to the least power of two at least `8(λ+1)`, a polynomially bounded modulus, linearly growing
centered-binomial width, and probability-one fresh Boolean refresh. Its confidentiality theorem is
conditional on the exact native auxiliary-input CircLWE game plus ordinary scalar and ring LWE
games.

The remaining milestones are therefore:

1. Treat native auxiliary-input CircLWE as the precise open circular-security boundary. The
   supplied ACPS, BV, BGK, and PKC 2024 references do not reduce TFHE's heterogeneous bilinear
   BRK/KSK distribution to ordinary LWE or RLWE. A future unconditional result must either prove
   that construction-specific assumption, instantiate a genuinely matching KDM-secure
   construction, or explicitly change the evaluation-key construction. The native shifted
   candidate evaluator and complete `(BRK, KSK, tape)` transform are now executable. Its
   uniformized endpoint is exactly connected to the public uniform game, and a statistical adapter
   exposes mask-averaged rank loss as an explicit TV term. A direct statistical certificate now
   also records the concrete correct-view distance without assuming a fixed residual form; the
   sampled-residual smudging certificate is a proved sufficient specialization and permits the
   residual to depend on evaluator coins and fresh secrets; deterministic residuals embed as
   probability-one samplers. The actual arbitrary-BRK correct phase has now been decomposed into
   the target gadget phase plus the executable digitized-CMux residual, and conditioning the
   selected mask bit is an exact reparameterization of the original uniform evaluator coin. The
   concrete open subproblem is therefore quantitative output-mask/error-law freshness for this
   fixed residual experiment, support-wise smudging bounds, the mask-averaged wrong-branch
   distance, and augmented paired-search hardness.
2. Connect the finite centered-binomial binary-secret ring-LWE assumption to a genuinely matching
   foundational structured-LWE hardness theorem. The complete normalization interface is now
   checked: the post-cut BRK batch, binary-secret RLWE, and a coefficient-level problem with
   explicit negacyclic convolution have equal real and uniform games and identical advantage; the
   centered-binomial ring sampler is exactly the direct independent coefficient sampler. The ring
   degree is now a power of two with `8(λ+1) ≤ N < 16(λ+1)`. The identity
   `Φ_(2N)=X^N+1`, equality of the defining quotient ideals, and bijective multiplicative map from
   the executable carrier to that quotient are all checked, rather than inferred from the
   parameter shape. The secret space has checked cardinality `2^(rN)` and exact point probability
   `2^(-rN)`. The growing-noise end-to-end theorem consumes this
   coefficient game directly. What remains is the actual hardness theorem for rank one, composite
   modulus `(2N)^6`, Boolean coefficient secret, and centered-binomial error. Brakerski--Döttling's
   concrete entropic theorem instead concludes hardness with Gaussian target error under
   DSPR/noise-lossiness hypotheses and explicitly observes that entropy bounds alone do not reach
   binary coefficient secrets. The supplied binary-secret Module-LWE result requires an increased
   module rank and explicitly does not settle binary-secret Ring-LWE, so neither result closes this
   step.
3. Align with the original TFHE paper by formalizing non-divisible approximate modulus switching
   and a rounded/truncated torus-Gaussian sampler with checked tail and statistical-distance bounds.
4. If the target is the LPR hardness theorem itself, first build the number-field/ideal-lattice and
   canonical-embedding library, then Gaussian smoothing and search-to-decision. Treat the quantum
   reduction as a separate final layer.

This ordering keeps the immediately useful FHE security theorem independent of the much larger
foundational hardness proof, while leaving a precise path to the latter.
