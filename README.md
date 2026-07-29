# FormalProof4FHE

Lean 4 formalizations of security reductions used by lattice-based fully homomorphic encryption.
The repository currently contains decisional LWE and finite negacyclic RLWE interfaces, executable
centered-binomial RLWE errors, concrete Regev and ring-Regev one-time IND-CPA reductions, the
block-binary secret reduction of ePrint 2023/958, the
shared-randomness LWE hardness reduction of ePrint 2023/979, and a checked embedding of
shared-randomness LWE into a generalized heterogeneous two-subspace game. It also contains the
adaptive affine-projection oracle and rank-loss accounting needed for the broader Subspace-LWE
hardness theorem. The TFHE layer formalizes finite-modulus native TLWE and structured TRGSW
ciphertexts, key extraction, concrete cloud-key samplers, their circular dependency cycle, and an
adaptive one-time encryption theorem together with a fixed-batch, query-counted extension.
It also includes a query-bounded sequential encryption-oracle theorem in which later message
pairs may depend on earlier ciphertexts, plus an asymptotic negligible-advantage theorem for
families carrying explicit polynomial query bounds and a finite centered-binomial instantiation
with executable base gadgets. All direct-TLWE key-switch and challenge
obligations reduce to shared-secret binary LWE. Native TRGSW sampling is proved exactly equivalent to direct
gadget-phase module-LWE rows, exposing the remaining circular premise as bilinear cross-key KDM
security rather than an unspecified ciphertext-format assumption. A separate cut-cycle theorem
proves that once the opposite KSK edge is zero, native BRK replacement follows from ordinary
parallel binary-secret module-LWE; the unresolved premise is therefore confined to the first hop
while the two-way cycle is intact.
The optimized
shared-randomness IKSK is proved to introduce no security assumption beyond the conventional
full-size IKSK between independent keys.

## Build

Initialize the pinned proof-framework dependency and build the Singularity image:

```bash
git submodule update --init vendor/VCVio
scripts/container-build
scripts/check
```

The generated `build/formalproof4fhe.sif` is intentionally not tracked. Lean, Lake, and all proof
checks run inside the container; no host Lean installation is required.

## Main checked results

- `FormalProof4FHE.RLWE.quotientOf_bijective` and `quotientOf_mul` connect the executable negacyclic carrier
  `ZMod q[X]/(X^N+1)` to its semantic polynomial quotient.
  `FormalProof4FHE.RLWE.PowerOfTwoCyclotomic.cyclotomic_two_pow_succ_eq` proves
  `Φ_(2N) = X^N + 1` for `N = 2^k`; `executableToCyclotomic_bijective` and
  `executableToCyclotomic_mul` then identify the executable carrier bijectively and
  multiplicatively with that exact cyclotomic quotient. The companion game module transports
  arbitrary source secret and error laws through this equivalence, proves equality of the complete
  real and uniform transcript distributions, and preserves every distinguishing advantage in both
  directions. Its two hardness-transfer theorems therefore lose nothing at this representation
  boundary.
  `uniformSecretProblem_eq_moduleProblem_one` and `uniformAdvantage_eq_moduleRankOne` prove that
  finite uniform-secret decisional RLWE is exactly rank-one module-LWE, with no loss in advantage.
  This is the average-case assumption interface, not the LPR worst-case ideal-lattice reduction;
  see `docs/RLWE.md` for the boundary and roadmap.
- `FormalProof4FHE.RLWE.CenteredBinomial.coeffBounded_of_mem_support` and `probOutput_neg`
  check an executable centered-binomial polynomial sampler: every coefficient has a representative
  in `[-eta, eta]`, and swapping its bit pairs proves exact negation symmetry.
- `FormalProof4FHE.RLWE.RingRegev.oneTime_abs_signedAdvantage_le_rlwe_add_leftover` proves
  rank-one ring-Regev one-time IND-CPA from the existing uniform-secret RLWE game, with the explicit
  finite masking term `sqrt(q^(2N) / 2^m) / 2`. The corresponding hardness-transfer theorem and
  centered-binomial specialization are checked as well. This is base-encryption security; it does
  not by itself cover homomorphic evaluation keys, relinearization, or circular security.
- `FormalProof4FHE.RLWE.LeakyCircular.kdmAdvantage_le_two_fullLeaky_probComp` checks the candidate
  error-only Leaky-RLWE reduction for one unscaled two-component square ciphertext. The target laws
  are `S=e₂+ρ₂` and `E=e₃-e₀(e₁+ρ₁)` with independent sampler blocks. Both square/uniform and
  zero/uniform hops are exact reductions from the complete four-sample leakage view, including
  explicit uniform-branch bijections; their sum bounds square/zero KDM advantage. The leakage
  matrix has checked Gram bound `3`, and the product-noise and weighted-error identities are also
  formalized. `FormalProof4FHE.LWE.Leaky.advantage_le_lwe_add_paperLoss` now checks the complete
  finite-game reduction from the paper's statistical simulator certificate to ordinary LWE, with
  exact loss `4ε/(1-ε)`; its Condition-2 specialization permits an arbitrary identical secret
  law and error-only leakage. The multivariate discrete-Gaussian theorem producing that certificate
  remains analytic input, and gadget-weighted relinearization with weight-independent errors is not
  solved; see `docs/RLWE.md`.
- `FormalProof4FHE.RLWE.IntervalMaskedQuadratic.binary_kdmAdvantage_le` and
  `ternary_kdmAdvantage_le` prove the interval-mask completion of unscaled quadratic KDM security.
  For an independent coefficient mask `Z ∈ {0,…,M-1}^N`, the checked public map
  `A=C-2H`, `B=Y-H²` with `H=S-Z` sends hinted RLWE exactly to
  `(A, AS+S²+E-Z²)` and sends its random branch exactly to uniform. A one-sample ordinary
  short-secret RLWE reduction handles `(A,AS+E-Z²)`, while the cancellation-free two-copy
  reduction has loss `sqrt(2 ((M+1)/M)^N Adv)` for binary coefficients and the sharper
  `sqrt(2 ((M+2)/M)^N Adv)` for ternary coefficients. The public interval code and its
  injectivity, both affine game identities, the squared-bias probability identity, and the
  concrete cardinality factors are all checked. The conclusion deliberately uses the modified
  error law `E−Z²`; it does not claim gadget-weighted `gS²` security with narrow
  weight-independent noise.
- `FormalProof4FHE.RLWE.QuadraticKDM.kdmAdvantage_le_search_add_loss_add_zero` formalizes the
  conditional fixed-gadget theorem from `rlwe_quadratic_kdm_security.tex`. For arbitrary public
  weights satisfying `sum_r α_jr β_jr = g_j`, the checked compiler sends the corrected correlated
  HNF source view exactly to `(A_j, A_j S + g_j S² + H_j)` and sends its random branch exactly to
  joint uniform through an explicit inverse. The one-coordinate split-field correct/wrong
  candidate laws, joint public-key extension, relinearization phase, latent reconstruction,
  source-error size bound, and projected discriminant identity are checked as well. The final
  theorem deliberately requires a `SplitSearchToDecisionCertificate`, its correlated-HNF search
  bound, and a zero-message RLWE bound; the BJTW general-distribution search theorem and its
  boundedness, entropy, sample-count, automorphism, and lattice inequalities are not asserted as
  consequences of ordinary decisional RLWE.
- `FormalProof4FHE.RLWE.QuadraticKDMBinaryTernary.binary_kdmAdvantage_le_search_add_loss_add_zero`
  and `ternary_kdmAdvantage_le_search_add_loss_add_zero` formalize the centered-mask extension in
  `rlwe_quadratic_kdm_binary_ternary_extension.tex`. The finite hint fibers are shown surjective
  with a unique mask for each `(hint,secret)`, giving exact residual entropy
  `N log₂(dM/(M+d−1))`. The masked source compiler sends
  `b₀=X−S`, `dⱼ=cⱼX+gⱼZ²+Eⱼ` exactly to
  `(Aⱼ,AⱼS+gⱼS²+Eⱼ)` and its random branch exactly to uniform. Centered ternary and mask
  signed actions, the binary affine complement `s ↦ −s+1`, real/random affine source symmetry,
  the conditioned source-error bijection, the `gⱼ`-dependent source norm bound, and the direct
  weighted identity with residual error `W−gⱼZ²` are checked. The two concrete security theorems
  remain deliberately conditional on a checked split search-to-decision certificate, correlated
  HNF-RLWE search hardness, and exact binary/ternary zero-message RLWE; they do not silently
  instantiate the external general-distribution search theorem.
- `FormalProof4FHE.RLWE.RNSSplitSearchToDecisionCorrelated.rns_quadraticKDMAdvantage_le_search_add_loss_add_zero`
  formalizes `rns_split_search_to_decision_correlated.tex` over the genuine heterogeneous product
  `(i : Limb) -> Slot -> K_i`. The wrong-candidate permutation is lifted through an arbitrary
  coherent error/leakage state sampler, the non-target secret shift retains that state, and a
  liftable common HNF anchor upgrades one recovered limb to the complete secret. Binary and
  centered-ternary coefficient anchors are proved limbwise liftable for `q_i>2` through explicit
  per-limb NTT equivalences. The limb-major `s*N` hybrid endpoints, one-coordinate adjacency,
  `epsilon/(s*N)` gap, diagonal automorphism action, binary affine-complement action, exact
  narrow-error quadratic compiler, random affine permutation, and KDM/source game correspondence
  are checked. The final finite advantage
  theorem keeps acceptance estimation, amplification, anchor-failure, and oracle-cost accounting
  in an explicit `SearchToDecisionCertificate`; the library does not claim its unmodeled
  asymptotic runtime formula as an executable Lean cost theorem.
- `FormalProof4FHE.RLWE.RankOneHNFLossinessRLWENTRU.realUniformHNFRecovery_le_coefficientAdvantage_add_averageLossiness`
  formalizes the rank-one lossiness reduction from
  `sketch/rank_one_hnf_lossiness_rlwe_ntru.tex`. The map
  `b₀=X-S, dⱼ=aⱼX+Eⱼ ↦ (b₀,aⱼ,dⱼ-aⱼb₀)` is an explicit bijection and sends the
  original game exactly to an independent uniform anchor plus `aⱼS+Eⱼ`. Conditional
  guessing probability is operationally defined as the supremum over every finite estimator,
  yielding the exact bound `Pr[recover] ≤ Adv_coeff + P_guess`. The module proves the common
  masked-ratio identity, the DSPR/statistical-ratio plus Hermite-RLWE hybrid, direct joint-NTRU,
  RLWE-only wide-ratio, coherent-RNS, rerandomization, and quadratic product-cancellation
  compositions. Gaussian smoothing, singular-value tails, joint-ratio/DSPR hardness, Hermite
  RLWE, and Stehlé--Steinfeld ratio uniformity are explicit certificate premises; they are not
  introduced as Lean axioms. In particular, the final product-cancellation theorem still requires
  the actual joint `P_guess` bound for `sum F⋅G+H` conditioned on all public leakage.
- `FormalProof4FHE.RLWE.RankOneHNFLossinessRefined.contextualSupportAwareGuessingBound`
  formalizes the refinements in `sketch/rank_one_hnf_lossiness_refined.tex`. It proves the exact
  complete-leakage cancellation `(a,Y) ↦ (a-K,Y-P)`, invariance of operational guessing under
  that public bijection, and exact advantage preservation for the leakage-dependent translation
  `a=K(Λ)+aTilde`. For finite alphabets it proves
  `P_guess(S|Y)=sum_y max_s Pr[(s,y)]`, derives contextual and additive-channel maximal-leakage
  bounds, integrates descriptor-dependent bounds, and composes conditional leakage over RNS limbs
  whose law may depend on the complete preceding history. The Fano algebra and covariance
  residual identity are native. Differential-entropy maximization, continuous/discrete Gaussian
  existence, smoothing, and subgaussian concentration are retained as typed certificates rather
  than axioms.
- `FormalProof4FHE.RLWE.RankOneHNFLossinessSupportAware.weightedSpanningTreeGuessingBound`
  formalizes `sketch/rank_one_hnf_lossiness_support_aware.tex`. For an actual finite secret-support
  tree it proves `P_guess <= pi(root) + sum_edges ||pi(u)P_u-pi(v)P_v||_1`, proves the sharp
  weighted-TV edge estimate, and derives the uniform `1/M + 2(1-1/M)delta` corollary. Descriptor
  averaging, finite interval cells, randomized data processing, full-ternary and exact-weight
  support cardinalities, and the quadratic local-edge factorization are native. The complete
  coherent CRT/RNS channel samples one shared error, has an exact center-lift/consistency
  likelihood and maximal-leakage expansion, and is invariant under CRT recombination. The IID and
  fixed-weight tensor pushforwards to the stated square covariance are checked by matrix algebra.
  Continuous-Gaussian TV/log-determinant entropy, concrete negacyclic tensor/moment construction,
  and Bernstein row-energy tails remain ordinary proof-carrying certificate inputs, not axioms.
- `FormalProof4FHE.RLWE.RankOneHNFLossinessRenyi.conditionalRenyiProductGuessingBound`
  formalizes `sketch/spanningtree.md` and replaces the additive tree estimate by the exact finite
  conditional Renyi product theorem. It proves the prior-sensitive `L^alpha` guessing bound and
  exact tensorization across independent evaluation-key rows, with each coherent CRT/RNS row kept
  as one joint output. Row-energy and min-entropy reduction, centered-MGF arithmetic, the explicit
  exponential margin and its displayed `r` choice, fixed-weight conditioning loss, descriptor
  averaging/bad-set splitting, finite coordinate oscillations, and quadratic codebook update and
  sensitivity identities are native. The equal-covariance Gaussian integral, Hoeffding/Doob MGF
  step, product-Laplace density integral, and infinite-lattice theta estimate are isolated as
  proof-carrying certificates; their use through the ternary and discrete-Gaussian endpoint
  theorems is checked without new axioms.
- `FormalProof4FHE.RLWE.RankOneHNFLossinessMixtureRenyi.conditionalGaussianMixtureClusterGuessingBound`
  formalizes `sketch/mahalanobisimprove.md` and removes the artificial absolute-Mahalanobis-energy
  cost of a single zero-centred reference. Lean proves the arbitrary-reference theorem, the exact
  optimized Renyi centre, its finite variational optimality, the expected posterior-norm and
  posterior-collision formulas, and the fact that the actual-marginal objective is at most one.
  Weighted log-sum-exp then gives the local-cloud exponent
  `(alpha-1)D + (alpha-1)A/2 + (alpha-1)^2*‖dbar‖^2/2`; uniform-support cancellation, the displayed
  exponential lossiness criterion, posterior-neighborhood mass, descriptor/leakage averaging,
  normalized discrete-Gaussian weights, and the quadratic codeword-difference factorization are
  native. The equal-covariance density-ratio integral and standard-Gaussian linear MGF are the two
  explicit fields of `EqualCovarianceGaussianMixtureCertificate`, not hidden axioms. The optimized
  finite theorem itself also applies directly to wrapped, modular, and coherent-RNS channels.
- `FormalProof4FHE.RLWE.RankOneHNFLossinessGaussianCluster.conditionalGaussianMixtureEffectiveOverlapBadSetBound`
  formalizes `sketch/gaussiancluster.md`. Lean constructs the soft-overlap Gibbs law, proves its
  exact entropy--energy decomposition, and proves the barycenter-aware primal--dual gap. A
  proof-carrying Gibbs fixed point certifies strong duality and optimizer quality. Full and
  restricted local clouds, the floored effective-codebook bound, exponential bad-set theorem,
  arbitrary finite non-Gaussian likelihood-ratio inequality, and tail-truncation/data-processing
  theorem are native. The quadratic product-cancellation difference and complete embedded row
  energy are factored exactly. Continuous equal-covariance Gaussian integration remains the
  explicit inherited certificate boundary; existence or numerical discovery of a fixed point is
  not assumed as an axiom.
- `FormalProof4FHE.RLWE.RankOneHNFLossinessSparseRank.primitiveDifferenceRank_dyadic_lower_bound`
  and `exact_encodedPrimitiveRank_count_eq_syndrome_count_sub_succ` formalize the symbolic sparse-rank
  refinements for binary repeated-root negacyclic rings. Lean proves the Hasse-syndrome
  characterization of `(X-1)`-adic valuation, the exact repeated-root minimum distance
  `2^(d-log2 r)`, and the resulting dyadic lower bound on every distinct fixed-weight ternary
  primitive difference. It also decodes the existing support-and-sign secret representation,
  proves its exact cardinality, classifies exceptional low-rank pairs by adjacent syndrome counts,
  and derives exact rank-enumerator, coarse minimum-rank, Markov, and finite union bounds. The
  odd-determinant lifting theorem proves that any certified nonzero binary minor gives uniformly
  distributed production coordinates even after a fixed quadratic translation. Selecting such a
  minor for the concrete implementation channel and supplying its one-coordinate Gaussian/theta
  or bounded-support estimate remain explicit premises, not axioms.
- `FormalProof4FHE.RLWE.RankOneHNFLossinessSparseRankChannel.card_primitiveDifference_binaryQuotient_range`
  connects that symbolic rank to literal multiplication in
  `F₂[X]/(X^(2^d)+1)`: the primitive ternary difference has image cardinality exactly
  `2^primitiveDifferenceRank`, hence an abstract equivalence with that many independent binary
  coordinates. A production minor certificate lifts any concrete nonsingular binary minor and
  proves affine uniformity after the factored quadratic shift. The module also gives a VM-executable
  finite `(two-adic exponent, Hasse rank)` histogram, proves its Boolean coefficient scanner equal
  to the mathematical Hasse valuation, expresses every cell as adjacent branch-restricted syndrome
  counts, and aggregates exponent-dependent `theta_e^r` factors.
  For bounded noise it proves the local factor itself by finite coordinate-box counting. Finally,
  it proves that a wrong candidate is exactly uniform on its principal ideal, computes the
  missing cokernel as `2^valuation`, proves that positive valuation prevents promotion to
  full-ring uniformity by deterministic reindexing, and shows precisely how an independent
  cokernel coordinate would complete it. Finding a public, hidden-difference-independent
  completion (or padding construction) remains a reduction-design obligation, not an axiom.
- `FormalProof4FHE.RLWE.RankOneHNFLossinessTwoSmith.card_quotientPowerOfTwo_twoPrimary_range_eq_layered`
  formalizes `sketch/twosmith.md` in the literal ring
  `(ZMod (2^K))[X]/(X^(2^d)+1)`. Lean proves that a primitive lift with binary Hasse depth `v`
  is a unit times `(1-X)^v`, proves `2` is a unit times `(1-X)^(2^d)`, and consequently computes
  the image as `2^((K-e)(n-v)+(K-e-1)v)` and the cokernel as `2^(e*n+v)`. The module supplies
  carrier equivalences with the two-level Smith image and cokernel models; it deliberately does
  not expose a high-norm Smith basis change. Instead, a concrete triangular Pascal minor proves
  that the first `v` coefficient positions form a Hasse information set, yielding the exact
  binary-cube enumerator bound and the IID factor `p_e^(n-v) p_(e+1)^v`. It also proves the
  invariant finite local-overlap identity, its two-level joint-stratum aggregation, and an exact
  annihilator-character formula for arbitrary correlated finite error tapes. All of these are
  native theorems; converting an implementation's analytic Gaussian or bounded-noise model into
  the scalar local masses remains the parameter-specific input.
- `FormalProof4FHE.RLWE.RankOneHNFLossinessTwoSmithExact.jointTupleAggregation`
  formalizes `sketch/twosmith_exact_parameter_note.tex`. The native Hasse/Pascal code has an exact
  IID Fourier collision identity, and its row-space and kernel weight enumerators satisfy the
  Lucas recurrences used by the rational evaluator. Lean proves the IID parity-bias square
  identity, the exact Hasse factor and its two-level product bound, the adjacent-kernel
  coefficient formula, and both branches of the signed fixed-weight ternary pair histogram.
  For the literal power-of-two quotient it also proves capped multiplicativity of the chain
  valuation and applies it to the complete descriptor
  `(t-s)*(z+f*g*(t+s))`, without assuming the second factor is a unit. Finally, finite sums are
  regrouped by the complete row tuple, with rowwise factorization available only after explicit
  conditional independence.
- `FormalProof4FHE.RLWE.TFHEppLvl5BootRenyiObstruction.lvl5_firstOrderRenyiMargin_not_pos`
  is the concrete arithmetic screen for TFHEpp `lvl5bootparam`. Lean bounds the corrected
  fixed-weight support `2^96 choose(32768,96)` below `2^1038`, checks the exact square moment
  `600806592/32767`, and proves that the `g=2^622`, `sigma=2^33` top row alone exceeds twice the
  entire support entropy. This rules out the direct uniform-prior, equal-covariance Renyi
  sufficient condition for these rows; it neither proves insecurity nor discharges the abstract
  continuous-Gaussian/channel-identification premise.
- `FormalProof4FHE.RLWE.TFHEppLvl5BootGaussianClusterScreen.radiusTwoGoodMask_no_128bit_certificate`
  checks the follow-up Gibbs-cluster experiment against the source-bound TFHEpp parameters. The
  support-radius-two cloud is represented by the three replacement orbits
  `2^96 choose(96,k) choose(32672,k)` for `k=0,1,2`; it has `log2(M)=137.1463`, so unlike radius
  one it is large enough for 128 bits under hypothetical perfect overlap. One top-row mask
  coordinate makes every nonidentity Gaussian kernel smaller than `2^-604` in expectation.
  Lean checks the resulting Markov arithmetic (`Pr[K > 1+2^-128] < 2^-338`) and proves that an
  effective size below two cannot yield even a one-bit Renyi bound at any positive order. It also
  checks the exact signed-`int64` support diameter and the finite-channel union arithmetic
  (`<2^-436`): on the good mask event, every tested neighbor is support-disjoint from the centre
  in one coefficient. The integer theta-sum estimate and source-to-uniform-coordinate refinement
  are explicit certificate boundaries; this rejects the tested cluster, not security itself.
- `FormalProof4FHE.RLWE.TFHEppLvl5BootTwoSmithScreen.lvl5_literalCompleteCodebookOverlap_lt`
  extends that experiment from radius two to the complete fixed-weight codebook using the exact
  two-level principal image. Lean proves a general finite-ring mask-overlap count and candidate
  union bound, then specializes the literal `2^640`, degree-32768 ring. Every bare ternary
  difference has total order at most `2n-1`, hence at least `20905985` image bits; the complete
  signed-int64 error-difference box has fewer than `2^(65n)` elements, with no independence
  premise. Since the whole secret support is below `2^1038`, one uniform row has probability
  below `2^-18775027` of overlapping any nonidentity shifted support. This correlation-safe
  support obstruction subsumes anisotropic information-set, correlated-Fourier, and nonlocal
  cluster refinements for the actual uniform-mask low-order strata. The proof-only DSPR/NTRU
  lossy descriptor remains uninstantiated; Lean records that its complete-product total order
  must first reach `18840435 = 574n+31603` merely to escape the coarse 128-bit screen. This is a
  proof-route obstruction, not a computational attack.
- `FormalProof4FHE.RLWE.TFHEppLvl5BootRepresentation.lvl5DoubleDecompositionEquiv` closes the
  representation gap for those rows. Lean checks `2^640 = (2^16)^40` and proves that TFHEpp's
  public centering offset, signed digit conversion, coefficientwise decomposition, and
  `35 * 40 = 1400` row layout form an equivalence. For every FFT equipped with an exact
  round-trip decoder, `finiteRenyiMoment_lvl5Representation` and
  `conditionalGuessingProbability_map_lvl5EncodedRows` prove exact Renyi-moment and guessing
  invariance, including when the encoded codomain contains unreachable values;
  `idealDigitFFTEncoding` discharges that contract unconditionally for the exact complex DFT.
  The SPQLIOS/IEEE-754 source routine remains an implementation-level numerical boundary rather
  than an axiom hidden in the cryptographic theorem.
- `FormalProof4FHE.RLWE.PowerOfTwoQuadraticKDMStatistical.tvDist_quadratic_ideal_le_literalPowerOfTwo`
  formalizes the unconditional collision theorem from
  `power_of_two_quadratic_kdm_statistical.tex`. For arbitrary correlated finite secret, error, and
  leakage tapes it proves the exact gadget-independent bound
  `TV ≤ sqrt(Theta - 1) / 2`; the zero-message, quadratic-to-zero, masked-HNF, compiler, and
  relinearization statements are checked too. `PowerOfTwoCyclotomicChainRing` proves directly that
  the literal quotient `ZMod (2^kappa)[X]/(X^(2^r)+1)` is the required chain ring: parity has
  principal kernel `(1-X)`, `(1-X)^(kappa*2^r)=0`, every ideal is a power of `(1-X)`, and the
  level-`v` ideal has `2^(kappa*2^r-v)` elements. Thus the final literal-ring theorem has no
  ramification certificate premise. As in the paper, usefulness for narrow FHE noise still
  depends on numerically showing `Theta - 1` is negligible.
- `FormalProof4FHE.Regev.oneTime_abs_signedAdvantage_le_lwe_add_leftover` proves one-time Regev
  security from decisional LWE with the concrete term `sqrt(q^(n+1) / 2^m) / 2`; the finite
  leftover hash lemma and binary subset-sum two-universality are checked in
  `FormalProof4FHE.Probability.LeftoverHash`.
- `FormalProof4FHE.BlockBinary.advantage_le_randomized_ordinaryLWE_add_jointGap_capped` is the
  sharp reduction-specific block-binary-secret LWE theorem over a finite ring. It folds both
  matrix-masking sides and every row transition into one randomized narrow-LWE adversary, retaining
  cancellation, and keeps noise absorption plus extraction as one exact TV distance `Δ_joint`.
  For `k` blocks of length `ℓ`, the bound is
  `min(1, 2kℓ · Adv_narrow(B±) + Δ_joint + Adv_wide)`.
  `advantage_le_of_ordinaryLWEBounds_tight` gives the convenient uniform corollary
  `min(1, 2kℓ · ε_narrow + ε_noise + sqrt((|R|^d - 1) / (ℓ+1)^k) / 2 + ε_wide)`.
  The sharper split theorem `advantage_le_randomized_ordinaryLWE_nonlinear` uses the exact finite
  expectation of `1 - ∏ⱼ(1 - dⱼ)`, where each `dⱼ` is the translation TV of the complete summed
  narrow-error shift in sample `j`. It has no caller-supplied shift, moment, or tail hypothesis and
  is formally no worse than the older bound
  `ε_noise ≤ min(1, m·kℓ/(ℓ+1) · δ_scalar)`.
  `card_keys_with_activeBlockCount` and `probEvent_activeBlockCount_uniform_key` prove the exact
  active-block law `Pr[H=h] = choose(k,h)ℓ^h/(ℓ+1)^k`; `extractorHash_leftover_tight` checks the
  finite extraction constant.
- `FormalProof4FHE.ModularGaussian.torusDistribution` defines the ideal mod-`q` discrete Gaussian
  exactly as `D_ℤ,αq mod q`. `shiftDistance_distribution_le_valMinAbs` proves modular data
  processing through the centered integer lift, while
  `shiftDistance_torusDistribution_le_natAbs_mul_unit` reduces every centered modular shift to
  its integer magnitude times one underlying integer-Gaussian unit-shift distance. The generic
  `shiftDistance_zsmul_le` proof uses only translation subadditivity and sign symmetry. That unit
  distance is proved exactly equal to the centered Gaussian's mass at zero, and any natural
  window `W ≤ αq` bounds it by `exp(1/2)/(W+1)` using a finite normalization window. Finally,
  `convolutionDistance_le_conditionalShiftCost` proves that mixing the summed error before TV can
  only improve on revealing the shift. These are infinite-support mathematical `PMF`s. They are
  deliberately not identified with an executable `ProbComp`: an implementation has finite support
  and must be analyzed as the actual sampler used by the finite reduction.
- `FormalProof4FHE.FiniteFieldRank.rankFailure_le` proves that a uniform
  `(d + δ) × d` finite-field matrix loses column rank with probability at most
  `2 / |F|^(δ+1)`. `rankMulFailure_le_rectangular` proves the fixed high-rank
  overlap bridge used in Pietrzak's reduction.
  `GeneralizedSubspaceLWE.Adaptive.noisyInnerProduct_eq_secretAffine` also exposes every fixed
  Subspace-LWE response as a public affine function of its one hidden secret. Together with the
  full binary-key-support TFHE non-affinity theorem, this formally records why that reduction
  cannot directly generate the native secret-secret mask-block product.
- `FormalProof4FHE.SharedRandomness.zmod_advantage_eq_batch` implements Theorem 6 of ePrint
  2023/979 as an exact reduction to ordinary LWE with `m + m` samples. The scalar error-
  convolution premise is proved to lift to IID vectors.
- `FormalProof4FHE.SharedRandomness.KeySwitching.sharedIKSK_advantage_eq_fullIndependent`
  proves the no-new-assumption result for shrinking/shared-randomness IKSKs. A full-size IKSK for
  independent input and output keys encrypts gadget messages for `unusedPrefix || suffix`; its
  public suffix projection has exactly the shared IKSK distribution, which publishes only the
  suffix messages under the retained key. Both real and uniform branches, and hence advantages,
  are equal with no hybrid or IKSK-size factor.
  `sharedIKSK_hardAgainst_of_fullIndependent` states the corresponding bound-preserving transfer
  for arbitrary adversary classes closed under the explicit projection reduction; this is the
  formal no-new-security-assumption statement. `affineIKSK_advantage_eq_lwe` independently gives
  an exact whole-batch reduction to LWE under the retained key, while
  `sampleRestriction_advantage_eq` proves exact monotonicity in the number of LWE samples.
  `twoPairProjection_advantage_eq` applies two independently sampled, possibly heterogeneous IKSK
  projections jointly without a factor-two loss. The theorem does not include or make a claim
  about BRK security.
- `FormalProof4FHE.SharedRandomness.KeySwitching.blockBinarySharedIKSK_advantage_le_of_ordinaryLWEBounds_nonlinear`
  composes that lossless IKSK layer with the checked nonlinear block-binary reduction. Thus, for
  the ePrint 2023/958 retained key, the only cryptographic premises remain the same ordinary-LWE
  bounds already exposed by the block-binary theorem.
- The source-to-target ring-key extension layer now formalizes the intended shared-randomness
  construction with two nested ring keys
  `S_target = S_source || S_suffix`. A source-key TLWE/GLWE row is extended by appending zero mask
  coordinates. A full target-layout TGSW ciphertext also needs the new suffix gadget rows; these
  are constructed by externally multiplying the source BRK entry with the corresponding
  suffix-only ring-KSK row. `rowError_extendWithKeySwitch_suffix` proves the exact completion
  formula, including the KSK and external-product residuals. Applying this construction to every
  BRK entry keeps the message vector fixed and gives the formal public arrow
  `BRK(messages, S_source) -> derived BRK(messages, S_target)`.
  `tvDist_realDerivedTarget_zero_le_sourceCircular` proves that the converted target real/zero
  distance is no larger than the source one-circular BRK-plus-KSK distance. Thus conversion creates
  no new target-key circular assumption. The corresponding continuation theorem proves the same
  bound after any randomized evaluator or distinguisher uses the derived BRK. The output is
  deliberately called a derived BRK: no
  equality with a freshly sampled native target BRK is asserted. The converter uses a ring-valued
  suffix KSK under `S_source`; this is stronger public material than the standard scalar TFHE KSK.
  If only the scalar KSK is available, a separate LWE-to-GLWE packing theorem is still required.
- The full-target-message security layer instantiates the fixed-message arrow exactly as
  `BRK(KeyExtract(S_target), S_source) -> derived BRK(KeyExtract(S_target), S_target)`, with
  `S_source` a literal prefix of `S_target`. Coefficient lemmas identify the source and suffix
  coordinates inside the fixed target-message vector. The target scalar encryption key is
  `KeyExtract(S_target)`; sample extraction returns to that same key, so this variant needs no
  scalar shrinking KSK. The complete derived-BRK replacement, including an arbitrary
  secret-dependent continuation, adaptive encryption, and public FHE evaluation, is exactly one
  contextual source term. A checked suffix-only hybrid further splits it into the genuine
  source-prefix self-key replacement and an acyclic independent-suffix replacement; the refined
  adaptive and public-evaluation bounds display both terms separately. The acyclic hop is also
  definitionally identified with a generic auxiliary-input real/zero game and bounded by its
  real/uniform plus zero/uniform branches, retaining the same ring-extension table and adaptive
  input tape. For positive ring degree and one common ring-error sampler, a checked sample-
  extraction conversion now combines the complete suffix-only BRK, ring-extension table, and
  query-counted target-key input tape into one ordinary same-source-secret blocked module-LWE
  problem. Exact real branches and a common uniform endpoint bound the complete adaptive acyclic
  hop by two ordinary module-LWE advantages; the reductions never receive either secret.
  The genuine prefix hop is additionally packaged as one exact auxiliary-input CircRLWE problem
  in the PKC 2024 sense. Its real/reference KDM advantage is exactly the existing prefix term,
  and a triangle bound separates real/uniform CircRLWE from the prefix-zero/suffix-retained
  reference branch. For a public FHE continuation, that reference branch is now bounded by two
  ordinary blocked module-LWE advantages, rather than retained as another circular assumption.
  Fixed-secret native generation is exactly the degree-two monomial
  presentation: source coordinates are self-key monomials, while suffix coordinates contain an
  independent suffix coefficient. This equality is now lifted through nested-secret sampling,
  the real extension table, the complete query-counted target-key tape, and every public
  continuation. Consequently the remaining public BRK CircRLWE advantage in the full adaptive
  FHE theorem is exactly its explicit degree-two monomial presentation, not only rowwise
  equivalent at fixed keys. It is also exactly the earlier PKC-style prefix CircRLWE problem
  with the adaptive tape sampled by its experiment continuation. The matching complete-view
  recovery problem gives the solver the BRK, extension table, and tape, while keeping the latter
  two objects in the uniform-BRK recovery baseline. The associated public exact-recovery problem
  is explicit. Same-noise and narrow-search/widened-decision interfaces now carry any checked
  shifted-evaluation and guess-and-check certificate into the final adaptive theorem, producing
  exactly nested-key recovery, the certificate loss, and one ordinary blocked module-LWE term.
  The BRK-first recovery view `(BRK,(extension,tape))` is also proved exactly equivalent to the
  established tape-first view `(tape,(BRK,extension))`: the public solver conversions are inverse,
  success probabilities agree, and real-valued search hardness is equivalent. Thus both circular
  formulations share one nested-key search obligation rather than postulating two reordered
  assumptions. The same chain is now lifted to security-parameter families: negligible tape-first
  recovery, negligible checked reduction loss, and ordinary module-RLWE security imply negligible
  adaptive TFHE advantage, with distinct narrow-search and widened-decision error families.
  However, the shifted-function evaluator needed for search-to-decision—and hence any reduction
  from ordinary RLWE—remains a research obligation.
  Uniform source-BRK and fresh-input errors give exact zero
  advantage for arbitrary ring-extension errors. This is confidentiality only; for narrow
  centered-binomial or discrete-Gaussian errors, the prefix self-key term remains the circular
  research obligation. A sharper public BRK challenge retains the real extension table and
  target-key tape as auxiliary input and compares the complete target-message source BRK directly
  with a uniform BRK. After this single circular hop, one ordinary joint module-LWE reduction
  reaches a fully uniform tape, which is exactly fair for every query-bounded adversary. The
  strongest adaptive theorem is therefore one explicit degree-two monomial CircRLWE advantage
  plus one ordinary blocked module-LWE advantage, with no separate zero-BRK endpoint.
  A second, more direct FHE circular-security formulation now retains the complete real public
  evaluation material
  `(BRK(KeyExtract(S_target), S_source), Ext(S_suffix, S_source))` and challenges the
  query-counted zero-encryption tape under `KeyExtract(S_target)` against a uniform tape. The
  adaptive adversary is a public distinguisher receiving no secret, and for every query-bounded
  adversary Lean proves exact equality between its absolute honest TFHE IND advantage and this
  direct auxiliary-input CircLWE advantage. Independent XOR masks give an exactly fresh nested
  secret. A specialized PKC-style shifted-view certificate now states the remaining operation:
  publicly transform the complete `(tape, BRK, extension)` view to the widened fresh-key law.
  Same-distribution and narrow-search/widened-decision reduction theorems charge the supplied
  guess-and-check/smudging loss once. The view certificate is now narrowed to `(BRK, extension)`:
  arbitrary nested XOR masks transport the complete target-key tape exactly, with no scalar-noise
  widening, and centered-binomial noise transports the changed BRK plaintext vector exactly.
  For a rank-one source GLWE, global complementation of both nested keys transports the extension
  table exactly and bounds the complete adaptive view solely by the established BRK complement-
  shear distance. A certified discrete-Gaussian corollary gives the explicit
  `levels * degree * scalarLinearShiftBound` envelope. Every complete fresh nested mask is now
  proved uniquely equivalent to a normalized relative mask (with one fixed source anchor
  coefficient) plus one Boolean global-complement bit. Uniform relative mask and uniform anchor
  send every fixed nested key to the exact fresh-key law. A checked compiler lifts any evaluator
  for just the normalized-relative `(BRK, extension)` material through the exact target tape,
  applies the concrete anchor transform, and produces the complete PKC-style view randomizer with
  error `relativeError + globalComplementViewError`. Constructing that normalized nonconstant
  relative evaluator is still the research step; the candidate-dependent one-coordinate
  guess-and-check layer around it is checked below. A checked
  classification shows why the PKC vector-LWE rerandomizer does not instantiate it directly: at
  modulus greater than two, a normalized source-relative XOR mask has a scalar-affine ring-key
  transport only when every retained source coefficient is false. Ordinary RLWE is not assumed
  to provide the missing nonlinear transport. The additive case itself is now carried through
  the native rank-one TGSW format: after ordinary LWE key translation, the public row shear
  `(row_mask,row_body) -> (row_mask-delta*row_body,row_body)` repairs every gadget phase and
  produces the same TGSW message under `s+delta`. Its complete statistical cost is exactly the
  corresponding error shear, and the full BRK cost is bounded by the number of entries times that
  distance. Thus the gadget rows are not the obstruction. At coefficient modulus two this gives
  an exact arbitrary-XOR BRK transport under shear-invariant noise; at practical moduli the XOR
  mask is not an additive ring shift, so this boundary theorem does not remove the remaining
  evaluator. The missing endpoint is now stated without any
  source/target ambiguity. Centered-binomial symmetry first changes the BRK messages exactly from
  `KeyExtract(S)` to `KeyExtract(S')` while retaining the old source encryption key and extension
  table. The remaining certificate must map
  `(BRK(KeyExtract(S'),S_source), Ext(S_suffix,S_source))` to
  `(BRK(KeyExtract(S'),S'_source), Ext(S'_suffix,S'_source))`. This first hop adds zero error, and
  the checked compiler carries the key-shift error unchanged into the relative evaluator.
  The binary guess-and-check layer around this endpoint is now checked as well. Randomizing one
  coordinate of every target-tape row with a candidate bit preserves the complete real view for
  the correct candidate and makes the entire tape independently uniform for the wrong candidate.
  The relative/anchor compiler preserves both decision branches with the same budget
  `keyShiftError + globalComplementViewError`. Postcomposition with any public direct-CircLWE
  distinguisher and canonical sign selection therefore gives an executable one-coordinate
  predictor with success at least `(1 + advantage - 2 * budget) / 2`. This completes the
  probabilistic PKC guess/check implication, but remains conditional on constructing the displayed
  nonlinear ring-key-shift evaluator; ordinary RLWE is still not claimed to supply it.
  Running that tester once for every extracted target-key coordinate on the same public view is
  also formalized. Coefficient extraction is an explicit equivalence with the pair
  `(S_source,S_suffix)`, and a finite union bound gives a public exact-nested-key solver without
  assuming independence of coordinate events. The resulting checked narrow-search/wide-decision
  certificate yields the adaptive TFHE bound with loss equal to the sum of the one-shot coordinate
  errors. That sum is normally too large without amplification; amplification on a shared view
  needs a stronger conditional-fiber law and is not silently inferred from the averaged result.
- A separate prefix-message nested-ring optimization embeds the same converter in a complete
  TFHE cloud-key and adaptive encryption experiment. Its scalar encryption key is
  `KeyExtract(S_source)`, the
  derived BRK encrypts that fixed message vector under
  `S_target = S_source || S_suffix`, and a separate scalar suffix-only KSK returns extracted
  target-ring rows to the shared scalar key. The ring-valued extension key is consumed during key
  generation rather than published. `tvDist_continuation_eq_sourceOneCircular` proves that the
  complete derived-BRK replacement, including arbitrary secret-dependent encryption and public
  FHE evaluation, is exactly one source self-BRK replacement. The adaptive IND theorem therefore
  has one source-circular term plus the explicit BRK-zero endpoint, rather than a heterogeneous
  two-key circular term. Uniform source-BRK and fresh-input errors discharge both terms exactly
  and give zero adaptive/evaluated distinguishing advantage for arbitrary extension and scalar-KSK
  errors. This is a confidentiality-only endpoint: those uniform errors are incompatible with
  useful TFHE correctness. For narrow centered-binomial or discrete-Gaussian errors, proving the
  source one-circular term and the cross-presentation BRK-zero endpoint remains open.
- A separate coefficient-nesting model, `TFHE.Native.SharedRandomnessOneCycle`, specializes the
  ePrint 2023/958 key relation to a rank-one TFHE variant. One uniform master ring key splits
  exactly into an independent scalar
  prefix and suffix; the KSK publishes rows only for the suffix and reduces as one batch to
  ordinary binary-secret LWE. In TFHE source/target terminology, the BRK source scalar key is
  `s = prefix(S)` and the BRK target encryption key is the full ring key `S`; hence the remaining
  object is exactly `BRK_S(prefix(S))`, a genuine one-key object rather than the original
  heterogeneous two-key cycle. Its diagonal Boolean self-products are affine,
  while `offDiagonalBinarySelfProduct_not_affine` proves that every distinct-coordinate product
  with nonzero gadget remains quadratic, so shared randomness alone does not turn narrow-noise
  native TRGSW security into ordinary RLWE.
  There is nevertheless an unconditional security-only endpoint. Uniform ring-row errors make
  every fixed-message native TGSW ciphertext exactly uniform, and this equality survives an
  arbitrary continuation that receives the master secret and the correlated suffix KSK.
  `secretContinuationAdvantage_le_uniformRingError` extends the result to any finite error
  sampler at distance `delta` from uniform with loss at most
  `2 * BRKrowCount * delta`.
  `TFHE.Encryption.SharedRandomnessOneCycle` now instantiates that context with the actual
  one-time left-or-right TFHE encryption experiment. It resamples the real BRK as independent
  uniform, splits the master key into independent prefix and suffix keys, and places the complete
  suffix KSK plus adaptive input row in one unequal two-block LWE transcript. The checked final
  bound is `BRKrowCount * delta + Adv_LWE`; only one sampler-replacement side is needed for
  confidentiality. With equal KSK/input noises this is exactly ordinary binary-secret batch LWE
  on `suffixDimension * keySwitchLevels + 1` rows. Uniform or nearly uniform BRK noise is
  incompatible with the usual TFHE correctness margin, so no security-and-correctness claim for
  standard narrow Gaussian TFHE is made.
  `TFHE.Encryption.Adaptive.SharedRandomnessOneCycle` proves the reusable-key strengthening. One
  hidden bit and cloud key are reused across a sequential, query-bounded encryption oracle; later
  message pairs may depend on earlier ciphertexts. The eager-tape proof charges exactly
  `queryCount` input rows, proves the uniform adaptive branch fair, and gives the same one-BRK
  statistical cost plus ordinary batch LWE on
  `suffixDimension * keySwitchLevels + queryCount` rows in the equal-noise case. At exactly
  uniform BRK error the full adaptive advantage equals that ordinary batch-LWE advantage, and
  the adversary-class theorem derives reusable-key confidentiality from batch-LWE hardness alone:
  no circular- or KDM-security premise remains for this wide-noise variant. The asymptotic
  packaging turns this equality into negligible reusable-key advantage for polynomial-query
  adversaries and preserves it through arbitrary efficient public evaluation. It also proves the
  near-uniform version whenever the one-draw ring-error distance from uniform is negligible and
  the BRK dimensions grow polynomially.
  A concrete executable instance now uses positive-width centered-binomial BRK errors at
  coefficient modulus two. Lean proves that this ring-error sampler has total-variation distance
  zero from uniform and therefore derives reusable-key adaptive confidentiality, including after
  arbitrary deterministic public evaluation, from ordinary query-counted binary-secret batch
  LWE alone. This is a genuine no-circular-premise security theorem, but only a security-only
  boundary case: uniform error modulo two eliminates TFHE's decryption and bootstrapping noise
  margin, so it does not give correct standard TFHE parameters.
  The narrow-noise endpoint is now stated separately and exactly. The complete master ring key
  is the sole secret of an auxiliary-input CircLWE problem; the real challenge is the native
  self-circular BRK, the comparison challenge is a uniform BRK of the same type, and the retained
  side information is the real suffix-only KSK. The real challenge is proved to have the exact
  degree-two self-monomial presentation. For arbitrary finite ring noise, including the existing
  centered-binomial and discrete-Gaussian samplers, reusable-key adaptive confidentiality is
  bounded by this one native CircLWE advantage plus ordinary binary-secret batch LWE on
  `suffixDimension * keySwitchLevels + queryCount` rows. Public deterministic evaluation keeps
  the same two terms. This is the precise one-circular conditional theorem requested for usable
  narrow noise; it does not assert that ordinary RLWE proves the remaining self-quadratic term.
  A second, more literal endpoint now avoids using real-versus-uniform CircLWE as the name of the
  circular premise. Its first term is exactly
  `BRK_S(prefix(S))` versus `BRK_S(0)` under the same master key; the non-circular zero-BRK versus
  uniform-BRK encryption term and the ordinary scalar batch-LWE term remain explicit. Finite,
  asymptotic, and public-evaluation theorems all use this three-term decomposition. This prevents
  the current/shifted full-master states used inside a possible randomizer from being confused
  with TFHE's source scalar key and target ring key.
  The asymptotic lift packages this as a conventional negligible-advantage result: negligible
  one-cycle auxiliary-input CircLWE and negligible ordinary batch LWE imply negligible complete
  adaptive TFHE advantage. It includes explicit constructors for the executable centered-
  binomial family and for certified finite discrete-Gaussian ticket samplers, and the evaluated-
  ciphertext game inherits the same theorem without an additional security loss.
  The matching exact search experiment is also formalized. A solver receives the native
  self-monomial BRK and real suffix KSK and must recover the complete master key. At the uniform-
  BRK endpoint this is exactly affine shared-KSK search LWE; complete prefix/suffix recovery is
  bounded by conventional binary-secret batch search LWE under the prefix key. If both public
  transcripts are uniform, recovery is exactly `2^-(prefixDimension + suffixDimension)`. Hence
  the remaining search-to-decision task is localized to transforming the real self-circular BRK,
  rather than to the KSK or the independent guessing endpoint.
  The complete master-key randomization geometry is now checked as well. Coefficientwise XOR by
  a uniform binary ring-key mask gives an exactly fresh master key and preserves both the shared
  prefix and suffix. The public additive ciphertext correction used by the PKC 2024 CircLWE
  randomizer exactly transports a ring key by addition. At modulus two this realizes binary XOR,
  but at every modulus `q > 2` a complete characterization proves that such an additive
  implementation exists only for the all-false mask. In particular, toggling one master-key
  coefficient rules out the direct additive route for native binary TFHE. For rank-one TGSW,
  the additive transport is nevertheless complete rather than merely an LWE-row observation:
  a checked mask/body row shear repairs the key-dependent gadget phase, preserves uniform
  challenges, exposes the exact narrow-noise TV defect, and lifts pointwise through the BRK.
  The characteristic-two arbitrary-XOR specialization is exact with shear-invariant errors, but
  is a diagnostic boundary rather than a practical TFHE parameter choice. That diagnostic is now
  closed through the entire direct relative-material interface. Lean proves that every positive-
  width centered-binomial coefficient modulo two is exactly uniform, hence the complete ring
  sampler is uniform and both additive and complement TGSW error shears have zero loss. Ordinary
  additive key transport plus a public gadget-message body shift transports the ring-extension
  table, so the message-normalized pair
  `(BRK(KeyExtract(S'), S_source), Ext(S_suffix, S_source))` maps exactly to
  `(BRK(KeyExtract(S'), S'_source), Ext(S'_suffix, S'_source))`. The resulting relative evaluator,
  adaptive-tape lift, and global anchor instantiate the complete fresh-key view randomizer with
  error zero. This validates the theorem chain but supplies no usable correctness parameters:
  the positive-width noise already fills the coefficient ring, and the additive identity fails
  for nonconstant XOR masks at every `q > 2`. The checked boundary
  now also covers the larger natural scalar-affine class: inverse-scaling the public RLWE
  challenge and correcting the body transports `s` to `u*s+d` exactly, but at `q > 2` such a map
  realizes coefficientwise XOR only for the identity mask or the global-complement mask. For a
  key with at least two coefficients, arbitrary randomized selection among those surviving maps
  is formally proved not to have the fresh uniform-key law. This excludes additive and
  scalar-affine public randomization, not nonlinear homomorphic evaluation or a circular-security
  proof using a different secret representation. The surviving action is characterized exactly:
  every positive-length binary key is equivalent to one global anchor bit plus its relative XOR
  pattern, a fresh key makes those two parts independently uniform, and global complement
  refreshes only the anchor while fixing the complete relative pattern. The generic CircLWE
  `ViewRandomization` interface is now proved inconsistent with a uniform fresh-secret law when
  all of its native key actions come from this scalar-affine class. Thus the missing evaluator must
  randomize the relative pattern nonlinearly, rather than merely choose the complement bit. Full
  XOR is now factored exactly into a normalized relative-mask action followed by global
  complement, and a uniform relative mask paired with a uniform anchor is proved to recover the
  complete fresh-key law. This leaves the future evaluator with a precise `N-1`-bit nonlinear
  obligation. The final one-bit action is now lifted through the evaluation key itself. For the
  suffix-only KSK, negating each row, adding the all-one gadget table, and applying the existing
  target-key XOR transport exactly complements both source and target keys under any
  negation-symmetric scalar noise. For a rank-one TGSW/BRK, a checked public conjugation also
  complements the ring key and plaintext, but it necessarily maps every matched mask/body error
  pair to `(e_mask + d*e_body, -e_body)`. Besides the exact invariant-noise theorem, the formal
  comparison now bounds one TGSW by the total-variation defect of this shear, the full BRK by
  `lweDimension` times that defect, and the joint BRK+KSK by the same quantity: the KSK term is
  exactly zero. Under negation symmetry the defect is at most `levels` times a scalar translation
  envelope. For the certified symmetric discrete-Gaussian sampler this becomes
  `levels * degree * scalarLinearShiftBound(certificate, q / 2)`. The universal `q / 2` bound is
  unconditional but conservative, so it does not establish negligibility for standard narrow
  TFHE parameters. A second, exact route now changes the joint row-error geometry: average any
  IID narrow vector with its image under the involutive shear using one hidden uniform bit per
  TGSW entry. The resulting correlated TGSW sampler is proved equivalent in its structured and
  direct presentations and has zero complement loss through the complete BRK+KSK. With
  centered-binomial base width `eta`, every resulting row has norm at most
  `eta + degree * eta` (where `degree` is the actual ring length). Thus the shared-randomness
  variant removes the shear obstruction without uniform errors, at the cost of a modified
  correlated noise law. The relative and complement steps are now composed in the generic
  search-to-decision interface: their total-variation errors add once, while the concrete
  correlated centered-binomial BRK plus suffix-KSK complement step has error exactly zero.
  Therefore any relative-mask evaluator with error `epsilon` yields full fresh-master-key view
  randomization with error exactly `epsilon`. The suffix KSK is now removed from the relative step
  too: selectively negating its source rows and adding their gadget values transports every
  arbitrary suffix mask, while the existing target transform transports the prefix mask. Under
  centered-binomial symmetry this simultaneous full-master KSK action is exact. Conditional
  independence at a fixed master key then proves that any BRK-only relative evaluator with error
  `epsilon` yields the complete `(BRK,KSK)` relative view, and hence full fresh-key randomization,
  with the same `epsilon`. The BRK plaintext part is now removed from that obligation too. The
  shear-centered-binomial error vector is exactly invariant under complete negation, so public
  TGSW toggling transports every selected BRK message bit exactly. In the search-to-decision
  randomizer, this first installs `prefix(S')` in a BRK still encrypted under the current master
  `S`, before a supplied evaluator transports that view to the shifted master `S'`. Here `S` and
  `S'` are two same-size randomization states—not TFHE's source and target keys. The KSK, BRK
  messages, and final complement add zero error. This compiler is an internal ingredient; the
  actual one-circular security target remains `BRK_S(prefix(S))` versus `BRK_S(0)`. Constructing
  the current-to-shifted-master evaluator and completing the decision-to-search accounting remain
  the central obligations. The native CMux/key-change mismatch is now checked explicitly. For
  every TGSW row, interpreting a fixed ciphertext under a new ring secret adds the dot product of
  the secret difference with the ciphertext's homogeneous mask. Hence a correct candidate has
  target-key error equal to its existing same-key residual plus this exact defect, and the claimed
  shifted-key residual holds if and only if the defect is zero. The same equivalence survives any
  finite sequence of correct-coordinate CMux calls. Sequential guess testing therefore does not
  silently instantiate the whole relative-key evaluator; a future nonlinear construction must
  cancel or quantitatively smudge the named defect. Every signed negacyclic monomial is proved to
  act bijectively on ring masks, so merely retaining a uniformly masked row across the `+X^i` or
  `-X^i` difference of a one-coordinate binary-key flip makes its target-key phase uniform. The
  result now holds jointly for any number of independently masked rows. This does not make the
  public ciphertext table uniform: `rankOneMaskPhaseView_not_surjective` proves that retaining the
  masks leaves the mask/phase transcript on a proper deterministic graph over every nontrivial
  ring. In the augmented reduction,
  `coordinateSource_context_evalDist_eq_realPublicView` additionally proves that forgetting the
  tested secret bit gives exactly the real circular BRK+KSK+tape view. Hence the present candidate
  evaluator is an internal CircLWE search-to-decision step, not yet an ordinary-RLWE simulator for
  its own source.
- `FormalProof4FHE.LWE.AffineCircular.advantage_eq_lwe` proves an exact fixed-affine KDM theorem
  for direct fresh LWE rows. A simultaneous challenge-matrix translation absorbs every affine
  function of the encryption secret, so there is no per-row hybrid loss. By itself this does not
  cover the bilinear cross-key messages in native TGSW mask blocks.
- `FormalProof4FHE.LWE.MultiKeyAffine.advantage_eq_batch` strengthens that baseline to an arbitrary
  fixed affine clique: every fresh row under any of `users` independent binary keys may encrypt an
  affine function of all user keys. A checked master-key/mask coupling produces exactly independent
  keys, and the complete real and uniform games equal one ordinary binary-secret LWE batch with
  `users * samples` rows. This proves direct 1-circular, 2-circular, and affine-clique security;
  it still does not cover TFHE's bilinear ring/vector gadget phases.
- `FormalProof4FHE.TFHE.PackedLinearCircularRLWE.gadgetAdvantage_eq_binarySecretRLWE` checks the
  power-of-two ring analogue of the proved linear circular-LWE argument from PKC 2024. Independent
  coefficient bit planes pack bijectively into a uniform negacyclic-ring key, and one triangular
  transcript permutation produces powers-of-two gadget encryptions of every plane together with
  arbitrary zero-message rows. The resulting advantage is exactly one ordinary binary-secret
  RLWE advantage for any finite error sampler. This is a nondegenerate practical-modulus linear
  baseline, not a proof of native TFHE circular security: the TRGSW mask blocks contain degree-two
  scalar-bit/ring-bit products, and the source binary-secret RLWE assumption remains explicit.
- `FormalProof4FHE.TFHE.Circular.circularAdvantage_le_replacements` formalizes TFHE's actual
  heterogeneous evaluation-key cycle and splits real-to-zero cloud-key replacement into the
  bootstrapping-key and key-switching-key hops.
  `fullAdvantage_le_circular_add_zeroKey_add_circular` and
  `fullHardAgainst_of_circular_and_zeroKey` then compose contextual circular security on both
  challenge branches with payload security in the zero-message cloud-key game.
- `FormalProof4FHE.TFHE.Native.nativeCycleSpec` instantiates that cycle with concrete
  finite-modulus TLWE/TRGSW layouts: one TRGSW ciphertext per scalar-key bit and one direct TLWE
  row per extracted ring-key coefficient and gadget level. `TFHE.Encryption` defines the adaptive
  symmetric one-time IND-CPA game in which messages are chosen after the cloud key is visible.
- `FormalProof4FHE.TFHE.TGSW.encrypt_evalDist_eq_directEncrypt` proves that `Z + message * H` has
  exactly the distribution of fresh direct module-LWE rows carrying `gadgetPhase`; there is no
  statistical or hybrid loss. `gadgetPhase_castSucc` and `gadgetPhase_last` identify the messages
  as bilinear `-(ringKey_j * (scalarBit * gadget_l))` in mask blocks and affine
  `scalarBit * gadget_l` in the final block.
  `TFHE.TGSW.CircularBoundary.gadgetPhase_eq_affine_add_cross` records this as an exact
  affine-plus-cross-key decomposition and proves that the cross-key part vanishes at the
  zero-message cut.
  `continuationBootstrapReplacementAdvantage_eq_directBilinear` lifts this equality through the
  real key-switch key and every downstream continuation. `DirectBilinearHardAgainst` is the exact
  concrete circular-security interface; the library does not claim that ordinary LWE/RLWE proves
  this KDM assumption. See `docs/TFHECircular.md` for the boundary and roadmap.
  `TFHE.TGSW.MonomialKDM.scaledProduct_not_affine` now proves that a nonzero mask-block gadget
  product cannot be affine in the two native key coordinates. The growing centered-binomial
  family proves its first concrete TGSW gadget coordinate nonzero and specializes that
  obstruction in `nativeMaskBlockPhase_not_affine`, so the nonlinear boundary is non-vacuous for
  the exact parameters used by the security theorem. The stronger binary-support theorem permits
  arbitrary affine coefficients on every bit of both complete native key vectors and still rules
  out the selected cross coordinate. The full-support specialization additionally embeds an
  arbitrary binary ring polynomial and proves the complete selected mask-block function
  non-affine in every ring-key coefficient and scalar-key bit, matching the input model of affine
  LWE-KDM results.
  Conversely,
  `gadgetPhase_eq_expandedGadgetPhase` factors the complete normalized phase through the explicit
  degree-two coordinates `ringKey_j * scalarBit_i`, after which every row message is a public
  linear projection and gadget scaling. The resulting monomial BRK sampler is exactly—not merely
  statistically—equal to the direct native sampler, and
  `Asymptotic.MonomialKDM.adaptiveSecurityGame_secureAgainst_iff_directBilinear` lifts this
  identification to polynomial-query adaptive families. This matches the algebraic monomial-lift
  viewpoint of Brakerski--Goldwasser--Kalai while explicitly not importing their transformed
  encryption scheme's KDM theorem into native TFHE.
  In particular, the native assumption is not security for an arbitrary degree-two polynomial
  KDM family. It is only the fixed outer-product table `ringKey_j * scalarBit_i`, at the public
  gadget scales and row positions used by TRGSW. Adding `scalarBit_i * gadget_l` to a uniform
  mask (nonce) coordinate does not remove that product: after renaming the translated mask to
  `a'`, the corresponding body has phase
  `b - <a', ringKey> = error - scalarBit_i * gadget_l * ringKey_j`.
  Thus nonce placement explains the restricted monomial shape, but it does not reduce the intact
  narrow-noise BRK to affine KDM or ordinary RLWE.
  `TFHE.TGSW.MonomialKDM.FullTable.phase_selfMaskRowCombination_eq` further records the joint-table
  qualification: one GSW entry is rank one, but a complete self-BRK contains every pairwise
  monomial. A public linear combination of its fixed-level mask rows has phase equal to any
  weighted quadratic form plus the exact combined row error. The native specialization
  `FullBRKQuadraticSpan.extractedOuterProduct_coefficient` checks coefficient by coefficient that
  the ring-valued table contains the corresponding Boolean products. Hence the native game is
  narrower than a general adaptive quadratic-KDM oracle, while still spanning all static
  quadratic forms once the full self-key table is public.
  The Boolean refinement
  `selfQuadraticForm_embedBinarySecret_eq_diagonal_add_offDiagonal` splits every such form exactly
  into an affine diagonal term, using `s_i^2 = s_i`, and a square-free off-diagonal term containing
  only `s_i * s_j` for `i != j`. The matching phase theorem tracks the same split together with
  the exact combined row error. Thus the irreducible nonlinear premise is smaller than general
  degree-two KDM, but it still contains every off-diagonal pair exposed by a practical full BRK.
  `CoefficientAffineCircularRLWE` now checks the missing qualification. Its bundled
  `coefficientTransfer` is the elementary coefficient-linear map `E_(i,i)`, and
  `coefficientEquiv_diagonalCrossAtDegree_rankOne` proves that the actual native diagonal cross
  coordinate is exactly this projector. `rightNegacyclicMulLinear` proves that subsequent public
  gadget multiplication is coefficient linear, and the mask/body product theorems identify the
  native terms respectively with `rightMul ∘ E_(i,i)` and `rightMul ∘ E_(0,i)`. In every
  nontrivial coefficient ring and ring degree at least two,
  `nativeFirstDiagonalCross_not_ringMultiplicationOnBinary` proves that no fixed public
  negacyclic polynomial realizes the underlying projector by multiplication, even only on
  Boolean secrets. Thus the diagonal lies in a precisely defined coefficient-affine
  structured-LWE class, but the ordinary rank-one RLWE challenge translation cannot discharge
  it. A compatible
  coefficient-linear/circulant circular theorem is still required. The same module packages the
  exact diagonal-only BRK versus zero-BRK experiment as a fixed-auxiliary-input circular-RLWE
  problem retaining the real shared KSK. Its real and zero games are definitionally the existing
  cloud-key games, and the checked refined bound is
  `Adv_one-cycle <= Adv_square-free + Adv_coefficient-affine-CircRLWE + Adv_zero-BRK-LWE`.
  The native shared-randomness one-cycle game now has the matching exact game split.
  `SharedRandomnessOneCycle.SquareFreeSecurity.generateBootstrappingKey_evalDist_eq_split` rewrites
  the honest BRK as diagonal plus square-free phases without changing its distribution, and
  `oneCircularAdvantage_le_squareFree_add_diagonal` proves
  `Adv_one-cycle <= Adv_square-free + Adv_diagonal`. The first term removes exactly the fixed
  distinct-coordinate outer-product table; the second removes the remaining coefficient-affine
  diagonal table. This is the precise restricted premise to attack—neither arbitrary degree-two
  KDM security nor an unqualified appeal to ordinary RLWE is inserted.
  The same split now holds for the stronger secret-dependent continuations used by the adaptive
  encryption experiment, not merely for public cloud-key distinguishers. The asymptotic theorem
  composes it all the way through reusable encryption and arbitrary public deterministic FHE
  evaluation:
  `Adv_TFHE <= Adv_square-free-table + Adv_coefficient-affine-CircRLWE + Adv_batch-LWE`.
  Thus the former generic circular-RLWE premise has been eliminated from the theorem statement,
  while the two exact native research assumptions have not been claimed to follow from ordinary
  LWE or RLWE.
  A separate security-only route now removes both native circular components statistically for a
  sufficiently shift-tolerant certified discrete-Gaussian BRK sampler. Each exact TGSW gadget
  phase is moved into its independently sampled body error; data processing and the finite-product
  hybrid charge one additive translation distance per native BRK row. This is proved for the
  complete self-key message and arbitrary secret-dependent continuations, so it simultaneously
  covers the diagonal and square-free tables. Polynomial layout growth and negligible certificate
  error together with negligible `(q/2)/(window+1)` make the complete real-versus-zero KDM loss
  negligible. The generic finite-group averaging theorem
  `FiniteProduct.tvDist_uniform_le_of_addShiftDistance_le` additionally proves that a
  never-failing sampler stable under every additive shift is close to exact uniform. Applied to
  the same certified Gaussian, it removes the zero-BRK endpoint as well. The strongest adaptive
  encryption and public-evaluation theorems therefore retain only ordinary batch LWE, with no
  circular/KDM or auxiliary zero-BRK hardness premise. This does not claim correctness: the
  necessary Gaussian width may be too large for bootstrapping correctness.
  `SharedRandomnessOneCycleConcreteWideGaussianSecurity` now instantiates every numerical premise.
  It takes `q = (2N)^(lambda+1)`, relative Gaussian width `alpha = 2^lambda`, hence integer
  standard deviation `q * 2^lambda`, and uses the same quantity as the universal translation
  window. A rounded finite ticket table with denominator `q * (q+1) * 2^lambda` has compilation
  error at most `2^-lambda`; the modulus-scaled inverse-window term is also at most
  `2^-lambda`. The checked polynomial layout absorbs both losses. Consequently the literal
  real-self-BRK KDM game, its adaptive form, full reusable-key encryption, and arbitrary public
  deterministic FHE evaluation are secure assuming only ordinary query-counted batch LWE. The
  rounded table is currently a noncomputable existence witness, and this deliberately enormous
  noise is not claimed to preserve TFHE correctness or yield a practical implementation.
  The supplied GSW papers do not close either term. The original GSW paper proves its leveled
  scheme from LWE but explicitly invokes circular security for bootstrapping. Gay--Pass prove
  non-circular shielded-randomness-leakage security of GSW from LWE, while their encrypted-key
  cycle is a separate 2-circular SRL conjecture. The current GG-GSW manuscript explicitly marks
  its principal IND-CCA1 proof as incorrect, so it is not used as a circular-security reduction.
  `LWE.AuxiliaryInput` now adds the PKC 2024-style real/zero/uniform fixed-side-information
  interface. `TFHE.MonomialKDMAuxiliaryInput` instantiates it with the exact paired native keys,
  monomial BRK, uniform native BRK type, and retained real KSK; its real and zero games are
  definitionally the existing monomial games. The two triangle bounds prove that native
  monomial-KDM and real-versus-uniform auxiliary-input CircLWE are equivalent modulo the explicit
  zero-message-versus-uniform side-information term for arbitrary continuations. The equivalence
  is lifted to adaptive negligible-function games by `AsymptoticAuxiliaryInputCircularLWE`.
  `TFHE.AuxiliaryInputZeroSecurity` then handles the continuations induced by query-bounded
  adaptive TFHE adversaries: a zero BRK with uniform ring errors is exactly uniform, and a fair
  hidden-bit intermediate bounds the zero-side term by the actual-BRK-context and
  uniform-BRK-context joint-LWE games. Equal scalar noises flatten both exactly to ordinary
  binary-secret batch LWE. Thus this zero-side obligation is no longer an independent assumption,
  while real-versus-uniform auxiliary-input CircLWE remains the named circular assumption; no
  ordinary LWE/RLWE reduction for that remaining game is claimed.
  `TFHE.ScalarSecretRandomization` proves the next search-to-decision prerequisite for the
  executable centered-binomial model: every fixed binary mask transports the scalar key through
  both native evaluation-key components, and the same public bijection preserves the joint real
  BRK+KSK and uniform-BRK+real-KSK endpoint distributions exactly. Sampling the mask uniformly is
  further proved to yield a fresh uniform scalar key and its corresponding view, with the ring key
  held fixed. The TGSW step uses exact centered-binomial negation symmetry, while the KSK affine
  transform preserves its errors. `LWE.AuxiliaryInputSearch` and
  `TFHE.AuxiliaryInputCircularSearch` define exact paired-secret recovery from the public BRK+KSK
  view and prove that experiment equal to the existing native monomial real game; the scalar-mask
  coupling is connected directly to this search view. `TFHE.ScalarMaskCandidateView` now audits
  that coupling in the actual coordinate-recovery experiment: after averaging over the uniformly
  sampled native scalar and ring keys, every fixed public scalar mask preserves the complete real
  BRK+KSK endpoint exactly. It packages the result as an averaged candidate transformer with zero
  correct-view error and wrong-view error exactly `TV(realPublicView, uniformPublicView)`. Because
  this transform ignores the candidate, `candidateCheckGap_toCandidateCheck_eq_zero` proves that
  postcomposition with any public distinguisher has candidate gap exactly zero. Thus scalar
  rerandomization is a checked prerequisite, but cannot by itself replace a candidate-dependent
  freshness step.
  `TFHE.KeySwitchCandidateRandomization` and `TFHE.KeySwitchFirstCandidateView` now close one exact
  candidate-dependent route on the opposite edge of the cycle. They add a fresh vector to one
  scalar-coordinate row of every KSK challenge and add the proposed bit times that vector to the
  bodies. The true bit preserves the complete real KSK distribution; for the opposite bit, the
  embedded difference is `+1` or `-1`, so an explicit inverse proves that the complete KSK is
  exactly uniform over every finite commutative ring. Keeping the real BRK fixed, the resulting
  candidate gap equals the real-BRK/real-KSK versus real-BRK/uniform-KSK decision advantage.
  The existing coordinate union bound and centered-binomial KSK decoder then give a checked
  paired-secret recovery lower bound. `TFHE.KeySwitchFirstSearchToDecision` packages this endpoint
  as a generic auxiliary-input problem with the KSK as challenge and the real BRK as side input.
  It proves that swapping the sampling and argument order preserves both public games and native
  paired-search success, then constructs a checked `Reduction`. Its additive loss is exactly
  `max 0 (advantage - oneShotLowerBound.toReal)`, so native paired-search hardness transfers to
  KSK-first decision hardness without concealing the coordinate union-bound deficit. This is a
  complete one-shot KSK-first search-to-decision certificate, but its loss is not claimed
  negligible at production dimensions. It does not make the BRK uniform, prove the original
  BRK-first auxiliary-input CircLWE endpoint, or derive circular search hardness from ordinary
  LWE/RLWE.
  `Probability.MajorityAmplification` and `TFHE.KeySwitchFirstFreshView` now provide the stronger
  fresh-view route needed to improve that loss. A generic whole-vector theorem repeats
  independently sampled trials inside each majority tree while keeping one hidden-key fiber; it
  charges `∑ᵢ amplifiedErrorᵢ` plus one `averageFiberError / threshold` term, rather than paying the
  same bad fiber once per coordinate. For native TFHE, an opaque sampler handle returns fresh
  BRK+KSK views under one fixed key pair. The fixed-secret candidate laws prove that every scalar
  coordinate has the same conditional error, whose average is exactly
  `ofReal((1 - keySwitchDecisionAdvantage)/2)`. Centered-binomial KSK completion then preserves
  amplified paired-key success exactly, and fresh-view search hardness transfers with an explicit
  schedule-dependent loss. This premise is deliberately named separately: no theorem identifies
  fresh-view search hardness with single-evaluation-key search hardness or ordinary LWE/RLWE.
  `TFHE.KeySwitchFirstFiniteView` removes the unrestricted-query ambiguity for the concrete
  reduction. At one common amplification depth `r`, its paired-search challenge samples exactly
  `lweDimension * 3^r + 1` independent native BRK+KSK views under one hidden key pair: one ternary
  majority tree per scalar coordinate and one final KSK for ring-key completion. A deferred-
  sampling theorem proves that the finite-batch solver has exactly the fresh-view solver's output
  distribution, and finite-batch search hardness transfers to KSK-first decision hardness with
  the same explicit loss. This makes the stronger premise finite and auditable, but does not
  derive multi-view native circular-search hardness from ordinary LWE/RLWE or from one evaluation
  key.
  The KSK-first cloud-key composition is also checked end to end. It follows the exact hybrids
  real/real, real/uniform-KSK, zero/uniform-KSK, and zero/zero. Uniform scalar errors make a
  zero-message KSK exactly uniform, so the two post-search hops reduce to two conventional ring
  batch-LWE advantages and one conventional scalar batch-LWE advantage. The resulting theorem
  derives native cloud-key circular security from finite-batch paired-search hardness, its
  explicit amplification loss, and those ordinary LWE assumptions. It does not silently promote
  the bounded multi-view search premise to ordinary LWE/RLWE, and it does not yet include a
  secret-dependent adaptive encryption transcript.
  `LWE.AuxiliaryInputSearchToDecision` then
  formalizes a quantitative paper-aligned boundary: narrow and widened views, probabilistic
  shifted evaluation/smudging with one explicit TV loss, a public-distinguisher-to-search-solver
  certificate, and the additive hardness transfer theorem. `TFHE.AuxiliaryInputSearchToDecision`
  instantiates the scalar randomizer with zero loss. `TFHE.KeySwitchRecovery` proves that a known
  scalar key recovers every extracted ring-key bit from any supported centered-binomial real KSK
  under an explicit gadget margin, and `TFHE.AuxiliaryInputPairedRecovery` proves exact equality of
  scalar-only and completed paired-search success. Consequently
  `ScalarSecretReduction.toPairedSecretReduction` constructs the full paired certificate without
  extra loss. `TFHE.ScalarCoordinateRecovery` then constructs a scalar solver from randomized
  per-coordinate tests and proves the whole-key error bound `Pr[failure] ≤ ∑ᵢ εᵢ` without assuming
  independence of the shared public view. `CoordinateSecretReduction.toScalarSecretReduction`
  connects that theorem to the existing scalar boundary. `Probability.BinaryGuessCheck` now gives
  the executable per-coordinate tester and proves its exact one-shot error formula.
  `CandidateViewTransformer` isolates the native scheme law needed by that tester: the correct
  candidate must transform the correlated view to a fresh real BRK+KSK view, while the wrong
  candidate must produce uniform BRK plus real KSK. Under those laws the coordinate error is
  exactly `(1 - publicAdvantage) / 2`, and
  `CandidateViewTransformerReduction.toScalarSecretReduction` packages the conditional one-shot
  path to scalar recovery. `Probability.MajorityAmplification` additionally implements an
  executable majority-of-three tree with exact error recurrence
  `e ↦ e²(1 + 2(1 - e))`. Its shared-context theorem samples BRK+KSK once and is therefore driven
  by a support-wise conditional error bound. `TFHE.PointwiseCandidateView` states that law and now
  proves its overlap obstruction: if the same fixed public context supports both hidden bits, the
  statistical real/uniform distance is at most the sum of the two claimed pointwise errors.
  `TFHE.AveragedCandidateView` records the strictly weaker averaged law and proves the sound
  threshold fallback `amplifiedError(rounds, τ) + averageError/τ`; the second term prevents an
  averaged gap from being misused as per-context freshness. The widened reduction now carries
  that thresholded error through the scalar-key union bound, exact centered-binomial KSK
  completion, and final search-hardness transfer. Meanwhile,
  `TFHE.WidenedAuxiliaryInputSearchToDecision` completes the narrow-centered-binomial to arbitrary-
  wide-sampler accounting: it subtracts the two conditional TV errors from the target decision
  advantage, amplifies coordinatewise, applies the union bound and KSK completion, and exports the
  final additive hardness transfer theorem.
  The averaged transformer now also exposes a strictly one-shot endpoint. Its executable tester
  predicts one selected scalar-key coordinate from one narrow augmented `(BRK, KSK, tape)` view,
  and the checked finite inequality is

  ```text
  public augmented CircLWE advantage
    <= selected-coordinate prediction bias + correct-view error + wrong-view error.
  ```

  There is no repetition, threshold, bad-context division, coordinate union bound, or correctness
  premise in this theorem. The asymptotic lift turns negligible prediction bias and negligible
  selected-coordinate statistical errors into public augmented CircLWE security. This is the
  preferred security-only boundary when the averaged whole-key amplification loss cannot be
  shown negligible. The exact scalar-key randomizer does not invalidate that caution: it holds
  the ring key fixed and transports one sampled cyclic evaluation-key view, rather than sampling
  independent full BRK--KSK contexts. The unused effective-gap premise has therefore been removed
  from the averaged reduction interfaces; the pointwise amplifier retains its genuinely needed
  support-wise gap hypothesis.
  `TFHE.ConditionalSmudging` proves pointwise TLWE/TGSW body-smudging bounds for any executable
  finite wide sampler. `TFHE.NativeConditionalSmudging` sums the translation costs across the
  exact native BRK+KSK layout. `TFHE.NativeResidualCandidateView` turns exact correct/wrong
  residual normal forms into the complete pointwise transformer automatically and now also has a
  genuinely averaged residual certificate: the normal-form laws need hold only after sampling the
  original hidden bit and public context, while support-wise fresh-evaluation residual costs are
  integrated soundly. Its reduction adapter carries those averaged laws through thresholded
  amplification, the scalar-key union bound, exact KSK completion, and narrow-search hardness.
  `TFHE.AsymptoticNativeResidualCandidateView` lifts the resulting inequality to negligible-
  function games: public CircLWE advantage is bounded by generated paired-search success plus the
  explicit residual/amplification loss. It also proves exact equality with the existing native
  CircLWE carrier on continuations that ignore both secret arguments. The growing centered-
  binomial family selects KSK gadget level one, proves its centered distance is exactly `2N`,
  discharges the width-`λ+1` recovery margin, and exports the corresponding public CircLWE and
  public-continuation monomial-KDM security theorems.
  `TFHE.InternalProduct` now defines native rowwise TGSW internal product and CMux and proves their
  exact phase/residual normal forms: data-row error, decomposition residual, weighted control-row
  error, and (for CMux) the retained false-branch error are all explicit. These algebraic theorems
  now also prove complete-ciphertext zero/one endpoints: exact gadget decomposition reconstructs
  the whole TLWE row, and CMux is the selected branch plus one explicit homogeneous-control
  internal product. They deliberately make no distributional freshness claim about that
  perturbation. The scalar-only audit proves that masking without candidate-dependent evaluation
  has exactly zero candidate gap.
  `TFHE.NativeShiftedCandidateEvaluator` now implements the construction-specific step itself:
  it toggles the selected TGSW control by the candidate, exactly decomposes every branch
  difference, applies native CMux pointwise to a complete BRK, and canonically writes every
  arbitrary public BRK as its declared binary gadget message plus a homogeneous remainder. It
  proves an exact correct-candidate phase law whose residual is the actual digitized-CMux
  computation, with no structural-generation premise. It also proves, as equalities of complete
  ciphertexts, that every correct whole-BRK output is its source entry plus the named internal-
  product perturbation and every wrong output is its fresh branch entry plus that perturbation.
  The proof includes the explicit coherence bridge between the executable and proof-facing `Rq`
  operation dictionaries. `TFHE.NativeAdaptiveShiftedCandidateEvaluator`
  samples a uniform scalar mask and uniform true-branch BRK, transports the complete
  `(BRK, KSK, tape)` context and candidate coherently, and fixes this executable map in its
  certificates with no abstract transform field. The exact uniformized experiment is now proved
  equal to the existing uniform public view, including the transported KSK and adaptive tape.
  Conditioning the selected mask coordinate on a requested target bit is proved to be an exact
  reparameterization of the original uniform mask, and the equality remains exact after adding
  the independent uniform true-branch BRK. This gives a total concrete sampler for the computed
  correct-branch residual, together with its rowwise phase theorem, at zero conditioning loss.
  Pointwise branch bijectivity is retained as an exact sufficient condition, while the usable
  `DirectStatisticalCertificate` charges the actual mask-averaged branch-map TV distance and
  therefore permits rare rank loss. It also exposes the concrete evaluator's averaged
  correct-view distance directly, so security does not depend on an unjustified fixed residual
  representation. `SampledResidualCertificate` supplies the preferred smudging route: evaluator
  coins may sample a residual correlated with the fresh secret, and explicit totality plus a
  support-wise translation bound imply the direct correct-view distance. The deterministic
  `StatisticalCertificate` is proved to be its probability-one special case. The fully fixed
  `ConcreteStatisticalCertificate` now splits the only remaining evaluator losses into
  output-mask/error-law freshness for that concrete residual experiment, support-wise smudging,
  and the mask-averaged wrong-branch distance. `TFHE.NativeShiftedResidualBounds` now identifies
  the correct residual exactly as one retained source-row error plus the digit-weighted error of
  the zero-message control. Secret-bit toggling preserves every control-row error up to sign, so
  it creates no second support obligation. The executable digit and convolution bounds give both
  a sharp centered-binomial budget for coupled keys and a sound `q / 2` fallback for an
  independent fresh-secret boundary. `TFHE.NativeShiftedDiscreteGaussianBounds` converts either
  budget into a coefficientwise translation bound for the certified modular discrete-Gaussian
  sampler and discharges `smudgingCost_le` support-wise for the concrete residual sampler. Its
  sharper route costs, per scalar coefficient, twice the sampler-certificate error plus the
  residual bound times a single integer-Gaussian unit-shift TV distance; the latter is exactly
  the mass at zero and has the checked finite-window bound `exp(1/2)/(W+1)`. It does not sum over
  all bounded residues. `TFHE.AsymptoticNativeShiftedDiscreteGaussianBounds` now proves that this
  complete correct-side loss is negligible when the native dimensions, gadget, and residual
  grow polynomially, the ticket-certificate error is negligible, and a checked window of size
  `2^λ` fits below `αq`. It also proves closure under a negligible normal-form error and
  polynomially many uses. The growing centered-binomial dimensions have a concrete polynomial
  growth witness, while the theorem explicitly does not claim that their present polynomial
  modulus supports the exponential Gaussian window. The universal bound is intentionally
  conservative. The coupled endpoint now retains the complete
  source key pair, regenerates only the residual-bearing BRK under the masked scalar key, proves
  that its monomial comparison is exactly the ordinary augmented real view, and carries the sharp
  `eta` envelope through averaging. Its direct-certificate adapter leaves only
  output-mask/error-law freshness and the wrong-branch law as construction premises.
  The remaining BRK-first construction work is therefore output-mask/error-law freshness,
  a parameter family compatible with the exponential smudging window, the
  canonical one-control wrong-branch estimate, and narrow paired-search hardness. The public augmented route
  now carries the complete
  bounded input tape as auxiliary input instead of passing either hidden key to a continuation.
  Exact XOR transport preserves the real and uniform-BRK endpoints, and the actual adaptive
  real-to-zero hop is exactly this public augmented KDM game. Its zero branch is discharged by two
  ordinary joint-LWE games, so public augmented CircLWE is the sole circular premise in the finite
  and asymptotic adaptive theorems. The retained KSK also completes any augmented scalar solver to
  paired-key recovery with no loss under the centered-binomial decoding margin. The augmented
  candidate-view frontend now averages over the complete `(BRK, KSK, tape)` source, applies the
  sound threshold/bad-context amplification bound, unions all scalar-coordinate errors, and feeds
  exact residual-smudging normal forms into paired recovery. What remains is to prove the concrete
  native evaluator's output-mask/error-law freshness for the explicit perturbation, bound the
  canonical-control statistical rank/freshness distance and residual loss negligibly, and supply augmented paired-
  search hardness. No secret-aware batching or ciphertext-algebra bridge remains.
  The exact KSK-first alternative above isolates the obligation to the other edge rather than
  leaving both coordinate transformations open.
- `FormalProof4FHE.TFHE.Native.BootstrapCutSecurity.cutBootstrapReplacementAdvantage_le_two_batchModuleLwe`
  proves the complementary post-cut result: with the KSK messages already zero, replacing the
  native BRK by zero-message rows costs at most two ordinary parallel binary-secret module-LWE
  advantages. Sampler regrouping and uniform gadget translation are exact.
  `TFHE.Encryption.CutCycleSecurity.oneTimeCutBootstrapReplacementAdvantage_le_two_parallelModuleLwe`
  carries the same result through the adaptive one-time challenge. Together with the existing
  KSK-after-zero-BRK reduction, both second hybrid hops are standard LWE/module-LWE; only the
  intact-cycle first hop remains circular.
  `LWE.ParallelBatch.advantage_eq_batch` subsequently flattens those equal-size batches exactly,
  and `cutBootstrapReplacementAdvantage_le_two_batchModuleLwe` states the final result using two
  conventional binary-secret ring batch-LWE problems with
  `lweDimension * TGSW.rowCount` samples.
  `TFHE.Circular.continuationCircularAdvantage_le_keySwitchFirst_add_bootstrapAfter` formalizes
  this opposite ordering in the common game layer. The two `...add_postCuts` theorems and their
  concrete `keySwitchFirstReplacementAdvantage_le_directBilinear_add_postCutLwe` converse pair
  prove that BRK-first direct-bilinear KDM and KSK-first intact-cycle security are equivalent up to
  the checked post-cut LWE terms. `Encryption.Adaptive.CutCycleSecurity` proves the same converse
  pair for the complete sequential oracle, and
  `Asymptotic.CutCycleSecurity.adaptiveFirstHop_secureAgainst_iff` lifts it to negligible
  polynomial-query adversary families. The alternative-order end-to-end result is
  `abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_jointLwe`.
  `NativeIntactCycleKDMHardAgainst` names that exact scheme-specific first-hop premise, and
  `oneTimeHardAgainst_of_nativeIntactCycleKDM_and_batchLwe` composes it with explicit hardness
  bounds for both conventional ring batch-LWE reductions and the zero-cloud joint-LWE reduction
  into an adversary-class one-time TFHE security theorem. In the equal-noise setting,
  `oneTimeHardAgainst_of_nativeIntactCycleKDM_and_standardBatchLwe_same_noise` leaves only the
  named circular premise plus three conventional batch-LWE assumptions.
- `FormalProof4FHE.TFHE.Encryption.Security.abs_signedAdvantage_real_le_bootstrap_add_jointLwe`
  proves the one-time TFHE encryption bound. The honest advantage is at most the
  contextual structured-TRGSW bootstrapping-key replacement cost plus one heterogeneous
  shared-secret binary-LWE advantage containing every key-switch row and the fresh challenge row.
  If key-switch and input errors use the same sampler,
  `abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_same_noise` reduces that term exactly to
  ordinary binary-secret batch LWE with `((ringRank * degree) * keySwitchLevels) + 1` samples.
  Distinct noise samplers remain explicit unless a relation is supplied.
  `abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_input_convolution` proves that when the
  input error is the KSK error plus a total independent widening sampler, the same ordinary
  batch-LWE conclusion holds with the KSK error distribution. The underlying generic theorem is
  `LWE.TwoBlock.heterogeneous_advantage_eq_batch_of_convolution`.
  `oneTimeHardAgainst_of_directBilinear_and_jointLwe` and its equal-noise batch-LWE specialization
  compose explicit bounds for both remaining assumptions into a complete conditional one-time
  TFHE security theorem for an arbitrary reduction-closed adversary class.
- `FormalProof4FHE.TFHE.Encryption.MultiQuery.abs_signedAdvantage_real_le_bootstrap_add_jointLwe`
  lifts the same native game to a fixed batch of `queryCount` left-or-right challenges selected
  after the cloud key is visible. The whole vector uses one hidden challenge bit and one scalar
  key. Its reduction places every KSK row and exactly `queryCount` challenge rows in one
  heterogeneous LWE transcript; when the scalar noises agree,
  `abs_signedAdvantage_real_le_bootstrap_add_batchLwe_of_same_noise` flattens this exactly to
  ordinary binary-secret batch LWE on
  `((ringRank * degree) * keySwitchLevels) + queryCount` rows. The BRK/circular term is paid once
  for the whole continuation, and `hardAgainst_of_directBilinear_and_batchLwe_same_noise`
  packages the adversary-class conditional theorem. This remains the simpler fixed-batch
  multi-challenge interface; the sequential strengthening is described next.
- `FormalProof4FHE.TFHE.Encryption.Adaptive.abs_signedAdvantage_real_le_bootstrap_add_jointLwe`
  formalizes a query-bounded sequential left-or-right encryption oracle. The adversary is an
  `OracleComp` that sees one cloud key and may choose each new message pair from all earlier
  ciphertexts and its internal uniform randomness. The proof installs an eager tape of exactly
  `queryCount` LWE rows, proves one source-row query per encryption query, and proves that adaptive
  translations of a uniform tape are bit-independent. The final circular term is still paid once,
  while equal scalar noises give ordinary binary-secret batch LWE on
  `keySwitchSamples + queryCount` rows. The corresponding adversary-class theorem is
  `hardAgainst_of_directBilinear_and_batchLwe_same_noise` in the `Encryption.Adaptive` namespace.
- `FormalProof4FHE.TFHE.Encryption.Adaptive.CutCycleSecurity.abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_jointLwe`
  extends the KSK-first cut-cycle proof to that full sequential oracle. The cloud key is replaced
  once for the entire adaptive transcript: one exact native intact-cycle KDM term, two ordinary
  binary-secret ring batch-LWE terms, and the query-counted zero-cloud joint-LWE term bound the
  honest advantage. `hardAgainst_of_nativeIntactCycleKDM_and_batchLwe` packages the corresponding
  adversary-class theorem. With equal scalar noises, the joint endpoint is exactly an ordinary
  scalar batch-LWE problem on `keySwitchSamples + queryCount` rows.
- `Encryption.Adaptive.KeySwitchFirstFiniteView.hardAgainst_of_finiteSearch_and_lwe` replaces that
  intact-cycle continuation term by a concrete finite augmented-search premise. Each public view
  contains a real BRK, a real KSK, and a zero-message input tape under the same fixed scalar key;
  common-fiber majority amplification uses exactly `lweDimension * 3^rounds` such views. The full
  bounded adaptive advantage is then controlled by finite scalar-search success, its explicit
  amplification loss, two ordinary ring batch-module-LWE bounds, and one ordinary scalar
  batch-LWE bound on exactly `queryCount` input rows. The remaining nonstandard premise is the
  bounded augmented native search problem, not an unmodeled secret-dependent continuation and
  not a claimed consequence of ordinary LWE/RLWE.
- `Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.secureAgainst_of_universal_finiteSearch_and_lwe`
  lifts that theorem to security-parameter families without a separate amplification-residual
  premise. A `PolynomialViewSchedule` certifies that the exact
  `lweDimension * 3^rounds` augmented views remain polynomially bounded. The balanced threshold
  `(2 - advantage)/4` gives
  `decision ≤ 2·search + 2·summedMajorityError`, and the capped form
  `balancedResidual = min(summedMajorityError, decision / 2)` also handles zero-advantage
  families. Quantitative majority bounds now choose, for each exponent in the definition of
  negligibility, a logarithmic-depth schedule whose `3^rounds` view cost is polynomial and whose
  dimension-scaled capped residual is inverse-polynomially smaller than that exponent. Thus
  security for augmented scalar search under every polynomial-view schedule, two ordinary ring
  batch-module-LWE games, and the ordinary input-tape batch-LWE game imply negligible adaptive
  TFHE advantage. The centered-binomial specialization discharges key-switch sampler totality
  and the dimension-growth obligation exactly. The only remaining nonstandard cryptographic
  premise in this route is universal polynomial-view augmented native search hardness; it is
  still explicit and is not claimed to follow from ordinary LWE/RLWE. Fixed-schedule residual and
  coordinate-error variants remain available as lower-level interfaces.
- `Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.secureAgainst_of_universal_batchCircular_and_lwe`
  removes the universal augmented-search assumption from the public theorem statement. For any
  finite solver, exact scalar-key recovery from the real augmented batch is at most the complete
  real-versus-independent batch circular advantage plus exactly
  `2^(-lweDimension)`. If `lweDimension ≥ securityParameter`, the latter function is negligible.
  Composing this fact with the universal logarithmic schedule proves adaptive TFHE security from
  full-transcript circular decision security and the three ordinary post-cut LWE games. The
  centered-binomial family and the exact-rotation `q = 2N` family instantiate this endpoint. This
  is the stronger full-transcript decision normalization.
- `Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.secureAgainst_of_universal_bootstrapCircular_flatSearchLwe_and_lwe`
  gives the sharper factored endpoint. The circular game replaces only the polynomial same-secret
  batch of BRKs and retains the real KSK and input tapes. At its uniform-BRK endpoint, exact
  majority-tree flattening and search-preserving transcript equivalences compile every retained
  KSK row into one scalar-LWE block and every input row into a second block under the same hidden
  binary key. Thus augmented recovery is bounded by BRK-only circular advantage plus one
  conventional heterogeneous two-block scalar search-LWE success probability. If the two scalar
  error samplers coincide, the blocks concatenate exactly into one ordinary batch. This
  equal-noise identity is lifted to asymptotic security by
  `secureAgainst_of_universal_nativeCircular_ordinarySearchLwe_and_lwe`: the centered-binomial
  wrapper records sampler equality explicitly, and the exact-rotation family discharges it from
  its definition. Its scalar-side premise is therefore one conventional combined-batch search-LWE
  game, rather than the heterogeneous two-block interface.
  `LWE.AuxiliaryInput.Batch.advantage_eq_card_mul_randomHybrid` and
  `KeySwitchFirstFiniteView.bootstrapBatchCircularAdvantage_eq_viewCount_mul_nativeCircularLwe`
  now close the single-view/multi-view bridge exactly: one uniformly selected native CircLWE
  challenge realizes an adjacent BRK hybrid, so the complete batch advantage is precisely
  `viewCount` times that one-challenge advantage. The schedule already proves `viewCount`
  polynomial, hence
  `secureAgainst_of_universal_nativeCircular_flatSearchLwe_and_lwe` handles arbitrary scalar
  noises, while the new ordinary-search theorem derives equal-noise adaptive TFHE security from
  the existing native auxiliary-input CircLWE game, one ordinary scalar search-LWE game, and the
  post-cut LWE games. The native CircLWE premise itself remains explicit; no ordinary-RLWE
  reduction for that intact circular term is asserted.
- `FormalProof4FHE.TFHE.SamplerReplacement.tvDist_adaptiveRealGame_le` supplies the explicit
  model-alignment loss between any two executable finite error-sampler triples. It counts exactly
  `lweDimension * TGSW.rowCount ringRank tgswLevels` BRK ring errors,
  `(ringRank * degree) * keySwitchLevels` KSK errors, and `queryCount` adaptive input errors;
  deterministic TLWE/TGSW assembly and arbitrary downstream adversarial processing add no loss.
  `abs_signedAdvantage_implementation_le_directBilinear_add_batchLwe_add_replacement` composes the
  resulting statistical term with the native direct-bilinear circular premise and ordinary batch
  LWE. `TFHE.SamplerReplacement.CutCycleSecurity` gives the alternative-order finite theorem:
  one native KSK-first intact-cycle term, three post-cut LWE terms, and the same exact replacement
  cost. This is a finite-to-finite result: a truncation or torus-discretization construction must
  still prove the three one-draw distances before it can instantiate the bound for the original
  paper's ideal Gaussian notation.
  `FormalProof4FHE.Probability.FinitePMFCompiler` now supplies a proof-carrying way to discharge
  that finite-to-ideal interface: a nonempty uniform ticket table has an exact rational output
  law, and a finite per-residue check certifies its TV distance to any target PMF.
  `TFHE.DiscreteGaussianSampler` specializes the target to the exact torus-scaled modular discrete
  Gaussian, lifts two common-target certificates coefficientwise to executable ring errors, and
  feeds the resulting `degree`-scaled gap into the complete BRK/KSK/adaptive-input replacement
  count. It also bounds translation of one executable scalar table by twice its certificate error
  plus the ideal modular-Gaussian shift distance, then sums that bound coefficientwise for native
  ring errors. The linear specialization further reduces every bounded ideal shift to the bound
  times one integer-Gaussian unit-shift distance, identifies that distance exactly with the mass
  at zero, and bounds it by `exp(1/2)/(W+1)` for every checked `W ≤ αq`. These bounds instantiate
  the conditional smudging layer above. The asymptotic native shifted-Gaussian module proves the
  resulting expression negligible from polynomial construction growth, negligible
  sampler-certificate decay, and a checked `2^λ` window, and supplies the concrete polynomial
  growth witness for the growing centered-binomial dimensions. A generic canonical rounding
  theorem now constructs a denominator-`D` finite ticket certificate for every nonempty finite
  target PMF, with pointwise error at most `(card + 1) / D`. This is a noncomputable finite
  existence construction for real-valued target masses, not a uniform PPT table generator; no
  irrational ideal PMF is treated as executable.
  `TFHE.DiscreteGaussianSecurity.abs_signedAdvantage_le_monomialKDM_add_batchLWE_add_certificates`
  now closes the finite composition: implementation advantage is at most the exact native
  degree-two monomial-KDM circular term, one ordinary query-counted binary-secret batch-LWE term,
  and the explicit certificate loss. Its asymptotic companion
  `Asymptotic.MonomialSamplerReplacement.implementationSecurityGame_secureAgainst_of_monomialKDM_and_batchLWE`
  proves negligible implementation advantage from those three negligible premises. This is a
  complete conditional native-TFHE security theorem; the monomial-KDM premise is intentionally
  retained because the cited KDM papers change the encryption or secret-key geometry.
- `FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.replacementSecurityGame_advantage_negligible`
  lifts that exact loss into the negligible-function framework. New polynomial witnesses cover
  every BRK and KSK draw, while each adaptive adversary supplies its existing query polynomial.
  Thus negligible one-draw ring, KSK, and input TV gaps remain negligible after the complete
  execution. `implementationSecurityGame_secureAgainst_of_directBilinear_and_batchLWE` gives the
  final implementation-level composition: reference native circular/KDM security, reference
  ordinary batch LWE, and negligible sampler approximation imply negligible adaptive TFHE
  implementation advantage. The implementation's two scalar samplers may differ; only the
  reference samplers used by the ordinary batch-LWE theorem must coincide.
  `Asymptotic.CutCycleSamplerReplacement.implementationSecurityGame_secureAgainst_of_keySwitchFirst_and_three_batchLWE`
  supplies the matching alternative-order implementation theorem from negligible native
  intact-cycle KDM, three ordinary reference batch-LWE games, and negligible sampler gaps.
- `FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.secureAgainst_of_directBilinear_and_batchLWE`
  lifts the exact adaptive game to security-parameter-indexed families. Each adversary family
  contains a polynomial encryption-query bound; `batchSampleCount_le_polynomial` additionally
  proves polynomial total LWE sample growth when ring rank, ring degree, and KSK levels have
  polynomial bounds. The general
  `secureAgainst_of_directBilinear_and_jointLWE` theorem preserves distinct key-switch and input
  error families; its equal-noise specialization uses ordinary batch LWE. In both versions,
  negligible native direct-bilinear KDM and LWE advantages compose into negligible honest TFHE
  advantage. The circular premise remains explicit and is incurred once for the interaction.
- `FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.CutCycleSecurity.secureAgainst_of_keySwitchFirst_and_two_ringBatchLWE_and_jointLWE`
  lifts the alternative hybrid order pointwise and asymptotically. Negligibility of the native
  KSK-first intact-cycle game, the two post-cut ring batch-LWE reductions, and the zero-cloud
  joint-LWE reduction implies negligible adaptive TFHE advantage. In the equal-noise theorem
  `secureAgainst_of_keySwitchFirst_and_three_batchLWE`, every non-circular premise is a standard
  binary-secret batch-LWE security game.
- `FormalProof4FHE.TFHE.CenteredBinomial.Family.parameters` instantiates those asymptotic games
  with the checked ring centered-binomial sampler, a new executable scalar centered-binomial
  sampler, and exact power-of-base gadgets. Support theorems give deterministic signed error
  bounds, both gadgets have checked reconstruction, and
  `Family.securityGame_advantage_le_monomialKDM_add_jointLWE` and
  `Family.securityGame_advantage_le_monomialKDM_add_batchLWE` expose the exact native
  degree-two monomial-KDM first hop directly. Their `secureAgainst` companions prove negligible
  adaptive advantage from that named circular premise and joint or ordinary batch LWE, with no
  sampler-replacement premise or loss. The KSK-first counterparts
  `Family.secureAgainst_of_keySwitchFirst_and_two_ringBatchLWE_and_jointLWE` and
  `Family.secureAgainst_of_keySwitchFirst_and_three_batchLWE` instantiate the cut-cycle proof
  without changing samplers. `linearModulusFamily` is a fully specified scalable finite witness with
  explicit polynomial KSK dimensions; `linearModulusFamily_polynomialEvaluationKeyGrowth` now
  covers all BRK dimensions as well, so it instantiates the polynomial sampler-loss accounting.
  This is not a production parameter recommendation or an identification with the original
  paper's torus Gaussian distribution.
  The compatibility theorems
  `Family.securityGame_advantage_le_circularLWE_add_zeroLWE_add_batchLWE` and
  `Family.secureAgainst_of_circularLWE_and_zeroLWE_and_batchLWE` state the same exact
  centered-binomial result using the named auxiliary-input CircLWE formulation with an explicit
  zero-side premise. The stronger
  `Family.securityGame_advantage_le_circularLWE_add_three_batchLWE` and
  `Family.secureAgainst_of_circularLWE_and_batchLWE` discharge that premise: the pointwise bound
  contains the ordinary actual-context batch-LWE advantage twice and the uniform-BRK-context
  batch-LWE advantage once.
- `FormalProof4FHE.TFHE.CenteredBinomial.EndToEnd.exactRotationFamily` gives one Boolean family
  shared by confidentiality and native refresh correctness: at parameter `λ`, `N = λ + 1` and
  `q = 2N`, both scalar error samplers coincide, and every BRK/KSK dimension has a checked
  polynomial bound. `secureAgainst_and_refreshCorrect` combines negligible adaptive advantage
  under exact native monomial-KDM plus ordinary batch LWE with probability-one fresh refresh under
  the two explicit public noise margins. The sharper
  `secureAgainst_and_refreshCorrectLinear_of_nativeCircular_ordinarySearchLwe` pairs the strongest
  native-CircLWE/ordinary-search-LWE route with `RefreshCorrectLinear`: exact signed rotations
  preserve coefficient infinity norm, so past BRK errors accumulate linearly instead of carrying
  an exponential propagation factor. The theorem
  `not_exactRotation_linearOutputMargin_of_pos` now proves that the output margin is impossible
  for every positive deterministic BRK row-error bound at `q = 2N`. Thus this family is a useful
  exact interface and diagnostic witness, but not a nonzero-noise correctness instantiation.
  `secureAgainst_and_refreshCorrect_of_circularLWE` gives the corresponding end-to-end statement
  from auxiliary-input CircLWE and ordinary batch LWE, without a separate zero-message
  side-information assumption; its only extra efficiency obligation closes the uniform-BRK batch
  reduction. The polynomial-view route now also has the single theorem
  `secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe`: native one-challenge
  auxiliary-input CircLWE, one equal-noise combined scalar search-LWE batch, and the three post-cut
  LWE games imply adaptive confidentiality, paired with probability-one refresh correctness for
  the same exact-rotation family.
- `FormalProof4FHE.TFHE.CenteredBinomial.LargeModulusEndToEnd.family` resolves that checked
  obstruction with a distinct finite construction. At `N = λ + 1`, it uses
  `q = 16N^4 = (2N)^4`, exact base-`2N` decomposition with four levels, and centered-binomial
  width one for every scalar and ring error. Because `2N ∣ q`, `divisibleRoundExponent` is an
  exact additive quotient from ciphertext phases to native rotation exponents; no approximate
  rounding error accumulates across the LWE mask coordinates. `outputMargin` proves that the
  complete sharp BRK budget fits the code distance for every `λ ≥ 7`, and `refreshCorrect` proves
  probability-one fresh Boolean refresh with no margin premise left to the caller. The single
  theorem `secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe` pairs that
  unconditional correctness conclusion with conditional adaptive confidentiality from native
  auxiliary-input CircLWE, one ordinary combined scalar search-LWE batch, and the three checked
  post-cut LWE games. Native CircLWE remains an explicit circular-security assumption, and this
  exact divisible-modulus construction is not identified with the original paper's torus-Gaussian
  parameter set.
- `FormalProof4FHE.TFHE.CenteredBinomial.GrowingNoiseEndToEnd.family` strengthens the preceding
  constant-width witness to an asymptotic family with growing noise. Writing `w = λ + 1`, it takes
  scalar dimension and ring degree `N = 2^⌈log₂(8w)⌉`, so `8w ≤ N < 16w` and `X^N + 1` is a
  power-of-two cyclotomic polynomial. This is checked as the literal identity
  `Φ_(2N) = X^N + 1`, together with a bijective multiplicative interpretation of the executable
  coefficient carrier in the cyclotomic quotient. It uses centered-binomial width `w` for BRK,
  KSK, and input errors, and `q = 64N^6 = (2N)^6` with six exact base-`2N` levels. The modulus has
  an explicit polynomial upper bound; `inputMargin` and `outputMargin` hold for every `λ`; and
  `refreshCorrect` proves probability-one fresh Boolean refresh for every supported error. Its
  shortest construction-faithful confidentiality theorem is
  `secureAgainst_of_nativeMonomialKDM_and_concreteBatchLWE`: negligible advantage for the exact
  native degree-two cross-monomial KDM game plus the explicit binary-secret LWE family implies
  negligible adaptive TFHE advantage. Pointwise,
  `securityGame_advantage_le_nativeMonomialKDM_add_concreteBatchLWE` contains exactly those two
  terms and no statistical off-diagonal replacement. Its public-evaluation corollary has zero
  additional advantage loss. The literature-aligned real-versus-uniform formulation is
  `secureAgainst_of_nativeCircularLWE_and_concreteBatchLWE`: negligible exact native
  auxiliary-input CircLWE and the explicit binary-secret LWE family with modulus `64N^6`,
  dimension `N`, `6N+Q` rows, and centered-binomial width `λ+1` imply negligible adaptive TFHE
  advantage, with no correctness, sampler-replacement, finite-view, or collision premise.
  `concreteBatchLWESecurityGame_eq_batchLWE` proves this is exactly the generic reduction target,
  and `concreteBatchSampleCount_le_polynomial` bounds its rows by
  `96(λ+1)+Q(λ)`. Pointwise,
  `securityGame_advantage_le_nativeCircularLWE_add_three_concreteBatchLWE` exposes one circular
  term and the three concrete LWE occurrences used by the real, uniform-BRK, and honest
  reductions.
  Public homomorphic use is covered directly by the adaptive game: the adversary already sees the
  complete cloud key and may perform arbitrary computation on every returned ciphertext.
  `evaluationSecurityGame_advantage_eq` makes this closure explicit by compiling any public
  cloud-key-dependent evaluator into the base adversary with pointwise identical advantage, while
  `evaluationSecureAgainst_of_nativeCircularLWE_and_concreteBatchLWE` composes the zero-loss
  compiler with the concrete circular/LWE theorem. Its only additional premise is preservation of
  the chosen efficient-adversary class; no decryption or refresh-correctness hypothesis is used.
  The combined security-and-refresh theorem remains available independently. Because the family's
  native ring rank is one, `postCutBinarySecretRLWESecurityGame_eq_ringBatchLWE` additionally
  identifies the complete post-cut ring game with finite binary-secret RLWE, pointwise and with no
  loss. The theorem
  `secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe_binarySecretRLWE` exposes
  that exact RLWE premise directly. The exact same game is also instantiated over
  `(Z/qZ)[X] / (Φ_(2N))`; `postCutBinarySecretRLWE_advantage_eq_cyclotomic` proves pointwise
  advantage equality. The security-only endpoint
  `secureAgainst_of_nativeCircular_ordinarySearchLwe_cyclotomicRLWE` concludes adaptive TFHE
  confidentiality without mentioning refresh correctness; the stronger convenience theorem
  `secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe_cyclotomicRLWE` accepts
  the same assumptions and additionally returns the independent correctness result.
  The quantitative theorem
  `securityGame_advantage_le_nativeCircular_add_ordinarySearchLwe_add_finiteLoss_add_two_cyclotomicRLWE_add_inputLWE`
  records the complete pointwise reduction before negligibility: exact BRK view count times one
  native CircLWE advantage, one ordinary scalar search-LWE term, the explicit finite-view loss,
  two losslessly transported cyclotomic-RLWE terms, and the adaptive input-LWE term.
  `Native.CoefficientStructuredLWE.problem` goes one step
  lower: it presents every ring element as a `Fin N → ZMod q` coefficient vector, proves that the
  noiseless map is the explicit schoolbook negacyclic convolution, identifies the ring sampler
  with independent direct centered-binomial coefficient sampling, and transports both games and
  every advantage through a public-transcript equivalence. The theorem
  `secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe_coefficientStructuredLWE`
  therefore accepts the exact coefficient structured-LWE game as its post-cut premise. Its secret
  has independent Boolean coefficients; `postCutRingSecret_pointProbability` proves that every
  rank-one secret has probability exactly `2^-N`, so it has exactly `N` bits of min-entropy. It is
  not silently replaced by uniform-secret RLWE. The companion
  `CenteredBinomialGrowingNoiseCircularSearch` module proves that KSK gadget level one has centered
  distance exactly `2N`, closes the paired-recovery margin, and specializes the averaged residual
  reduction to public CircLWE and public-continuation monomial-KDM security. The adaptive public
  auxiliary-input theorem additionally includes the entire bounded input tape and gives a single
  growing-family endpoint for adaptive confidentiality; a separate convenience theorem pairs it
  with probability-one refresh. The security-only theorem
  `AdaptivePublicCircular.secureAgainst_of_search_candidate_and_jointLWE` derives confidentiality
  from narrow augmented paired-search, the explicit native candidate loss, and ordinary joint
  LWE, while
  `securityGame_advantage_le_search_add_candidateLoss_add_three_jointLWE` records the exact
  pointwise bound with no circular term left. Public evaluation is covered by the corresponding
  zero-loss `evaluationSecureAgainst_of_search_candidate_and_jointLWE` theorem. Thus
  public augmented CircLWE is its only circular premise and ordinary joint LWE discharges the zero
  branch. A stronger residual-search headline now derives that public premise from narrow
  augmented paired-search security plus the evaluator's explicit smudging/threshold/amplification
  loss. A one-shot security-only companion instead proves the exact bound
  `TFHE advantage <= coordinate-prediction bias + selected-coordinate statistical error + three
  joint-LWE advantages`. The corresponding asymptotic confidentiality theorem assumes only
  coordinate-prediction security, negligible correct/freshness errors from the direct native
  certificate, ordinary joint LWE, and the expected efficiency-closure conditions. Public
  cloud-key-dependent evaluation adds zero advantage loss. Neither theorem imports refresh or
  decryption correctness; those remain optional, independent results.
  The discrete-Gaussian target specialization now supplies a parameter-compatible version of
  this security-only endpoint. It takes `q = (2N)^(lambda + 1)`, `lambda + 1` exact base-`2N`
  gadget levels, and relative width `alpha = 1/(2N)`, and proves internally that the integer
  Gaussian width is `(2N)^lambda >= 2^lambda`. Its canonical table uses denominator
  `q(q+1)2^lambda`; the checked certificate error is at most `2^-lambda` and is therefore
  negligible. Assigning all leftover tickets to zero also preserves exact negation symmetry.
  The preferred canonical theorem now exposes neither a Gaussian table-error premise nor a native
  distribution-law record. Wrong-view freshness is bounded by the exact message-one control fiber
  loss times the polynomial BRK layout; the selected diagonal uses the checked sharp operator
  reduction; and the complete off-diagonal replacement is bounded by its exact expectation under
  the generated source control. Exact structured/direct equivalence then eliminates that control
  ciphertext entirely: its masks, ring secret, and gadget message disappear, leaving the finite
  `L²` law `fresh centered-binomial error + uniform-digit operator (signed centered-binomial
  control error)` versus the compiled target error vector. The generated-control average is
  exactly the IID control-error expectation. Centered-binomial sign symmetry removes the final
  Boolean maximum. Exposing source errors as uniform bit-pair tables and target errors as uniform
  ticket indices, and replacing the exact-capacity uniform difference ciphertext by its IID base
  digits, identifies the complete quantity with a finite uniform average of explicit output-fiber
  cardinality formulas. A checked deterministic norm bound shows that every real residual
  coefficient remains within a polynomial-size ball, and a norm-threshold theorem lower-bounds
  total variation by one minus the target mass of that ball. Thus the current exponentially wide
  Gaussian is an auditable conditional target, not a justified statistical-smudging conclusion;
  the sound completion route is computational RLWE/native circular security or a matching narrow
  target. Subject to the explicit finite premise, adaptive and publicly evaluated TFHE confidentiality follows from
  negligibility of those three canonical construction quantities, coordinate-prediction
  security, ordinary joint LWE, and efficiency closure. These
  theorems deliberately make no refresh-correctness claim. The canonical table is a mathematical
  finite witness; uniform PPT generation or materialization of that table is not claimed.
  The shifted evaluator and its correct residual sampler are now executable. Its
  independent-difference form now has an exact simultaneous whole-key conditional normal form:
  native BRK coordinate independence is derived from the generator, uniform-mask translation is
  proved bijective, and every off-diagonal entry is residualized in one finite product. A checked
  hybrid bound isolates the complete correct-side cost as the averaged self-correlated diagonal
  marginal versus one fresh entry, plus the sum of the off-diagonal residual costs; it does not
  replace this marginal by a worst-case fixed-control bound. The bound now permits distinct source
  and target error samplers. The selected diagonal is reduced further rather than left as an
  opaque distance premise. After fixing the uniform difference ciphertext, its gadget digits
  induce one linear row operator on every public mask column and on the source error vector. A
  finite fiber-second-moment bound controls the transformed uniform mask without a field
  assumption. The linear form also gives an exact rank-event alternative: whenever the fixed row
  operator is bijective, its simultaneous action on every public mask column transports the
  complete uniform challenge exactly, so the mask-replacement cost is at most the probability of
  a non-bijective row operator under the actual uniform difference ciphertext. This event is now
  characterized algebraically without loss: the operator's canonical matrix has entries equal
  to the identity plus the candidate-signed difference digits, and non-bijectivity is exactly
  failure of its determinant to be a unit in the coefficient ring. An additional whole-key
  constructor accepts any proved upper bound on that explicit determinant event. At exact gadget
  capacity `q = B^ℓ`, scalar base decomposition is now proved bijective, then lifted
  coefficientwise to `Rq` and through every extended coordinate of the complete native TGSW
  difference. Consequently the determinant's entire row/block/coefficient/level digit tensor is
  jointly uniform, equivalently IID uniform in `Fin B`, and its casts are exactly the ring-valued
  digits appearing in the canonical matrix. The resulting estimate is now closed—and is an
  obstruction. For every positive-level exact-capacity even-base instance, coefficient reduction
  modulo two followed by evaluation at `X = 1` maps the row matrix to an exactly uniform square
  binary matrix. Its rank-failure probability is at least `1/2`; preservation of units by this
  ring homomorphism proves that the original determinant non-unit probability, and hence the
  rank-sharp diagonal loss, is also at least `1/2` for either candidate bit, independently of the
  error samplers. Therefore the exact-rank/bounded-determinant constructor cannot yield negligible
  loss for this native regime. The replacement route is now formalized as a direct
  side-information collision hybrid. It treats the complete uniform difference and public
  challenge as one extractor input, retains the error transformed by the same difference as side
  information, and replaces only the transformed challenge. Reassembly is proved exactly equal
  to the executable diagonal operator and existing mask-replaced experiment. Thus the new
  diagonal budget is the source-error average of an explicit joint collision loss plus one
  mixed-error-to-target distance, maximized over the two scalar bits; a whole-key constructor
  installs it without any fixed-difference invertibility premise. The joint collision loss is
  now proved exactly equal to a normalized finite-fiber cardinality sum. A parallel Pearson
  chi-square relaxation, also explicit in those fiber counts, is lifted through the selected
  entry and whole-key certificate for rank/codimension/Fourier estimates. A two-copy normal form
  further identifies every challenge collision with the zero fiber of a rectangular paired row
  operator. Surjective pairs contribute exactly the uniform baseline, and all remaining loss is
  one explicit rank-deficiency-weighted excess. If `D` is the number of difference ciphertexts,
  `C` the number of challenges, `K_t` the difference-fiber size at retained error `t`, and `E_t`
  its summed paired excess, the Pearson divergence is proved exactly equal to
  `sum_{K_t > 0} E_t / (D C K_t)`. Dropping the same-fiber restriction gives the further
  source-error-independent upper bound `totalPairExcess / (D C)`. A separate whole-key
  constructor consumes only a candidate-wise estimate of this global budget, so the collision
  premise no longer quantifies over centered-binomial error support or retained fibers. This last
  relaxation may be looser than the exact normalized expression because it replaces every
  nonempty `K_t` by one. At exact capacity with even gadget base, the parity reduction of two
  independent difference matrices is now proved exactly uniform on the binary `2m`-by-`m` matrix
  space, where `m` is the TGSW row count. Its rank-failure probability is at most
  `2 / 2^(m+1)`, in sharp contrast with the at-least-`1/2` failure of one square block. The binary
  matrix is entrywise the transpose of the parity-reduced concrete paired row matrix. A generic
  local-homomorphism lift is now checked: a binary left inverse is lifted entrywise, its square
  product has unit determinant because parity reflects units, and transposition supplies a right
  inverse for the original paired row matrix. Consequently binary full rank gives native row
  surjectivity and exactly zero paired-collision excess. The production specialization is now
  checked for `ZMod (2^k)[X]/(X^(2^d)+1)`, `k > 0`: reduction to the binary quotient has
  nilpotent kernel, the binary parity kernel is generated by `X - 1`, and therefore the concrete
  parity map reflects units. Thus a binary-full-rank pair has zero native collision excess at the
  actual power-of-two modulus. Quantitative accounting for the residual rank-deficient pairs is
  also made explicit: their exact ordered-pair count divided by the square of the difference-space
  cardinality is the rank-failure probability, total excess is at most that count times the square
  of the challenge cardinality, and the relaxed global budget is therefore at most
  `rankFailureRatio * differenceCard * challengeCard`. This checked magnitude factor explains why
  the rank-failure probability alone is not a negligible collision bound. The deficient-pair
  estimate is now sharpened rank by rank. For every finite additive operator, Lean proves the
  exact identity `zeroFiberCard * imageCard = domainCard`. Surjective coefficient reduction maps
  the native matrix image onto the reduced image, and a stronger local-ring lift shows that binary
  rank `r` supplies a free native image of cardinality at least `|Rq|^r`: a basis of the reduced
  image is lifted to native input columns, while a transposed right inverse proves the lifted
  column map injective. Hence each paired row zero fiber is at most
  `rowDomainCard / |Rq|^r`, full-rank pairs still contribute exactly zero, and all deficient pairs
  are summed with their individual ranks in a new normalized budget. That budget bounds the exact
  retained-fiber Pearson expression, the selected-diagonal distance, and a whole-key certificate;
  its power-of-two production form has no local-homomorphism premise. This removes the universal
  `challengeCard^2` magnitude from the preferred bound. It does not yet prove negligibility: a
  corank-`t` residue matrix can still carry an envelope factor `|Rq|^(t * ringRank)`. A sharper
  higher-adic image distribution or a direct estimate using the exact retained fibers `K_t`
  remains required. The centered-binomial parity analysis now supplies a typical unit source-error
  entry, and that unit has been used for the first direct conditioned count. At full gadget
  capacity, fixing all but its block/level digit column makes the retained transformed error
  determine the omitted digit polynomial uniquely in every row. Consequently every such native
  retained-error fiber has size at most
  `base^(m * (m - 1) * (degree + 1))`, with `m` the TGSW row count. This injective slice is not a
  whole-ring uniformity claim and does not yet control the kernel/cokernel weights averaged inside
  the fiber.
  The retained fiber is now characterized more sharply, not merely bounded. Every assignment of
  the other digit columns forces one selected ring polynomial; validity says exactly that this
  polynomial has small base digits. This validity predicate is row-local, so the native retained
  fiber is equivalent to a dependent product of finite valid-row types and its cardinality is the
  product of their cardinalities. A generic finite moment identity then expands the exact native
  self-kernel weight into proposed kernel-vector tuples and factors their acceptance count across
  rows. The all-zero tuple equals the fiber-cardinality baseline and cancels, leaving a manifestly
  nonnegative sum over only nonzero tuples. The distinct-pair native cokernel sum is likewise
  transported to a double product of valid rows. A checked two-column refinement now bounds those
  simultaneous row counts. One proposed kernel vector and the retained equation jointly determine
  the selected and pivot digit columns whenever their native `2 × 2` minor is a unit. If the
  selected source coordinate is a unit, all such minors are nonunits exactly when the proposed
  vector's binary parity lies on the two-element line generated by the source parity vector.
  Coordinatewise parity is surjective, so the exact bad-vector identity is
  `badCount * 2^m = 2 * valueCount`, and simultaneous bad tuples have the corresponding powered
  density. The complete moment is now bounded by a two-column term for all tuples plus a
  one-column term for the exactly counted bad tuples. A denominator-preserving normal form now
  divides the product fiber cardinality row by row, exchanges the complete transformed-error sum
  with the tuple sum, and factors the result into row-local normalized acceptance sums. Returning
  to the native equal-difference collision slice is exact: the zero tuple subtracts one baseline
  on every nonempty fiber, and the remainder is divided by the full difference-ciphertext space.
  Each row-local weight is now bounded by `min(1, A / K)`, where `A` is its two-column count on a
  good tuple (one-column count on a bad tuple) and `K` is that row's actual valid-fiber size. The
  checked complete bound retains the exact parity-bad tuple count, subtracts the nonempty-fiber
  baseline, and divides by the full ciphertext space. A second, denominator-preserving support
  argument maps every nonempty valid row fiber injectively into the centered polynomial box
  forced by the actual reconstructed error equation. For the canonical growing centered-binomial
  family, that box consumes at most a `2^-N` fraction after the complete twelve-row product and
  ciphertext normalization. Consequently the actual fixed-error equal-difference/self collision
  excess is at most `2^-N` for every supported source-error vector with a selected unit entry, and
  this envelope is proved negligible. The paired cokernel term now also has an exact
  denominator-preserving additive-character normal form. The native row cokernel factor is the
  cardinality of the common annihilator of the two paired row images; after taking the
  `ringRank` power, subtracting the uniform baseline removes exactly the all-trivial character
  tuple. Thus, in each retained transformed-error fiber, the complete distinct-pair excess is
  exactly `sum_{chi != 0} N_chi * (N_chi - 1)`, where `N_chi` counts the retained differences
  annihilated by the character tuple. Each `N_chi` is now further identified with the zero fiber
  of a sum of independent valid-row contributions. A second finite character transform gives an
  exact rowwise Fourier factorization: the trivial dual character is precisely the product of
  the actual valid-row cardinalities, and the centered deviation is a sum of products of
  nontrivial row-local Fourier coefficients. Finite biduality reindexes every abstract
  second-dual character by a unique nonzero tuple of concrete ring test values. In native ring
  rank one, each resulting row coefficient is exactly one finite sum of the original native
  character applied to the reconstructed row-operator entry at that test value. Eliminating the
  forced selected digit rewrites that entry as a fixed offset plus small digit polynomials
  weighted by the exact minors `s_selected * v_j - s_j * v_selected`. The fixed offset factors
  out with character norm one, so the coefficient norm is exactly the norm of this pure
  minor-weighted character sum. This also reveals a structured exception: the nonzero test row
  equal to the retained source error makes every minor vanish and gives a full-cardinality
  Fourier coefficient. Its phase is nevertheless exact—the complete row product is the retained
  fiber cardinality times the outer character evaluated on the transformed error. A phase-aware
  centered identity now splits this source mode from every remaining nonzero test tuple, avoiding
  the false requirement that every nonzero coefficient cancel. Exact outer-character `L²`
  orthogonality now evaluates that source mode completely: after deleting the trivial character,
  the squared factor sums to `4|G|-4` when the transformed error is zero and `2|G|-4` otherwise.
  A checked pointwise square inequality and its aggregate therefore bound the exact factorial
  moment by this closed source factor plus only the squared non-source second-dual remainder,
  divided by the full target-character cardinality squared. The canonical nonzero-parity
  certificate converts this phase-aware moment through the character, cokernel, selected-mask,
  negligibility, and security interfaces without a norm-only relaxation. The normalized collision
  loss still divides by the actual fiber cardinality and the full difference-ciphertext
  cardinality, with the challenge cardinality canceled exactly. What remains statistically is a
  quantitative minor-sum `L²` bound for the non-source test tuples at the canonical parameters.
  Separately, a
  reduction of the intact bilinear TFHE circular-coordinate prediction problem to ordinary
  LWE/RLWE remains unproved.
  The concrete growing-noise family now has an additional checked obstruction: ring rank one and
  six decomposition levels make `m = 12` at every security parameter, so its paired residue law
  is the same uniform `24`-by-`12` binary matrix law for every `λ`. Its rank-failure probability
  is proved equal to the exact finite-field product formula, bounded below by `2^-24`, and formally
  not negligible. Thus the residue full-rank event cannot itself supply an asymptotically
  negligible loss for this family. This does not prove the actual collision loss non-negligible;
  higher-adic image growth or cancellation in the exact retained-fiber sum may still close it.
  The older conditional budget
  can still use either the expected challenge-fiber loss or the exact bad-rank probability, and
  separate constructors retain the fiber, exact-rank, and bounded-determinant forms. The
  adaptive lift proves that centered-binomial scalar transport,
  the retained KSK and tape, and the ordinary target real view introduce no additional loss. A
  direct certificate constructor therefore consumes only the averaged diagonal bounds, the
  conditional off-diagonal source-to-target bounds, and one fully averaged wrong-branch
  freshness bound. Exact fixed-mask wrong-branch bijectivity is also proved to identify the
  mask-averaged
  experiment with uniform exactly, and a refined constructor sets its freshness loss to zero.
  That bijectivity premise is now decomposed without loss: the whole BRK map is a product of
  independent TGSW-entry maps, and every entry is a product of explicit finite TLWE-row maps.
  Rowwise bijectivity therefore discharges the exact transported wrong-branch premise directly.
  When exact bijectivity is unavailable, a quantitative companion bounds the whole-BRK defect by
  the double sum of the explicit row-map TV defects. The adaptive lift then averages this sum with
  the exact scalar-mask probabilities, without replacing it by a worst-case mask or adding a
  further hybrid loss. A whole-key certificate constructor accepts precisely these mask-averaged
  row bounds. More importantly for random-rank arguments, a second lift averages over the actual
  generated BRK, KSK, and input tape as well. It bounds the complete wrong view by the probability
  that some named row map is non-bijective, jointly over the public context and scalar mask, and
  union-bounds that event into explicit per-row failure probabilities. Rare bad public controls
  are therefore charged rather than prohibited support-wise. An exact translation-conjugacy
  theorem now sharpens this further: every false/data row induces the same normalized
  control-only map, so all of those named row events coincide. Exact gadget recomposition writes
  that map as identity plus the digit-weighted canonical homogeneous part of a message-one
  control. Complementary-candidate toggling cancels scalar XOR transport, and an exact marginal
  projection leaves only the original hidden bit and its selected TRGSW control. Expanding native
  key generation then proves that this marginal is exactly a coordinate-free sampler containing
  one uniform bit, one uniform ring secret, and one generated control. The final wrong-view bound
  therefore has one canonical-control failure probability and no KSK, input tape, coordinate,
  BRK-coordinate, or row-count factor; the older row union remains a compatibility theorem.
  For centered-binomial control noise, coefficientwise negation symmetry removes even that
  uniform hidden bit: toggling the generated hidden-bit control by its complementary candidate
  has exactly the law of one generated message-one control under the same uniform ring secret.
  Both the non-bijectivity probability and the expected normalized one-row TV defect are proved
  exactly equal to their message-one versions.
  A separate direct route does not require bijectivity: translation conjugacy proves every data
  row has exactly the normalized control-map TV defect, and the whole wrong view is bounded by
  the number of output TLWE rows times its canonical expectation. The whole-key certificate
  accepts either the zero-one message-one failure bound or this direct message-one statistical
  bound; the earlier canonical-control constructors remain available. That direct defect is now
  bounded without a field or linearity assumption. For each fixed message-one control, the
  identity-plus-digit map is treated as an arbitrary deterministic endomorphism of the finite
  TLWE row space. Its uniform-output distance is at most one half the square root of its exact
  fiber-second-moment excess over the permutation baseline. Averaging this loss under the actual
  nonuniform generated-control law and multiplying by the output-row count gives a checked
  complete wrong-view bound and a whole-key certificate constructor. A support-wise estimate
  `fiberSecondMoment <= |Row| * (1 + epsilon)` specializes the expected defect to
  `sqrt(epsilon) / 2`. This is valid for the production power-of-two coefficient ring and the
  nonlinear digitizer; proving a negligible quantitative fiber estimate for a chosen parameter
  family remains open. The centered-binomial-only normalization has also been factored through
  its true requirement: exact negation symmetry of the ring-error sampler. A finite Gaussian
  ticket certificate may now additionally prove equal ticket counts for every residue and its
  negation. That check gives exact scalar and coefficientwise-ring symmetry, exact scalar-XOR BRK
  transport, exact hidden-bit elimination to one message-one control, and the same complete
  wrong-view fiber bound for a symmetrically compiled discrete Gaussian. Its existing Gaussian
  approximation certificate remains available for the smudging estimates.
  These premises are packaged as a named whole-key rank certificate, with a certified
  discrete-Gaussian target specialization. A general asymptotic candidate-view adapter now carries
  that certificate through augmented paired search, and the growing-family endpoint concludes
  adaptive TFHE confidentiality together with probability-one refresh from negligible candidate
  loss, narrow search hardness, and ordinary joint LWE. A negligible message-one control failure
  probability or quantitative bound on the now-explicit identity-plus-digit fiber excess, the
  selected diagonal's explicit challenge-fiber and mixed-error terms (the bad-rank alternative is
  formally ruled out for exact-capacity even bases),
  off-diagonal estimates, and
  augmented paired-search hardness remain explicit inputs.
  For the preferred canonical one-shot security theorem, the native laws are already compiled
  into exact finite quantities: only negligibility of the sharp diagonal loss, the selected
  explicit IID digit/bit-pair/ticket off-diagonal fiber-count loss, and the message-one fiber loss is required, together with
  circular coordinate-prediction hardness and ordinary joint LWE. The off-diagonal term contains
  only effective error-vector probabilities; public masks, secrets, gadget messages, and
  ciphertext assembly have been eliminated by checked equalities and data processing. No
  correctness result is in that
  proof chain. The new residual support and TV-threshold audit explains why the off-diagonal premise
  should be discharged computationally rather than by the present exponentially wide Gaussian.
  This removes
  constant noise, the non-cyclotomic
  degree, and presentation ambiguity from the concrete witness, but it does not prove the
  binary-secret hardness premise, native CircLWE, or production parameters. Existing entropic
  RLWE results require Gaussian target error and additional DSPR/noise-lossiness hypotheses, and
  explicitly do not obtain the binary-coefficient rank-one case from entropy alone.
- `FormalProof4FHE.TFHE.Evaluation` starts the independent functional-correctness layer.
  `TGSW.phase_externalProduct_eq_mul_add_error` proves that an exact gadget decomposition makes a
  TGSW--TLWE external product carry `message * phase(input)` plus the explicit weighted row error.
  Its approximate counterpart additionally exposes `message * phase(decompositionResidual)` and
  can compute that residual from any proposed digit vector.
  `TGSW.KeySwitch.phase_apply_eq_phase_sub_error` proves that exact mask recomposition preserves
  the source TLWE phase minus the explicit accumulated key-switch error.
  `FormalProof4FHE.TFHE.GadgetDecomposition` implements fixed-length unsigned base digits in
  `ZMod q`, proves the digit bound and exact reconstruction under `q ≤ B^ℓ`, and lifts the same
  executable algorithm coefficientwise to the concrete negacyclic ring `Rq`.
  `FormalProof4FHE.TFHE.FullWidthBalancedDecomposition` additionally proves that an exact-capacity
  centered decomposition is a bijection, including signed interval digits, most-significant-first
  ordering, arbitrary row components, and flattened ordinary-row/auxiliary-level indices.
- `FormalProof4FHE.TFHE.BlindRotation` implements the public affine-TRGSW accumulator update,
  proves that a binary bootstrapping-key entry selects either `1` or the requested negacyclic
  rotation factor, and gives an exact list-level phase invariant with every row-error contribution
  retained. `FormalProof4FHE.TFHE.SampleExtraction` proves against executable negacyclic
  convolution that the extracted scalar phase is exactly the constant coefficient of the ring
  phase, including the native binary `keyExtract` specialization.
- `FormalProof4FHE.TFHE.NoiseBounds` proves centered modular triangle/product inequalities,
  coefficient-infinity bounds for concrete base digits, and a checked worst-case bound for every
  digit-weighted TGSW external-product error. `TFHE.SharpRotationNoise` proves directly for the
  executable negacyclic backend that convolution has a linear-in-`N` coefficient bound,
  multiplication by a native signed monomial preserves coefficient infinity norm, and the sparse
  factor `(X^a - 1)` costs at most twice the input norm.
  `TFHE.BootstrappingCorrectness` therefore exposes both the compatible geometric theorem and
  `decode_nativeBlindRotate_apply_linear`, whose accumulated-error budget is linear in the number
  of blind-rotation controls and uses the linear convolution estimate for each digit-weighted row.
  The remaining slack is the deterministic worst-case sum over gadget rows and digits, not a
  geometric trace or sparse-factor loss.
- `FormalProof4FHE.TFHE.RotationLookup` discharges the algebraic lookup obligation constructively.
  Executable signed monomials form the expected exponent group modulo `2N`; native mask controls
  collapse to one rounded phase exponent; and any first-half table is materialized as an
  executable negacyclic test vector with its forced anti-periodic second half. At the concrete
  finite modulus `q = 2N`, `exactRoundExponent` is the canonical `ZMod`/`Fin` equivalence and is
  proved to recover `b - <s,a>` exactly. The closed theorem
  `decode_nativeBlindRotate_apply_bitTable` therefore has no ideal-lookup or rounding premise;
  `decode_nativeBlindRotate_apply_bitTable_linear` supplies the same closed lookup result with the
  sharp linear rotation budget. `TFHE.DivisibleModulusRotation` further closes the lookup theorem
  at every larger modulus divisible by `2N`, using the exact additive quotient described above.
  Approximate modulus switching for non-divisible production-style `q` remains a separate
  model-alignment obligation.
- `FormalProof4FHE.TFHE.CenteredBinomialCorrectness` derives the BRK row premise from the
  executable key generator. It proves that each abstract TGSW row error is exactly its sampled
  homogeneous error, projects support membership through both finite products in BRK generation,
  and turns centered-binomial coefficient bounds into `cInfNorm ≤ eta`. Consequently
  `probEvent_bitTableBootstrappingResult_eq_one` gives probability-one correctness of the exact
  finite Boolean-table evaluator whenever the public code-distance margin holds; bounded support
  incurs no tail-probability loss. Its `_linear` companion uses the sharp rotation budget.
  Unbounded or truncated torus-Gaussian variants still require their own tail and model-alignment
  arguments.
- `FormalProof4FHE.TFHE.CenteredBinomialRefresh` connects that table evaluator to a freshly
  encrypted Boolean. It uses antipodal input phases `0` and `N` at `q = 2N`, proves that every
  signed scalar error in `[-inputEta, inputEta]` selects the intended anti-periodic threshold
  region when `2 * inputEta < N` (including wraparound), and composes fresh-input and BRK support.
  `probEvent_fresh_bitTableBootstrappingResult_eq_one` therefore proves complete native Boolean
  refresh correctness with probability one under the explicit input-region and output-distance
  margins; `probEvent_fresh_bitTableBootstrappingResult_eq_one_linear` proves the corresponding
  sharper result without geometric propagation of earlier row errors.
  `TFHE.CenteredBinomialDivisibleRefresh` lifts the complete support-wise and probability-one
  refresh proof to every coefficient modulus divisible by `2N`; the large-modulus families above
  discharge all margins first at width one and then at the growing width `λ + 1`.
- `FormalProof4FHE.GeneralizedSubspaceLWE.shared_problem_eq_generalized` and
  `sharedSpec_isNested` identify shared-randomness LWE with a nested generalized-subspace
  instance.
- `FormalProof4FHE.GeneralizedSubspaceLWE.shared_zmod_advantage_eq_batch` states the resulting
  ordinary-LWE reduction directly in the generalized-subspace presentation.
- `FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive.advantage_le_batchLWE_add_rankLoss` gives an
  explicit reduction from adaptive affine-projection Subspace LWE to ordinary matrix batch LWE:
  the SLWE advantage is at most the advantage of `batchReduction` plus
  `2 * (Q * (2 / |F|^(δ+1))).toReal`. The affine-fiber simulator, its real and uniform branch
  laws, the adaptive logged-transcript rank bound, and the bounded online-to-batch compilation are
  all checked. Its only operational hypothesis is the adversary's public `Q`-query bound;
  `advantage_le_of_batchLWE` packages the result against a supplied ordinary-LWE bound.

## Trust and proof status

Finished theorem files must build with warnings treated as errors, so any use of `sorry` fails the
check. `FormalProof4FHETest/AxiomAudit.lean`
records the axioms used by the public security theorems. See `docs/ProofStatus.md` for the mapping
between paper statements and Lean declarations.
