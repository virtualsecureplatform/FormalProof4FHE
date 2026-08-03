# Hash-lossy complete-view native TFHE theorem

`FormalProof4FHE.TFHE.NativeTRGSWHashLossyCompleteView` formalizes the finite mathematical claims
in `sketch/hash_lossy_complete_view_native_tfhe.tex`.

## Exact view-level lossy mode

For a surjective linear hash, `hashFiberResample` uses the existing affine-fiber sampler to draw a
uniform point in the fiber containing the original prefix.  `hashFiberLossyView_evalDist_eq_of_hash_eq`
proves exact fiber invariance for an arbitrary complete-view generator, so all BRK, KSK, and
auxiliary correlations can remain in one opaque output carrier.

`hashFiberResample_uniform_evalDist` proves that resampling the fiber of a uniform prefix remains
uniform.  Consequently, `lossyUniformPrefixView_evalDist_eq_ordinary` proves exact equality of the
unconditioned ordinary and lossy public marginals when the prefix is uniform and independent of
the suffix.  This identity is explicitly not used as a source-coupled reduction: generating a new
latent prefix may ignore an externally supplied LWE/RLWE source challenge.

## Digest match-and-square bound

`projectedLeakageConcentration_le_gamma` proves that every covering fake-digest law pays at least
the digest Renyi-half concentration.  The square-root tilt attains equality by
`projectedLeakageGamma_eq_concentration_of_squareRootTilt`.

For a public family of balanced `r`-bit hashes,
`averagedConditionalDigestConcentration_eq_twoPow` proves

\[
\mathbb E_H C_{1/2}(H(P)\mid H)=2^r.
\]

The hash seed is public context and is not charged as leakage.  The source-coupled scalar theorem
`averagedUniformBinaryDigestMatchSquareGap_le` combines diagonal correctness with a two-copy
source statistic and approximate branch erasure:

\[
\operatorname{Gap}_{\rm loss}
\leq \rho_+ + \rho_- +
\sqrt{2^r(2\varepsilon_{\rm source}+\upsilon^2)}.
\]

The fixed-hash version is `uniformBinaryDigestMatchSquareGap_le`; exact erasure gives the
`sqrt(2^(r+1) * sourceAdvantage)` form.  `uniformBinaryHashLossyCompleteViewComposition_le` adds
the two ordinary/lossy mode switches and exactly one terminal sampler defect.  Its exact-erasure
corollary is the final conditional theorem from the manuscript.

## Translation-only barriers

`phaseObliviousHash_injective` instantiates the checked Walsh stabilizer theorem.  At cutoff
`d + 2 <= t`, exact phase-oblivious correctness forces the hash to be injective, and
`prefixCard_le_digestCount_of_phaseOblivious` gives `t <= r` for a binary digest.

For approximate correctness, `approximatePhaseObliviousHash_defect_lowerBound` interprets the
existing table `L1` defect as twice total variation and proves

\[
\varepsilon \geq \frac{1}{4\lambda_d}
\]

whenever a digest fiber contains two distinct prefixes.  Thus a noninjective short hash cannot
give negligible defect through the existing translation-only constructor.

## Statistical decoding barrier

`hashFactorizedDecoderSuccess_eq_probability` connects the finite mass-table functional to an
executable decoding game.  `hashFactorizedDecodingProbability_le_cardRatio` proves that any
decoder succeeds with probability at most

\[
\frac{|\mathsf{Digest}|}{|\mathsf{Prefix}|}.
\]

For binary `t`-bit prefixes and `r`-bit digests this is exactly `1 / 2^(t-r)`.
`labelledDecoderSuccessGap_le_tvDist` applies data processing for total variation, and
`binaryHashStatisticalModeSwitch_lowerBound_of_factorizedView` concludes

\[
\varepsilon_{\rm mode}\geq 1-\kappa-2^{-(t-r)}
\]

when the ordinary labelled view is decoded with probability at least `1-kappa`.

## Remaining cryptographic premise

No ordinary/lossy native parameter generator is asserted.  A complete TFHE instantiation still
has to construct computationally indistinguishable ordinary and lossy BRK/KSK/auxiliary laws,
source constructors using only the digest, and a common uniform-source branch law.  The Lean
theorems show exactly what that construction would imply and rule out the phase-oblivious and
key-by-key statistical shortcuts; they do not disguise the missing computational dual mode as an
algebraic assumption.
