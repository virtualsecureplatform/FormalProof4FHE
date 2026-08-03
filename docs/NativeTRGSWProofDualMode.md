# Conditional native TFHE hash-lossy dual mode

`FormalProof4FHE.TFHE.NativeTRGSWProofDualMode` formalizes the additional finite claims in
`sketch/proofdualmode.md`. It is a synthesis layer over the already checked hash-lossy,
translation-barrier, decoder-barrier, and native nonce-row modules. It does not assert that the
sketch supplies a concrete cryptographic dual-mode generator.

## Source-independent construction is insufficient

`sourceIndependentConstructor` exposes the failure mode directly: the constructor has a source
argument but does not use it. Consequently
`sourceIndependentConstructor_real_reference_evalDist_eq` proves exact equality after replacing
the real state by a reference state.

`target_tvDist_le_of_sourceIndependent_erasure` proves the abstract triangle bound, and
`target_tvDist_le_of_sourceIndependentConstructor` connects it directly to real-source diagonal
experiments and a reference-source erasure experiment:

\[
\Delta(L_+,L_-)\leq \rho_+ + \rho_- + \upsilon.
\]

Thus fresh kernel-randomization can prove a view-marginal identity, but it cannot turn a target
distinguisher into a real/reference source distinguisher unless the supplied source is actually
consumed.

## Full conditional hybrid

`completeAcceptanceHybrid_le` checks the five transitions

\[
V_+^{\rm native}\to V_+^{\rm ord}\to V_+^{\rm loss}
\to V_-^{\rm loss}\to V_-^{\rm ord}\to V_-^{\rm native}.
\]

`completeConditionalDigestComposition_le` inserts the source-coupled match-and-square bound and
keeps every defect separate:

\[
\begin{aligned}
\operatorname{Gap}_{\rm native}\leq{}&
\varepsilon_{{\rm ord},+}+\varepsilon_{{\rm ord},-}
+\varepsilon_{{\rm mode},+}+\varepsilon_{{\rm mode},-}\\
&+\rho_++\rho_-
+\sqrt{C\,(2\varepsilon_{\rm source}+\upsilon^2)}
+\varepsilon_{\rm samp}.
\end{aligned}
\]

The sampler term occurs once. `averagedUniformBinaryCompleteDigestComposition_le` proves that a
balanced public `r`-bit hash has averaged conditional concentration exactly `2^r`; the public hash
seed itself is context and is not charged. Its exact-erasure corollary
`averagedUniformBinaryCompleteDigestComposition_le_of_exactErasure` gives

\[
\sqrt{2^{r+1}\varepsilon_{\rm source}}.
\]

`averagedUniformBinaryCompleteDigestComposition_le_of_exactFidelityAndErasure` additionally sets
both native/ordinary fidelity defects to zero and is the sketch's final boxed formula.

Exact fiber invariance and preservation of the unconditioned uniform-prefix marginal are already
proved by `NativeTRGSWHashLossyCompleteView.hashFiberLossyView_evalDist_eq_of_hash_eq` and
`lossyUniformPrefixView_evalDist_eq_ordinary`.

## Translation and decoding boundaries

The same imported module supplies the two no-go arguments used by the sketch:

- `phaseObliviousHash_injective` and `prefixCard_le_digestCount_of_phaseOblivious` prove that the
  exact translation-only constructor requires `r >= t` at the standard cutoff.
- `approximatePhaseObliviousHash_defect_lowerBound` gives the robust lower bound
  `epsilon >= 1 / (4 * lambda_d)` for a nontrivial collision.
- `binaryHashStatisticalModeSwitch_lowerBound_of_factorizedView` proves that key-labelled
  statistical closeness is incompatible with reliable prefix decoding for a short digest.

These results rule out the natural exact, negligibly approximate, and key-by-key statistical
shortcuts. They do not rule out a computational dual mode.

## Hidden rank and native nonce rows

`hiddenRank_nonceResidual_identity` proves exactly what a hidden-rank relation buys: it rewrites
the linear term, while the full `-h P_i S` nonce message remains in the residual.
`NativeTRGSWQuadraticKDMAndTFHET.nonceKDMMessage_eq_sum` separately expands that message into its
prefix/suffix and prefix/prefix products.

`FactorsThroughDigest` defines exact digest-only generation. The collision theorem
`factorizedResidual_add_nonce_not_factorsThroughDigest` says that an already digest-factorized
residual stops factoring if an added nonce term varies inside one hash fiber. The native
specialization
`factorizedHiddenRankResidual_add_nonceKDMMessage_not_factorsThroughDigest` supplies a concrete
nondegeneracy condition: two same-digest prefixes cross a control bit and the gadget does not
annihilate the resulting subset secret.

This is a conditional obstruction, not a claim that every hash has that particular collision. It
pinpoints the extra construction obligation: nonce rows must be programmed, erased, or hidden in
a way compatible with the joint KSK and auxiliary transcript.

## Remaining premise

The sketch does not define `Setup_loss`, `GenView_loss`, or a source-consuming `Build_b` for the
complete native BRK/KSK/auxiliary law. Therefore Lean proves the reduction and its boundaries,
but leaves existence and computational indistinguishability of those algorithms as the explicit
cryptographic research premise.
