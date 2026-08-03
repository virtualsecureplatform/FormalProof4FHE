# Hash-compressed native-TRGSW security

`FormalProof4FHE.TFHE.NativeTRGSWHashCompressedSecurity` formalizes the theorem package in
`sketch/tthpowerof2.md`.

## Checked conclusions

For every fixed public hash whose output is uniform on a uniform prefix,
`hashedPrefixConcentration_eq_card` proves that the order-`1/2` Rényi concentration of the
leakage is exactly the digest carrier size.  The binary specialization is

\[
C_{1/2}(H(P))=2^r.
\]

`hashOnlyNativeGap_le` then instantiates the existing projected match-and-square theorem and
proves

\[
\operatorname{Gap}_{\rm native}
\leq \sigma_+ + \sigma_- +
\sqrt{2^{r+1}\varepsilon_{\rm source}}.
\]

`hashOnlyExperiment` types the builder so that it receives only the branch, digest, and public
source view.  It cannot inspect the complete key directly.  Its diagonal correctness and source
security are explicit premises.  `hashLossyDualModeNativeGap_le` adds the two mode-switch losses
and the final sampler defect.

Surjective additive maps on finite groups are proved to have uniform output.  The
`hasUniformOutput_of_surjectiveF2LinearHash` specialization represents a full-rank linear binary
hash by a surjective `F₂`-linear map.

## Why the old builder does not instantiate the theorem

`no_short_uniformHash_phaseObliviousBuilder` combines the exact `2^r` concentration with the
existing aggregate-stabilizer lower bound.  At cutoff at most two below the prefix dimension, an
exact phase-oblivious translation builder forces concentration at least `2^t`.  Therefore no
balanced `r`-bit hash with `r<t` can drive that builder.  A hash-lossy result must use a genuinely
different nonlinear or hidden-mode construction.

## Block-cycle alternative

`blockCycleSecurity_le` proves the hybrid telescope

\[
\operatorname{Gap}_{\rm total}
\leq \sum_j\left(\sigma_j+\sqrt{2C_j\varepsilon_j}\right).
\]

For equal binary blocks, `exactPartitionBinaryBlockCycleSecurity_le` proves the corresponding
`t/b` bound under an explicit exact-partition premise.  The local adjacent-gap hypotheses must be
discharged with genuinely separate local key cycles; merely partitioning one stored BRK does not
provide them.

`blockSourceRequirement_sufficient` gives an exact algebraic version of the source-exponent
budget.  For block count `k`, it assumes

\[
\varepsilon\leq
\left(2^{2\lambda+b+1}k^2\right)^{-1}
\]

and proves that the sum of the `k` source terms is at most `2^{-\lambda}`.  When `k=2^\ell`,
`perBlockSourceRequirement_powerOfTwoBlocks` recovers the exact integer exponent
`2λ+b+1+2ℓ`.

## XOR representation boundary

`vectorLWE_xorTransport_exact` proves the public coefficientwise-XOR transport for vector LWE,
including exact preservation of the message and error, and
`vectorLWE_xorTransport_uniform_evalDist` proves uniform-mask preservation.  The native ring
analogue is blocked by `nativeScalarAffineXorTransport_iff_constant`: above characteristic two,
ring multiplication plus an offset implements only the identity and global-complement masks.

## Remaining cryptographic premise

The module does **not** construct a hash-lossy native generator.  To obtain an unchanged-format
native theorem one must still build ordinary and lossy modes whose complete BRK/KSK/auxiliary
view, in the lossy mode, depends on the prefix only through the public digest, and prove the mode
distributions indistinguishable.  This is the research premise; all loss accounting after that
premise is checked in Lean.
