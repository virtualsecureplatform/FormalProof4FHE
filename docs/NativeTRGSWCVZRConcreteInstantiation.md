# Concrete native CVZR instantiation

`FormalProof4FHE.TFHE.NativeTRGSWCVZRConcreteInstantiation` closes the technical side-builder
premises of the generic known-suffix CVZR reduction for the native shared-prefix/suffix TFHE
cloud-key format and coefficientwise centered-binomial noise.

## Source layout

One prefix-RLWE source contains two disjoint blocks:

- every homogeneous row of the complete zero-message BRK; and
- every row of the suffix-only KSK.

The row counts are respectively

```text
prefixDimension * TGSW.rowCount 1 tgswLevels
(suffixDegree + 1) * keySwitchLevels.
```

Lean defines an equivalence from the sum of these two index sets to the complete source index.
Consequently the BRK and KSK address maps are injective and have disjoint images. There is no
implicit row reuse.

## Exact native laws

For KSK rows, a fixed output coefficient of a uniform ring mask gives a uniform scalar prefix
mask. Selecting that coefficient from a coefficientwise ring-CBD error gives exactly the native
scalar CBD sampler. The proof compares the complete IID error vector, so it includes all rows and
does not infer a joint law from coordinate marginals.

For BRK rows, adding the independently sampled known suffix transports a prefix-secret
homogeneous row to the complete split secret without changing its error. The whole-BRK transport
and coefficient-to-native representation map are proved bijective. Thus two independent uniform
coefficient challenge/body functions compile to one exactly uniform native BRK.

Combining the disjoint blocks proves the complete fixed-key identity

```text
coefficient source builder
  =d native zero-message BRK + genuine suffix-only KSK,
```

with native ring CBD for BRK errors and scalar CBD for KSK errors. The corresponding uniform-BRK
endpoint retains the same genuine KSK. Deferred-sampling equalities then identify the key-sampled
source-order program with the literal native cloud-key program.

## Security statement

The module packages these laws as an exact public compiler for one explicit, non-auxiliary
prefix-RLWE problem. For every native CVZR distinguisher `D`, the checked theorem gives

```text
Adv_native-CVZR(D) <= 2 * Adv_prefix-RLWE(B_D).
```

The constructed source distinguisher actually has advantage exactly half of the native CVZR
advantage. The factor two is therefore the single branch-selection loss; it is not multiplied by
the number of BRK or KSK rows.

## Remaining boundary

For the native zero-row cloud-key endpoint with the stated CBD samplers, no KSK side-builder,
joint-error-law, row-partition, representation, or sampler-order premise remains. The remaining
security premise is the decisional hardness of the explicitly defined binary
prefix-supported RLWE problem.

When the prefix occupies a proper coefficient block, this is a prefix-subspace RLWE assumption.
The formalization does not derive that assumption from ordinary full-dimensional RLWE. It also
does not address the separate secret-message native TRGSW nonce-row problem: CVZR contains only
homogeneous zero rows, which is why known-suffix transport applies.
