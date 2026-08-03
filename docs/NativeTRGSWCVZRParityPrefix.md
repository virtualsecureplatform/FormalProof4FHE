# Parity-prefix CVZR and ordinary binary RLWE

`FormalProof4FHE.TFHE.NativeTRGSWCVZRParityPrefix` removes the nonstandard
prefix-subspace assumption from the homogeneous zero-row source when the
binary prefix is placed in the even coefficients of a doubled ring.

## Exact ring reduction

Write the degree-`2n` secret as

```text
P(X²) + X Z(X²).
```

The CVZR source uses only `P(X²)` as its hidden secret and samples `Z` itself.
For a public mask

```text
A(X) = A₀(X²) + X A₁(X²),
```

multiplication by the prefix splits as

```text
A(X) P(X²) = (A₀ P)(X²) + X (A₁ P)(X²).
```

Lean proves this identity for both executable and proof-facing ring
multiplication. Splitting challenges, outputs, and paired errors is a
bijection on complete transcripts. Consequently one degree-`2n` parity-prefix
sample is exactly two ordinary degree-`n` binary-secret RLWE samples sharing
the same secret. There is no statistical distance, support loss, or row
hybrid.

The main equality is

```text
Adv_parity-prefix-RLWE(A)
  = Adv_binary-RLWE-degree-n-with-2m-samples(B_A).
```

This is the even-coordinate analogue of the existing odd-secret reduction.
The odd case needs a public multiplication by the small-ring root in one
component; the even case is untwisted.

## Concrete representation facts

The module also checks the representation steps needed by a zero-row
compiler:

- the even prefix and known odd suffix add to the full interleaved secret;
- adding the known suffix to a real row preserves its error;
- the same translation is a permutation of the complete uniform mask/body
  carrier;
- selecting an even output coefficient gives the exact scalar dot product
  under the binary prefix;
- the complete matrix of masks extracted from independent ring rows is
  jointly uniform; and
- selecting even coefficients from IID paired ring-CBD errors gives exactly
  the complete IID scalar-CBD error vector used by the KSK.

The last two statements are complete-vector distribution equalities. They do
not infer independence from separately proved coordinate marginals.

## CVZR composition

For any exact CVZR compiler whose source is this parity-prefix problem, the
checked composition gives

```text
Adv_CVZR(D) <= 2 * Adv_binary-RLWE(B_D).
```

The constructed ordinary-RLWE adversary has advantage exactly one half of the
CVZR target advantage. The factor two is solely the existing CVZR
branch-selection loss and is not multiplied by the number of BRK or KSK rows.

The previously completed concrete native CVZR module uses a contiguous
prefix/suffix key layout, so its final source remains prefix-subspace RLWE.
Applying the new theorem to a literal cloud-key implementation requires the
interleaved key layout, paired target-ring error sampler, and parity-aware KSK
extraction described above. Those distributional ingredients are now proved;
the final format-specific `ExactCVZRCompiler` record must be instantiated for
the particular cloud-key carrier being evaluated.

## Boundary

This result concerns homogeneous zero rows. It does not construct native
secret-message TRGSW nonce rows. Rewriting a nonce-shifted row in terms of its
displayed mask introduces hidden products between the encrypted key bit and
the ring secret. That separate cryptographic research premise is described in
the workspace note `trgswnoncerow.md`.
