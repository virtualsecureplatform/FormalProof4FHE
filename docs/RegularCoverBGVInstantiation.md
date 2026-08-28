# Native BGV instantiation of the regular cover

`RegularCoverBGVInstantiation.lean` records the technical audit of
`refs/2022-1363.pdf` and the accompanying `Bootstrapping_BGV_BFV` Magma
implementation.

## Evaluation-key row coverage

The implementation generates four relevant row types:

- the ordinary public key encrypts zero;
- `GenBootKeyRecrypt` encrypts the operational secret;
- `GenSwitchKey` encrypts an automorphed operational secret; and
- `GenRelinKey` encrypts the square of the operational secret.

`NativeKeyRow` represents exactly these four messages. Lean proves that each
belongs to the public affine-automorphism span

```text
constant + sum_sigma coefficient_sigma*sigma(z).
```

The square row is included through the public equation `z^2=u*z+v`. An
arbitrary complete row table is covered pointwise.

For the cleanest exact reduction, the cover variant generates the boot key
directly with fresh uniform RLWE masks, as is already done for switch and
relinearization keys. The Magma `GenBootKeyRecrypt` instead invokes public-key
encryption, whose masks are derived from the public key and a short ephemeral
secret. Direct evaluation-key generation avoids this extra intermediate
distribution without changing the boot-key phase.

## Bootstrap operation coverage

The native bootstrap uses:

- additions and public-constant operations;
- polynomial digit extraction;
- ciphertext multiplication;
- rotations and Frobenius automorphisms;
- gadget key switching and relinearization;
- exact public division;
- centered reduction, modulus switching, and RNS reduction.

The first six are covered by the regular-cover circuit, multiplication, and
automorphism-switching theorems. Exact public division is unit scaling.

For the remaining non-ring operations, `pointwiseMap` lifts an arbitrary base
operation componentwise. Lean proves:

- diagonal inputs remain diagonal;
- compositions lift compositionally; and
- an automorphism-equivariant base operation commutes with the lifted regular
  action.

`coverRingHom` supplies the exact componentwise lift for modulus or RNS ring
homomorphisms.

## Challenge encryption

The proof-oriented cover variant uses dense-binary rank-one ring-Regev
encryption over the cover rather than the Magma code's sparse-ternary ephemeral
encryption. After the compiler replaces the public-key rows by uniform rows,
the repository's strong leftover-hash theorem applies directly.

Lean proves the explicit statistical term

```text
sqrt(|R|^(2*|Gamma|) / 2^m) / 2,
```

where `m` is the number of public-key rows. This closes the challenge masking
hybrid without an additional cryptographic assumption. Parameter selection
must choose `m` large enough for this term to be negligible.

Concrete centered reduction and modulus switching must instantiate the
equivariance premise. For odd moduli this should follow because the selected
cyclotomic automorphisms signed-permute coefficients and centered reduction is
compatible with negation. The exact rounding formula still needs to be
connected to the implementation.

The generic coefficient theorem is closed: every scalar operation satisfying
`f(-x)=-f(x)` commutes with every signed coefficient permutation. Therefore
the remaining implementation step is only to prove that the concrete centered
rounding formula is odd.

## Cover noise bounds

`CoverBound` expresses a uniform bound over all cover components. Lean proves
that:

- addition adds component bounds;
- multiplication uses the same base-ring expansion constant, with no
  `|Gamma|` multiplier;
- a norm-preserving base automorphism preserves the same cover bound; and
- any proved base-operation bound transfers componentwise.

Only probabilistic failure accounting incurs a union bound over cover
components.

## Pivot reduction

`PivotAdvantageCertificate` packages the exact relation between the transcript
gap and the rejection-sampled source gap. Lean proves the division by the pivot
success probability and the bound obtained from a failure estimate. Together
with the previously proved unit-density and repeated-failure bounds, this
closes the finite advantage arithmetic.

`EndToEndSecurityCertificate` composes the transcript hop and the challenge
masking hop into the final bound

```text
Adv_IND-CPA <= Adv_source/(1-pivotFailure) + maskingDistance.
```

There is no circular-security term. `NativeRefreshCertificate` similarly
packages native input/fresh bounds, strict contraction, and the component and
repeated-refresh union bounds.

## Remaining concrete work

The structural technical work is closed. The remaining implementation-facing
items are:

1. choose the exact BGV parameter branch and bootstrap entry point;
2. modify boot-key generation to use direct uniform-mask evaluation rows;
3. prove the implementation's centered-reduction and modulus-switch formulas
   satisfy `EquivariantMap`;
4. translate its existing scalar noise estimates into `CoverBound` premises;
5. instantiate the final IND-CPA challenge-encryption hybrid; and
6. run the parameter search at the base Binary-NTT dimension with the
   `|Gamma|` key/ciphertext overhead.

Items 2--5 are concrete integration proofs rather than new cryptographic
assumptions. The ordinary Binary-NTT RLWE assumption and independent review of
the new cover construction remain the foundational caveats.

## Principal declarations

- `NativeKeyRow`
- `nativeKeyRow_mem_affineSpan`
- `nativeKeyTable_mem_affineSpan`
- `pointwiseMap_diagonal`
- `pointwiseMap_liftedAction`
- `coefficientwise_signedPermute`
- `coverRingHom`
- `CoverBound.add`
- `CoverBound.mul`
- `CoverBound.liftedAction`
- `CoverBound.pointwiseMap`
- `PivotAdvantageCertificate.target_le_div_source`
- `PivotAdvantageCertificate.target_le_source_div_one_sub`
- `coverRingRegev_subsetHash_leftover_explicit`
- `EndToEndSecurityCertificate.indCpa_le_source_add_masking`
- `NativeRefreshCertificate.repeatedFailure_le`
