# Native TRGSW quadratic KDM security and the TFHE control length

`FormalProof4FHE.TFHE.NativeTRGSWQuadraticKDMAndTFHET` formalizes the mathematical claims in
`sketch/native_trgsw_quadratic_kdm_and_tfhe_t.tex`.

## Native row algebra

For a raw homogeneous row `(A₀, A₀S + E)`, nonce placement produces

```text
(A₀ + hm, A₀S + E).
```

After renaming `A = A₀ + hm`, `nativeNonceRow_eq_normalized` proves that this is exactly

```text
(A, AS - hmS + E).
```

Thus the nonce half is an RLWE encryption of `-hmS`; the body half is an RLWE encryption of
`hm`.  `nonceKDMMessage_expansion` and `nonceKDMMessage_eq_sum` expand the subset-key case
`S = E(P) + Z` into its mixed and prefix-quadratic terms.  The mixed Boolean derivative theorem
recovers the exact `-hE_j` affine barrier.

`translateKnownMessageRows_real` proves the exact nonce/body translation for one pair, and
`translateBRK_real` proves it for the complete indexed BRK at once.  The inverse maps are
explicit.  Consequently `translateKnownMessageRows_uniform_evalDist` and
`translateBRK_uniform_evalDist` are whole-carrier distribution equalities, not row-marginal
claims.  The complete-view wrapper forwards the KSK and auxiliary state definitionally unchanged.

## Parity-split half-ring source

The module selects one coherent proof-facing ring dictionary and proves

```text
Phi(a₀,a₁) Phi(P,Z)
  = Phi(a₀P + Y a₁Z, a₁P + a₀Z).
```

The prefix-only and suffix-only specializations are separate exported theorems.

`assembleParityZeroRow_real` proves that two half-ring RLWE rows under `P`, followed by the public
odd-suffix correction determined by `Z`, give one homogeneous full-ring row under `Phi(P,Z)`.
`splitParityZeroRow` is an explicit inverse, so `assembleParityZeroRow_uniform_evalDist` proves
exact uniform-source transport.

The imported parity-CVZR module supplies the remaining representation facts used by this source:

- complete extracted KSK masks are jointly uniform;
- the complete selected paired-CBD error vector is IID scalar CBD; and
- batched KSK extraction has the exact native affine equation.

These are joint vector laws rather than collections of marginal facts.

## Direct match-and-square reduction

`ExactDirectSourceCompiler` differs from the earlier two-branch CVZR compiler.  It maps a real
source transcript directly to the real match-and-square target and maps a uniform transcript
directly to the fair endpoint.  `reduction_advantage_eq_targetAdvantage` proves exact equality of
the source and target advantages.

Specialized to ordinary half-degree binary-secret RLWE,
`halfRingMatchSquareReduction_advantage_eq` proves

```text
Adv_RLWE(B_D) = Adv_match-square(B_D).
```

There is therefore no extra branch-selection factor.  Composing this equality with the checked
Rényi-half diagonal theorem yields

```text
Adv_native(D)
  <= sigma_real + sigma_zero
     + sqrt(2 * C_half(P) * Adv_half-RLWE(B_D)).
```

This is `nativeRestrictedQuadraticKDMGap_le_halfRingRLWE`.

The compiler record keeps the exact complete-view sampler law visible.  Its real law must include
the disjoint BRK, KSK, and retained auxiliary samples with the prescribed joint error and
representation law.  A mismatch belongs in the two whole-view defects; it is not silently
converted into a rowwise hybrid.  This is an explicit technical premise, not a new hardness
assumption.

## Public quadratic aggregation

`aggregateNonceBody_eq` proves that weighting one nonce row per encrypted prefix coordinate gives
one RLWE row with message `-h E(P) S`.  When `E(P) = S`,
`aggregateNonceBody_eq_square` specializes this to `-hS²`.  If one public weight is a unit,
`aggregateMask_uniform_evalDist_of_isUnit` proves that the aggregate mask is exactly uniform.

## Control length and source count

The theorem's control length is the number of secret bits encrypted in the BRK:

- the input LWE dimension in ordinary gate bootstrapping;
- the selected subset cardinality in subset-key TFHE; and
- the half degree in the even/odd parity construction.

It is represented separately from the ring degree, gadget level count, and key-switch digit count.
No implementation-profile constants are built into these definitions.

For ring rank `k`, gadget level count `l`, and control length `t`, one local parity view consumes

```text
2 * (k + 1) * l * t + m_KSK + m_aux
```

half-ring samples.  Match-and-square doubles this quantity.  The rank-one specialization is
proved exactly.

Finally, `uniformBinaryControlConcentration` proves `C_half(P) = 2^t` for a uniform binary
control prefix, while `oneCoordinateControlConcentration_le_two` proves the constant-loss isolated
one-bit statement.  `sqrt_sourceTerm_le_target` records the parameter-independent condition for
turning a desired target advantage into a required source advantage.

## Boundary

The result is a positive, complexity-leveraged restricted quadratic-KDM theorem for the stated
parity-split key law.  It does not claim that this law is the default TFHE implementation key law,
does not remove the `2^t` concentration, and does not prove correctness for a concrete finite
parameter set.  Those requirements remain separate from the security reduction proved here.
