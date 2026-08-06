# Masked Galois proof attempt

This note records the result of attempting to prove the masked joint automorphism theorem directly.

For one common secret `S`, proof mask `F`, final errors `E_j`, automorphisms `sigma_j`, and gadget
weights `g_j`, expose

```text
H = S + F
```

and form the complete source batch

```text
(H, {A_j, A_j S + E_j - g_j sigma_j(F)}_j).
```

The public compiler adds `g_j sigma_j(H)` to body `j`. Ring-homomorphism linearity cancels the
proof mask and gives

```text
A_j S + g_j sigma_j(S) + E_j
```

exactly. The target error is still `E_j`. For fixed `H`, body translation is bijective, so a
uniform complete source transcript maps to a uniform complete target transcript exactly.

The resulting finite-game theorem is

```text
Adv_joint-automorphism-KDM(D)
  = Adv_masked-source(compile_then_D),
```

and hence

```text
Adv_Galois-real-vs-zero(D)
  <= Adv_masked-source(compile_then_D)
     + Adv_zero-message-RLWE(D).
```

There is no compiler loss or per-row factor.

## Why this does not close the hard theorem

When `F` is uniform over the ring, `H=S+F` is uniform and independent of `S`. Given a target
transcript, a public reverse reduction samples an independent uniform `H` and subtracts
`g_j sigma_j(H)` from each body. Changing variables between `F` and `H=S+F` is a permutation, so
both the real and uniform games match the masked-source games exactly. Consequently, for every
source distinguisher `D_source`, Lean proves

```text
Adv_masked-source(D_source)
  = Adv_joint-automorphism-KDM(sample_H_then_decompile_then_D_source).
```

Thus uniform masking gives exact reductions in both directions. It does not simplify the
cryptographic assumption.

For a nonuniform proof mask the forward implication remains exact, but the hint is correlated
with the target secret. This makes the source an auxiliary-input version of the target problem;
ordinary RLWE, the current Leaky-RLWE interface, or scalar Subspace-LWE does not by itself supply
the needed joint simulator. In particular, the same `F` controls both the hint and every
automorphed error correction, and every coefficient of a row shares one structured ring mask.

The remaining proof is therefore not technical algebra. It requires a new cryptographic result,
such as a ring-aware joint automorphism-KDM reduction or a computationally hidden lossy/trapdoor
mode for the structured operators `M_A + g P_sigma`. The exact masked compiler is still useful as
a lossless normal form for such a theorem.

The formal development is in `FormalProof4FHE/RLWE/MaskedGalois.lean`.
