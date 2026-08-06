# Centered-binomial scaled quadratic KDM for BFV/BGV

## Scope

BFV/BGV relinearization publishes an evaluation-key batch whose row `j` has the form

```text
(A_j, A_j S + g_j S^2 + E_j).
```

Here `S` is the secret, `g_j` is a public gadget weight, and `E_j` is the narrow final
evaluation-key error. This document describes the exact checked reduction for this batch. It
does not claim that every key used by a complete bootstrapping implementation is covered:
automorphism or Galois keys encrypting transformed secrets are a separate obligation.

## Factorized source

Choose public factors `alpha_jr` and `beta_jr` satisfying

```text
sum_r alpha_jr * beta_jr = g_j.
```

The proof-only correlated source exposes two hint families

```text
alpha_jr S + F_jr,
beta_jr S + G_jr,
```

and an RLWE-like terminal row whose error is

```text
sum_r F_jr G_jr + E_j.
```

The secret, the two complete hint-error families, and the final-error family are sampled
independently. `F` and `G` may be sampled by the executable centered-binomial sampler with width
`hintEta`; the final `E` family may independently use width `finalEta`. All finite-product
samplers are proved never to fail.

For one factor per row, public values `left_j` and `right_j` give
`g_j = left_j * right_j`, and the terminal error is exactly `F_j G_j + E_j`.

## Exact public compiler

The public compiler combines the two hints with the correlated terminal row. Ring algebra
cancels every `F_j G_j` term and produces exactly

```text
(A_j, A_j S + g_j S^2 + E_j)
```

for all rows simultaneously. The compiler also maps its source-uniform branch exactly to the
uniform target transcript. Consequently there is no row-by-row hybrid and no multiplicative
loss depending on the number of gadget rows.

Most importantly for correctness, neither `F_j G_j` nor `g_j F_j G_j` appears in the compiled
evaluation key. The CBD products belong only to the proof source.

## Relinearization correctness

Suppose the third ciphertext component has gadget decomposition

```text
c2 = sum_j d_j g_j.
```

Using the compiled rows in the usual relinearization operation yields phase

```text
c0 + c1 S + c2 S^2 + sum_j d_j E_j.
```

This identity is exact over an arbitrary commutative ring. Thus the correctness calculation
uses only the selected narrow final errors `E_j`; it is independent of the width of the
proof-only hint errors.

## Security statement

For every distinguisher, the checked triangle and compiler give

```text
Adv_scaled-square-KDM
  <= Adv_correlated-source + Adv_zero-message-versus-uniform.
```

The first term is one joint advantage for the complete batch. The second is ordinary
zero-message RLWE for the same final-error law. A stronger interface accepts a split-ring
search-to-decision certificate and derives

```text
Adv_scaled-square-KDM
  <= searchBound + certificateLoss + zeroMessageBound.
```

The certificate, its search bound, and its loss are explicit arguments.

## Remaining security obligations

The correlated source contains the public hint families together with terminal errors
`sum_r F_jr G_jr + E_j`. The formal result does not identify this distribution with ordinary
RLWE. Proving its hardness from a standard assumption, or constructing a concrete split-ring
certificate with a useful bound, is the remaining cryptographic problem for this relinearization
path.

A complete BFV/BGV bootstrapping security theorem additionally needs a joint treatment of all
other evaluation material. In particular, common implementations publish switching keys for
automorphed secrets such as `sigma(S)`. The scaled-square theorem above covers the
relinearization-key component, not those transformed-secret rows.

## Lean declarations

The implementation is in
`FormalProof4FHE/RLWE/CenteredBinomialScaledQuadraticKDM.lean`. Its main declarations are:

- `fullyCBDLatentSampler` and `fullyCBDLatentSampler_probFailure`;
- `oneFactorGadget` and `terminalError_oneFactor`;
- `compiled_relinearization_phase`;
- `cbd_kdmAdvantage_le_source_add_zero`;
- `cbd_kdmAdvantage_le_search_add_loss_add_zero`.
