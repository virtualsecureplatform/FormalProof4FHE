# Regular-cover same-key BGV

`RegularCoverSameKeyBGV.lean` formalizes the algebraic and exact-uniform core
of `sketch/regular_cover_same_key_bgv.tex`.

## Construction

For a finite automorphism group `Gamma` acting on a base ring `R`, define the
cover `Gamma -> R` with componentwise operations. Its lifted action is

```text
(lift sigma x)[h] = sigma(x[sigma^(-1)*h]).
```

Lean constructs this action as a ring equivalence and proves its composition
law.

The diagonal embedding transports native plaintext computations. The second
embedding

```text
iota(x)[h] = h(x)
```

is fixed by every lifted automorphism. Lean proves the converse as well: every
cover element fixed by the complete lifted regular action is `iota(x)` for its
identity component. Thus the fixed source retains one full base-ring element
rather than collapsing to one bit.

## Completion and RLWE assembly

One bottom bit per orbit and one completion bit for every nonidentity cover
coordinate are exactly equivalent to all cover Binary-NTT bits. The induced
sampler is exactly uniform.

For common-secret base rows indexed by `h`, the assembly

```text
Abar[h] = h(a_h)
Bbar[h] = h(b_h)
```

has common invariant cover secret `iota(T)`. The assembly map has an explicit
inverse, so uniform base tables map to exactly uniform cover elements.

## Simultaneous compiler

For arbitrary public weights `g_sigma`, the compiler is

```text
A = (Abar - sum_sigma g_sigma*sigma(H))*H^(-1)
B = Bbar + A*C + sum_sigma g_sigma*sigma(C).
```

If the source secret `I` is fixed by every automorphism, Lean proves

```text
B - A*(H*I+C) = E + sum_sigma g_sigma*sigma(H*I+C).
```

Both one-row and complete-row-family maps have explicit inverses and preserve
their complete uniform endpoints.

## Operational-secret pivot

The pivot publishes

```text
beta = alpha*S + z
u = 2*beta-alpha
v = alpha*beta-beta^2.
```

For idempotent witness `S`, Lean proves `z^2 = u*z+v`. Ordinary and
affine-automorphism witness rows convert exactly to rows under the
coefficient-small operational secret `z`. The ordinary conversion is
bijective and preserves the uniform endpoint.

The arithmetic analysis proves that split dimension at most `q/2` gives unit
probability at least `1/2`, and `k` independent trials leave failure at most
`2^(-k)`.

## BGV operations

Lean proves:

- quadratic-hint multiplication has phase equal to the product of the input
  phases;
- gadget automorphism switching has the native automorphed phase plus exactly
  the gadget-weighted errors; and
- circuits made from additions, multiplications, public constants, and base
  automorphisms lift correctly on diagonal cover plaintexts.

## Exact scope

The formalization validates the new regular-cover compiler. It does not yet
instantiate the manuscript's final IND-CPA and repeated-refresh theorem.

Remaining obligations are:

1. choose one concrete native BGV/BFV bootstrap;
2. match every secret-dependent row it publishes to the compiler;
3. instantiate the public-key-encryption hybrid for that exact syntax;
4. prove executable error invariance for the selected automorphisms;
5. package the complete pivot rejection sampler and finite advantage theorem;
6. transfer the native noise recurrence to the cover norm;
7. handle the exact RNS and modulus-switching transcript; and
8. select parameters secure at the base Binary-NTT dimension and correct for
   the lifted circuit.

These obligations are predominantly technical and computational once the
native circuit is fixed. Independent cryptographic review remains appropriate
because the architecture is new. The result changes the ciphertext ring from
`R_q` to the polynomial-size product `R_q^Gamma`; it does not prove the
original single-ring joint theorem.

## Principal declarations

- `liftedAction`
- `liftedAction_mul`
- `fixed_iff_mem_fixedEmbedding`
- `coverCompletionEquiv`
- `coverCompletion_uniform_evalDist`
- `assembleCover_real`
- `assembleCover_uniform_evalDist`
- `compilerBody_real`
- `compilerBatch_uniform_evalDist`
- `splitUnitProbability_ge_half`
- `repeatedPivotFailure_le`
- `pivot_quadratic_hint`
- `pivotOrdinaryRow_real`
- `pivotAffineRow_phase`
- `quadraticHintMul_phase`
- `automorphismSwitch_phase`
- `RingCircuit.evalCover_diagonal`
