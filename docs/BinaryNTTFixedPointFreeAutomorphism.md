# Binary-NTT fixed-point-free tower automorphism

`BinaryNTTFixedPointFreeAutomorphism.lean` formalizes the simultaneous
half-degree reduction in `sketch/proof-fixed-point-free-auto.md`.

## Result

For the index-two cyclotomic tower

```text
R'_q = Z_q[Y]/(Y^n+1)  ->  R_q = Z_q[X]/(X^(2n)+1),  Y = X^2,
```

the involution `sigma(f(X)) = f(-X)` exchanges the two NTT coordinates above
each half-degree coordinate. A half-degree Binary-NTT secret `T` and one
uniform orbit coin per pair are encoded as

```text
S = H*T + C.
```

Lean proves that this is an exact equivalence between two independent
`n`-bit vectors and one uniform `2n`-bit Binary-NTT vector. All orbits are
completed simultaneously; no coordinate hybrid or exponential Fourier sum is
used.

For every gadget row, the compiler uses

```text
A_sigma = (A_tilde - g*sigma(H))*H^(-1)
B_sigma = B_tilde + A_sigma*C + g*sigma(C).
```

The checked real-branch identity is

```text
B_sigma = A_sigma*S + E + g*sigma(S).
```

The analogous zero-message compiler gives

```text
B_zero = A_zero*S + E.
```

Both row maps have explicit inverses. The inverses are lifted pointwise to an
arbitrary complete gadget-row batch, proving that the entire random transcript
is uniform—not merely each row marginal.

The even/odd coefficient assembly is represented by
`AdditiveIndexTwoAssembly`. Lean proves that two half-degree masks assemble
bijectively to a uniform full-ring mask and that two honest common-secret
equations assemble to the exact full-ring equation with the product
coefficient-error law.

Finally, the randomized comparison rule has output probability

```text
(1 + x - y)/2.
```

For arbitrary correlated pairs of public transcripts, its probability depends
only on the two marginals. The resulting source distinguisher has advantage
exactly half the automorphism-versus-zero advantage, hence

```text
Adv_AutoKDM <= 2 * Adv_half-degree-BinaryNTT-RLWE.
```

No sign advice is needed because decision advantage is absolute.

## Exact scope

The reduction is for the tower involution `X -> -X`, not for every abstract
fixed-point-free involution. A different involution needs a compatible
index-two subring decomposition whose uniform masks and actual coefficient
errors split correctly.

The security assumption is ordinary Binary-NTT RLWE in degree `n`, while the
target automorphism game has degree `2n`. A concrete parameter claim must
therefore estimate security at the half degree. If the original full degree
was selected only barely securely, the reduction may require increasing it.

This closes one fixed-point-free automorphism. A complete scalar-BGV bootstrap
still needs a joint theorem for every automorphism in its trace/Frobenius
family, or a circuit that performs the projection without publishing those
additional automorphism keys.

## Principal declarations

- `completionEquiv`
- `completionBits_uniform_evalDist`
- `completedSecret_affine`
- `AdditiveIndexTwoAssembly.assemble_real_equation`
- `automorphismBody_real`
- `zeroBody_real`
- `automorphismBatch_uniform_evalDist`
- `zeroBatch_uniform_evalDist`
- `comparison_advantage_eq_half`
- `automorphismKDM_advantage_le_twice_source`
