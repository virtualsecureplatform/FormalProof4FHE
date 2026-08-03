# Native TRGSW aggregate security and complexity leveraging

## Result

`FormalProof4FHE.TFHE.NativeTRGSWAggregateSecurityAndComplexityLeveraging` formalizes the new
technical content of `sketch/native_trgsw_aggregate_security_and_complexity_leveraging.tex`.
The earlier native row barrier, xor normalization, diagonal Fourier identity, low-degree leakage
removal, complete correlated channel, and statistical-tail infeasibility results are reused from
their existing modules.

For cutoff `d`, let `B_d` contain the zero Walsh frequency and every nonzero frequency of support
at most `d`. The module defines

```text
nu_d(c) = 1[c = 0] - (1 / 2^t) sum_(S in B_d) chi_S(c).
```

Its unnormalized Walsh transform is proved exactly equal to zero on `B_d` and one outside it.
The positive and negative Jordan parts have a common mass `lambda_d`; after division by this
mass they are nonnegative tables summing exactly to one. When `d < t`, `lambda_d` is strictly
positive. Walsh orthogonality and finite Cauchy--Schwarz give the sharp bounds

```text
1 - |B_d| / 2^t <= lambda_d <= (1 + sqrt(|B_d|)) / 2.
```

## Exact aggregate identity

For an arbitrary real complete-view response `f(p,m)`, the positive and negative aggregate games
evaluate `f(p,p xor c)` with `c` drawn from the two normalized Jordan tables. Their signed gap is

```text
AggPlus(f) - AggMinus(f)
  = (sum_(|S| > d) fhat(S,S)) / lambda_d.
```

This is a signed high-degree sum. It is sufficient because the exact real/random gap first splits
as the low-degree sum plus that signed high-degree sum; no triangle inequality is applied inside
the high-degree part. Consequently the complete bridge becomes

```text
|real - random|
  <= N_d * lowCoefficientBound
       + lambda_d * |AggPlus - AggMinus|.
```

The sign-guess calculation proving that aggregate security is contained in circular security has
the exact factor `1/2`. A finite point-oracle response has a strictly positive aggregate gap for
every `d < t`, formalizing the algebraic core of the claimed black-box separation. Query-time
complexity classes are not represented by the Lean probability library, so the asymptotic
polynomial-query statement remains a metatheoretic interpretation of this witness.

## Match-and-square reduction

The module specializes the existing two-copy squared-bias leakage-removal theorem by taking the
leakage to be the complete key itself. The real and ideal conditionals are the positive and
negative complete-view constructors evaluated with a guessed fake key and the actual source key.
For a fake-key law proportional to the square root of the actual key probability, it proves

```text
AdvAggregate
  <= sqrt(2 * C_half(K) * AdvMatchSquare),

C_half(K) = (sum_k sqrt(Pr[K = k]))^2.
```

It also proves that every covering fake-key law has matching factor at least `C_half(K)`, so the
square-root tilt is optimal within this match-and-square argument. Complete-view construction
defects add outside the square root. Uniform binary-prefix/ternary-suffix keys have the exact
factor

```text
2^prefixDimension * 3^suffixDimension.
```

## Final conditional theorem and remaining boundary

The final Lean theorem combines:

1. the low-degree complete heterogeneous affine-source coefficient bound;
2. the exact aggregate identity;
3. an approximate complete-view diagonal aggregate constructor;
4. the doubled zero-row source bound used by match-and-square; and
5. the independent-message/zero-message endpoint.

It obtains exactly the bound from the sketch, with the low-frequency count, `lambda_d`, complete
key concentration, construction defects, and endpoint all exposed.

This removes the standalone statistical spectral-decay premise, but it is not yet a practical
native TFHE proof. The companion concrete-channel module now defines the actual positive and
negative native cloud-key experiments and proves their exact or certified-approximate connection
to these abstract aggregate games. Two cryptographic research obligations remain:

- reduce the now-concrete complete native aggregate experiments, including every KSK and
  auxiliary object, to an accepted full-key zero-row RLWE problem; and
- avoid or sharply reduce the exponential `C_half(K)` factor for conventional binary/ternary
  keys.

The complete heterogeneous affine-source reduction and the independent-message endpoint also
remain premises, as before. The finite high-pass algebra, normalization, squared-bias reduction,
and concentration arithmetic are no longer open.

See `NativeTRGSWAggregateConcreteChannel.md` for the concrete experiments and explicit finite
mask-sampler defects.
