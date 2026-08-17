# Large-modulus BFV standard-assumption proof program

## Outcome

The sound finite spine of `sketch/bfv_circular_security_standard_assumption_program.tex` is
formalized in
`FormalProof4FHE/RLWE/BFVCircularSecurityStandardAssumptionProgram.lean`.

The final large-modulus circular-security statement remains a conjectural proof program. No Lean
theorem claims that stock BFV, or the proposed flooded BFV family, is circular-secure from ordinary
RLWE alone.

## Three-sample compiler

For three negative-sign RLWE rows

```text
b_j = -a_j*s + e_j,
```

Lean defines

```text
G = a₁*a₂,
A = a₃-a₁*b₂-a₂*b₁,
C = b₃-b₁*b₂
```

and proves exactly

```text
C = -A*s + G*s² + (e₃-e₁*e₂).
```

For fixed first and second rows, the map from the fresh pair `(a₃,b₃)` to `(A,C)` is an explicit
translation equivalence. Thus a uniform fresh pair produces an exactly uniform compiled pair,
even jointly with a retained value of `G`.

Turning this into a computational theorem requires a complete three-row decisional-RLWE game and
its deterministic postprocessing reduction. The finite identities needed by that reduction are
now checked.

## Normalization barrier and nonunit multiplier

Given a unit target `g`, a unit last Ring-SIS coordinate `a_last`, and programmed coefficients

```text
G_j = -g*a_j*a_last⁻¹,
```

Lean proves the generalized statement

```text
sum_j z_j*G_j = P*g
  -> sum_j z_j*a_j + P*a_last = 0.
```

For `P=1`, this is exactly the short `(z,1)` homogeneous Ring-SIS relation. For a deliberately
large nonunit multiplier represented by `P`, the relation is `(z,P)`. This checks the algebraic
motivation for the proposed escape, but it does not itself prove that the resulting normalization
algorithm exists or is compatible with RLWE hardness.

## Scalar-box hashing and missing targets

For box points in `Fin dimension -> Fin width`, distinct points have a scalar difference of
magnitude below `width`. Lean proves that this difference is a unit modulo `M` when

```text
width < minFac(M).
```

This is slightly weaker than the manuscript's sufficient premise `2*width < minFac(M)`. The
result is transported through an arbitrary algebra over `ZMod M` and gives the exact collision
law

```text
Pr_G[h_G(z)=h_G(z')] = 1 / |R|.
```

The module also proves the fixed-target Markov step. If the average conditional distance of the
hash image from uniform is at most `epsilon`, the fraction of public seeds missing a fixed target
is at most

```text
|R| * epsilon.
```

The existing leftover-hash theorem still has to be connected to the manuscript's precise
conditional-average expression and scalar-box input cardinality to obtain the displayed numerical
constant automatically.

## Approximate-CVP interface

`ApproximateCVPPreimageCertificate` records:

- the exact public additive map and target;
- a valid base coset solution;
- a correction in the exact kernel;
- a valid box witness;
- the approximation and distance inequalities.

Lean proves that the returned difference is an exact preimage and has norm at most

```text
rho * W * sqrt(m).
```

What remains is constructing this certificate from the actual coefficient matrix, HNF/SNF
output, an exact basis of the intended kernel lattice, and the selected LLL/Babai implementation.
The generic certificate intentionally does not claim those algorithms are already connected.

## Fixed-gadget combination and modulus-down

The public linear-combination theorem proves that random-coefficient quadratic rows, normalized to
`P*g`, plus one independent zero row give an exact auxiliary-modulus row with coefficient `P*g`.

For decompositions

```text
A = P*Ahat + rA,
C = P*Chat + rC,
```

Lean defines the modulus-down residual `delta` and proves both:

```text
Chat + Ahat*s = g*s² + delta  (mod Q),
P*delta = Etilde-rC-rA*s.
```

The second equality is the exact divisibility statement; no division or integral-domain
assumption is hidden in it.

The canonical quotient/remainder equivalence

```text
Fin(P*Q) ≃ Fin Q × Fin P
```

is then lifted coefficientwise. A uniform auxiliary-modulus element has jointly uniform,
independent quotient and remainder, and its quotient is exactly uniform after the remainder is
discarded.

## Joint flooding

The module proves the distributional composition needed for correlated public state: any uniform
per-coordinate translation bound lifts across an independent vector by a hybrid sum and remains
valid after conditioning on arbitrary shared context.

The concrete claim

```text
TV(U[-T,T], U[-T,T]+d) = |d|/(2*T+1)
```

under the no-wrap condition has not yet been connected to a concrete modular interval sampler.
That exact finite overlap theorem is still required before the manuscript's
`ell*n*D/(2*T+1)` loss is certified.

## Important correction to the zero branch

Coefficientwise quotient by `P` does not map a real RLWE row at modulus `P*Q` literally to an
ordinary RLWE row at modulus `Q`. It produces a row with a correlated quotient/remainder rounding
residue—the same algebra exposed by `modulusDownResidual`.

The proposed zero-branch simulation may still work by bounding and flooding this residue, but it
must use the modulus-down identity and joint flooding argument. It should not cite exact
distributional equality with ordinary small-modulus RLWE.

## Remaining end-to-end obligations

1. Build the complete multi-sample RLWE reduction, including bounded rejection sampling that makes
   `G=a₁a₂` uniform by conditioning on a public unit `a₁`.
2. Connect scalar-box two-universality to the exact average leftover-hash and simultaneous-target
   constants.
3. Implement and verify the coefficient matrix, target coset, kernel lattice, HNF/SNF, LLL, and
   Babai certificate construction.
4. Instantiate coefficient representatives and prove the concrete negacyclic norm bounds for
   `delta`.
5. Prove the modular interval-overlap formula and instantiate the joint flooding theorem.
6. Compose the real and uniform games, including preimage and algorithm failure behavior.
7. Prove the corrected zero-branch simulation through bounded rounding residue and flooding.
8. Establish BFV correctness with box noise, gadget decomposition, plaintext scaling, and the
   complete decryption margin.
9. State and justify the exact decisional-RLWE assumption at the auxiliary composite-modulus
   family, secret law, bounded error law, and sample count.

## Principal declarations

- `threeSample_identity`;
- `threeSampleFresh_withCoefficient_uniform_evalDist`;
- `normalization_yields_relation` and `unitNormalization_yields_relation`;
- `scalarBoxHash_pairCollision_probability`;
- `missingTarget_fraction_le`;
- `ApproximateCVPPreimageCertificate`;
- `approximateCVP_output_valid` and `approximateCVP_output_norm_le`;
- `fixedGadgetCombination`;
- `modulusDown_identity`;
- `coefficientQuotientRemainder_uniform_evalDist`;
- `coefficientQuotient_uniform_evalDist`;
- `conditioned_product_shift_tvDist_le`.
