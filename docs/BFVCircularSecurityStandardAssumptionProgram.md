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

The complete unit-conditioned uniform compiler is now an explicit equivalence onto an independent
uniform `(G,A,C)` triple. Lean also proves the exact data-processing reduction from a complete
unit-conditioned three-row source view to the compiled quadratic triple. Connecting that source
view to unconditioned RLWE now requires only the bounded public unit-rejection implementation and
its runtime/failure certificate.

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

Lean now proves that joint public-seed leftover-hash distance is exactly the average conditional
distance. Scalar-box universality is connected to the repository's leftover-hash theorem, giving
the exact `sqrt(|R|/W^m)/2` average bound. The fixed-target Markov step and the simultaneous finite
gadget-target union bound are composed automatically.

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

is lifted to the actual executable negacyclic `Rq` carrier. A uniform auxiliary-modulus element
has jointly uniform, independent quotient and remainder, and its quotient is exactly uniform
after the remainder is discarded. The same theorem is proved for a complete mask/body pair, and
the canonical coefficient identity `x=P*(x/P)+(x mod P)` is checked.

## Joint flooding

The module proves the distributional composition needed for correlated public state: any uniform
per-coordinate translation bound lifts across an independent vector by a hybrid sum and remains
valid while retaining arbitrary shared context and after any deterministic BFV-view assembly.

The concrete claim

```text
TV(U[-T,T], U[-T,T]+d) = |d|/(2*T+1)
```

is now proved for a concrete centered interval embedded in `ZMod Q`. Lean proves injectivity on the
joint no-wrap interval, exact support and overlap cardinalities, the clipped distance formula, the
exact small-shift ratio, and the joint `ell*n*D/(2*T+1)` bound.

## Important correction to the zero branch

Coefficientwise quotient by `P` does not map a real RLWE row at modulus `P*Q` literally to an
ordinary RLWE row at modulus `Q`. It produces a row with a correlated quotient/remainder rounding
residue—the same algebra exposed by `modulusDownResidual`.

The corrected zero-branch theorem now does exactly this: it treats the rounding residue as a
context-dependent bounded shift and floods it jointly with the assembled public view. It never
claims equality with ordinary small-modulus RLWE.

## Remaining end-to-end obligations

1. Implement bounded public unit rejection and certify its runtime/failure bound; the conditioned
   three-sample source reduction itself is formalized.
2. Implement and verify the coefficient matrix, target coset, kernel lattice, HNF/SNF, LLL, and
   Babai certificate construction.
3. Run the numerical parameter search and instantiate the proof-carrying BFV correctness budget;
   exact relinearization phase algebra and generic noise slots are already present.
4. State and justify the exact decisional-RLWE assumption at the auxiliary composite-modulus
   family, secret law, bounded error law, and sample count.

## Principal declarations

- `threeSample_identity`;
- `threeSampleFresh_withCoefficient_uniform_evalDist`;
- `conditionedUniformTriple_unitSampler_evalDist`;
- `compiledTriple_tvDist_uniform_le_source`;
- `normalization_yields_relation` and `unitNormalization_yields_relation`;
- `scalarBoxHash_pairCollision_probability`;
- `scalarBoxHash_isTwoUniversal` and `tvDist_hashed_eq_average`;
- `scalarBoxHash_simultaneousMissing_fraction_le`;
- `missingTarget_fraction_le`;
- `ApproximateCVPPreimageCertificate`;
- `approximateCVP_output_valid` and `approximateCVP_output_norm_le`;
- `fixedGadgetCombination`;
- `modulusDown_identity`;
- `coefficientQuotientRemainder_uniform_evalDist`;
- `coefficientQuotient_uniform_evalDist`;
- `rqPairQuotient_uniform_evalDist`;
- `ModularFlooding.tvDist_centered_shifted_eq_absRatio`;
- `ModularFlooding.conditioned_modularCenteredFlooding_joint_le`;
- `ModularFlooding.correctedZeroBranchFlooding_le`;
- `largeModulus_circular_tvDist_le`.
