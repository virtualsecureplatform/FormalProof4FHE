# TFHE subset-key proof: resolved layer and remaining research questions

## Scope

This note records the status of the delayed-projection subset-key route after the
canonical-ternary second-moment calculation. The route targets ordinary LWE-style assumptions
and does not assume NTRU.

Let

\[
  A\leftarrow (\mathbb Z/Q\mathbb Z)^{m\times d}
\]

be a uniform public source-mask matrix. For each prescribed target row \(t\), the simulator seeks
a short public row \(\ell\) such that

\[
  \ell^{\mathsf T}A=t\pmod Q.
\]

If the source error has covariance \(\sigma_E^2 I\) and delayed projection divides by the word
scale \(S\), the derived continuous covariance is

\[
  \frac{\sigma_E^2}{S^2}LL^{\mathsf T}.
\]

Solvability, efficient search, joint Gram control, and the exact finite error law are separate
questions. The first and third are now resolved information-theoretically. Efficient search is
the main cryptographic obstacle.

## Resolved technical results

### Canonical ternary second moment

Use the nonzero ternary rows whose first nonzero coefficient is \(+1\). For the full support
budget their cardinality and ordered same-support pair count are

\[
  N_m=\frac{3^m-1}{2},\qquad
  H_m=\frac{5^m-2\cdot 3^m+1}{4}.
\]

For one fixed target in \((\mathbb Z_{2^k})^d\), distinct canonical rows have the following exact
pair behavior.

- Different supports expose an odd two-by-two minor, so the pair map is surjective and the joint
  hit mass is \(Q^{-2d}\).
- Equal supports have identical parity, while a common positive pivot and a sign-change pivot
  expose a minor \(\pm2\). Their image is the equal-parity subgroup of index \(2^d\), so the joint
  hit mass is \(2^dQ^{-2d}\).

The resulting zero-preimage probability is

\[
  \delta_{m,d,Q}
  =\frac{Q^d-1}{N_m}
   +(2^d-1)\frac{H_m}{N_m^2}.
\]

This is a high-probability existence theorem, not a first-moment heuristic. For a prescribed
family of \(p\) targets, a union bound gives failure at most \(p\delta_{m,d,Q}\).

The Lean development proves the generic clustered first- and second-moment identities, the
zero-hit bound, the odd-minor surjectivity theorem, the equal-support parity and \(\pm2\)-minor
classification, and the deterministic SIS implication. The exact parameter script evaluates the
closed forms with integer and rational arithmetic.

### Disjoint-block joint Gram bound

Assign one independent source-row block to each target and extend each selected preimage by zero
outside its block. Then the rows are orthogonal and

\[
  LL^{\mathsf T}
  =\operatorname{diag}(\|\ell_1\|_2^2,\ldots,\|\ell_p\|_2^2)
  \preceq mI.
\]

This is proved as an exact matrix identity and a positive-semidefinite bound. It resolves the
simultaneous covariance question information-theoretically, at the cost of \(p\) times as many
source rows.

### Current TFHEpp parameter screen

For the source-bound parameter set, exact evaluation of the target-family union bound gives the
following least full-support block sizes for a 128-bit failure target.

| target interpretation | one-target rows | all-target rows | disjoint total source rows |
|---|---:|---:|---:|
| suffix-only | 8,037 | 8,044 | 44,370,704 |
| full secret | 20,756 | 20,764 | 114,534,224 |

The all-target values include the complete target-family multiplicity. Both row energies are far
below the exact integral radius-squared budget \(3104^2\). Thus the current noise radius does not
rule out the canonical ternary existence theorem. The construction is enormous and
noncomputable/exhaustive; these figures are not performance claims.

The earlier counts based only on \(3^m-1\) were not target-family failure bounds: they counted
both signs and did not charge the number of targets. They remain valid raw cardinality facts but
are not the security criterion used here.

### Conditional joint game and finite-noise layers

The whole-view BRK/KSK game theorem is already available. Given a public branch constructor, its
target advantage is bounded by twice the source-game advantage plus one global factorization
failure, one complete joint derived-error distance, and one uniform-branch defect. It retains the
full solver state and does not replace rows independently.

The rounded finite-error layer is also explicit. Conditional on retained solver state \(C=c\),
the complete output mass is the exact finite convolution of the transformed source error,
rounding map, and correction sampler. Equality of that table with the prescribed independent
target-error table is equivalent to exact equality of the full joint laws; a total-variation
version transports any nonzero defect through gadget assembly.

The direct suffix-secret orientation supplies the standard-assumption endpoint once the solver
and finite-noise obligations are met. A separate quadratic-KDM or NTRU assumption is not forced by
this proof orientation.

## Main remaining research question: efficient public search

The existence proof does not provide a polynomial-time algorithm. For a uniform public matrix,
finding the promised row is an inhomogeneous SIS or random modular subset-sum problem.

The geometric gadget makes the barrier precise. If a solver simultaneously returns ternary
preimages \(\ell_0,\ell_1\) for two targets satisfying

\[
  t_1=B t_0\pmod Q,
\]

then

\[
  h=B\ell_0-\ell_1
\]

is a nonzero homogeneous SIS relation. Ternarity proves nonzeroness, and a radius-\(R\) solver
gives \(\|h\|_2\le (B+1)R\). Therefore a generic efficient solver for the standard uniform
matrix is at least as hard as the induced SIS instance. Increasing the row count proves
existence but does not remove this search barrier.

There are three honest ways forward.

1. Show that the induced very-wide SIS instance is actually easy and give a polynomial-time
   algorithm with the required joint norm guarantee.
2. Replace the uniform source matrix through a standard LWE gadget-trapdoor or dual-mode
   construction, prove the matrix-distribution replacement, and sample the complete preimage
   matrix with a compatible Gram bound.
3. Change the implementation or correctness budget enough to use an existing constructive
   factorization. This is a parameter/design change, not a proof-only improvement.

The first two are genuine research problems. Favorable entropy alone is not an algorithm.

## Remaining implementation-analysis question: exact sampler comparison

Even with a solver, the proof needs a concrete bound between the full rounded corrected-error
law and the implementation sampler. The generic finite table and data-processing theorems are
done; the remaining work is to model the actual C++ sampler and evaluate or bound its complete
joint distance. A continuous covariance equality does not by itself prove equality of the finite,
wrapped, rounded distribution.

The comparison must include:

- all output coordinates jointly;
- rounding and modular wraparound;
- solver-dependent retained state;
- the exact correction sampler, if one is used; and
- the real PRNG-to-integer sampling procedure or an explicitly charged replacement theorem.

## Mechanization follow-up, not a new cryptographic assumption

The current Lean module isolates the exact singleton and pair masses as hypotheses of the generic
clustered-moment theorem and proves the algebra that supplies the two pair classes. A final library
step can package the equal-parity image cardinality and the closed-form candidate counts into one
fully instantiated probability theorem. This does not require a new mathematical idea and does
not affect the parameter result, which is evaluated exactly by the source-bound script.

Separately, a future executable reduction should connect the selected solver to an explicit PPT
model. Classical finite choice is suitable for the information-theoretic theorem but cannot be
silently treated as a polynomial-time simulator.

## Recommended order

1. Evaluate the induced SIS regime and attempt a concrete wide-instance solver. Stop this route
   if no polynomial-time algorithm with a joint norm guarantee is credible.
2. In parallel, assess a standard LWE trapdoor/dual-mode matrix replacement; charge its complete
   distribution loss and test the sampled Gram matrix against the same covariance budget.
3. For whichever solver survives, implement the exact finite C++ sampler comparison.
4. Instantiate the already-proved whole-view game theorem and suffix-LWE endpoint.

The decisive issue is now computational search, not information-theoretic existence, joint Gram
control, or an unavoidable quadratic-KDM/NTRU assumption.
