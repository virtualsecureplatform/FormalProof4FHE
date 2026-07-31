# TFHE subset-key proof: resolved layer and remaining research questions

## Scope

This note records the status of the delayed-projection subset-key route after the
canonical-ternary second-moment calculation. The original uniform-matrix branch targets ordinary
LWE-style assumptions and does not assume NTRU. A separate conditional NTRU lossy dual-mode
branch is now mechanized through its generic composition layer below.

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

### Source-aligned factor propagation: technical layer resolved

The alternative random-gadget route now has an operation-level factor calculus. A finite public
external product carries exactly the digit-weighted sum of its row factors, and CMUX adds this sum
to the accumulator factor. The recurrence remains exact when every digit vector is recomputed
from the current public ciphertext. The executable native blind-rotation step is equal as a
complete ciphertext to the same identity-plus-external-product normal form, and this equality is
proved for the entire native control trace. Public signed-monomial rotations are exact factor
scalings.

Coefficient sample extraction is also reduced to one precise compatibility equation: the scalar
gadget applied to the coefficient-extracted factor must equal coefficient extraction of the ring
gadget applied to the original factor. Under this equation the complete split-key phase is
preserved exactly. The exact CMUX energy identity retains its factor cross-correlation term. A
separate Cauchy--Schwarz theorem bounds external-product factor energy, and iteration gives a
conservative deterministic trace recurrence even for data-dependent digits.

Two concrete obligations remain before this route can judge the parameter set:

1. align every native BRK/TGSW control row with one common random ring gadget, construct the
   induced extraction-compatible scalar gadget, and connect it to the KSK layout; and
2. specialize the exact trace recurrence to the native decomposition rows and decide whether the
   resulting factor/noise tail fits the correctness margin.

The propagated factors are ghost proof state and need not be stored by the evaluator. Failure of
the deterministic trace bound would not by itself be a no-go theorem: it would identify the point
where a correlation-aware second-moment or concentration argument is required.

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

## Conditional NTRU lossy dual-mode branch

The reusable technical composition layer for an NTRU route is complete. The rank-one HNF
experiment

\[
  b_0=X-S,\qquad d_j=a_jX+E_j
\]

is packaged as exact recovery of the uniform auxiliary secret \(X\). Its success probability is
proved exactly equal to the pre-existing rank-one HNF search game, including arbitrary leakage
correlated with \(S\) and all \(E_j\).

The posterior statement is also exact. After revealing the structured descriptor in the
information-theoretic branch, arbitrary randomized estimators translate in both directions
between recovery of \(X\) from the HNF view and recovery of \(S\) from the complete entropic
channel. Hence their optimal guessing probabilities are equal. Public coefficient computations,
on the other hand, see only the coefficient marginal: replacing the hidden descriptor while
preserving that marginal leaves every such output law unchanged. Coordinatewise multiplication
by the hidden denominator is proved bijective and gives the exact DSPR channel
\(f_j(a_jS+E_j)=h_jS+f_jE_j\), with an analogous masked-ratio identity.

The decision-to-search interface is genuinely heterogeneous: the complete TFHE decision view
and the HNF search view may have different challenge and auxiliary-input types. A certificate
contains a generated HNF solver, a nonnegative reduction loss, and the checked inequality

\[
  \operatorname{Adv}_{\mathrm{decision}}(D)
  \le
  \Pr[\widehat X=X]+\operatorname{loss}(D).
\]

Combining this certificate with HNF hardness gives

\[
  \operatorname{Adv}_{\mathrm{decision}}(D)
  \le \varepsilon_{\mathrm{HNF}}+\operatorname{loss}(D).
\]

The real-versus-zero theorem then passes through the common uniform endpoint and retains the
second endpoint honestly:

\[
  \operatorname{Adv}_{\mathrm{real},\mathrm{zero}}(D)
  \le
  \varepsilon_{\mathrm{HNF}}+
  \operatorname{loss}(D)+
  \varepsilon_{\mathrm{zero},\mathrm{uniform}}.
\]

Two direct corollaries instantiate \(\varepsilon_{\mathrm{HNF}}\) with the existing joint-ratio
NTRU theorem or with its masked DSPR/NTRU-plus-Hermite variant. Their lossiness bounds are proved
finite before conversion from extended nonnegative reals to real-valued advantage.

This avoids the circular argument of revealing an NTRU trapdoor and then invoking ordinary LWE
conditioned on that trapdoor. The NTRU ratio descriptor stays hidden inside the lossy-mode
hardness statement. It is not public auxiliary input and is not supplied to an LWE adversary.
Nothing in this proof changes TFHEpp's algorithms or distributions.

The remaining NTRU work is research-level rather than interface plumbing:

1. Construct the concrete reduction from the complete joint BRK/KSK public decision view to the
   HNF recovery experiment, preserving all correlations and bounding its loss.
2. Match the full implementation secret and error/leakage sampler to one HNF source state. A
   suffix-only abstraction is insufficient unless the omitted prefix-dependent objects are
   simulated inside the same reduction.
3. Prove the Gaussian/smoothing lossiness certificate for that source and the selected
   parameters.
4. State and justify the precise joint NTRU/DSPR coefficient pseudorandomness assumption and
   discharge the zero-message-versus-uniform endpoint.

For an affine KSK compiler, the first item has a sharp necessary condition. Exact noiseless
correctness for every source secret is equivalent to equality of the affine offsets together with
the public factorization equation \(L\circ A=G\). Thus the compiler necessarily contains the
batch-preimage solver already isolated by the ordinary route. The hidden NTRU descriptor cannot
perform this public work because the coefficient distinguisher receives only the public
coefficient tuple. Avoiding that equation requires a genuinely nonlinear compiler, a redesigned
source distribution, or a stronger assumption that explicitly provides a simulation trapdoor.

Until these four items are supplied, the theorem is a sound conditional endpoint but not a
security judgment for the current TFHEpp parameter set.

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

For the source-aligned branch, first construct the concrete common-gadget control-row alignment
and extraction-compatible scalar gadget, then specialize the now-proved factor-energy recurrence
to the native trace. This is the most direct
technical test because it avoids the public-SIS solver entirely. For the NTRU branch, first
construct the complete-view TFHE-to-HNF reduction, then identify the
exact source sampler, prove its analytic lossiness certificate, and finally close the NTRU/DSPR
and zero-message endpoints. For the ordinary-LWE branch, the previous order remains appropriate:
evaluate the induced SIS regime, assess a standard gadget-trapdoor matrix replacement, and only
then invest in the exact finite C++ sampler comparison.

The ordinary branch is blocked by computational public search. The NTRU branch bypasses that
particular public-SIS solver requirement, but replaces it with the concrete full-view dual-mode
reduction and named NTRU/lossiness premises above.
