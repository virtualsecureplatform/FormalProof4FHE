# Remaining research questions for the TFHE subset-key proof

## Scope

This note separates the algebraic and parameter checks that can be completed mechanically from
the cryptographic questions that still require a new theorem or construction.  The intended
route uses standard LWE-style assumptions and does **not** assume NTRU.

Let

\[
  A\leftarrow (\mathbb Z/Q\mathbb Z)^{m\times d}
\]

be the public mask matrix of a batch of source LWE samples.  Delayed projection seeks, for every
prescribed gadget row \(g\), a public coefficient row \(\ell\) such that

\[
  \ell^{\mathsf T}A = Sg \pmod Q,
  \qquad S=Q/q.
\]

If the source error has covariance \(\sigma_E^2 I\), then division by \(S\) makes the derived
continuous covariance

\[
  \frac{\sigma_E^2}{S^2}\,LL^{\mathsf T}.
\]

Thus exact modular solvability is only half of the problem: all rows must also be short and their
joint Gram matrix must fit below the target covariance.

## Mechanically resolved boundary

The following points no longer require a research conjecture.

1. A solver obtained by first solving over the target ring and then multiplying every
   coefficient by \(S\) cannot meet the current noise budget.  After projection, every nonzero
   integral target-ring row retains at least the complete source-error variance, which is already
   larger than the target-error variance.  This rejects that solver, not delayed projection in
   general.

2. For a genuinely short high-modulus solution, the exact current covariance inequality has
   maximal integral Euclidean radius \(3104\); radius \(3105\) fails.  This is an exact rowwise
   budget, not an existence claim and not a simultaneous matrix-covariance bound.

3. The actual subset-KSK body has a full-secret linear representation.  If the source secret is
   split as \(y=(x,z)\), a native KSK row with prefix mask \(a\), gadget coefficient \(g\), and
   suffix coordinate \(i\) is

   \[
     \langle a,x\rangle + gz_i + e
     = \langle (a,g e_i),(x,z)\rangle+e.
   \]

   Consequently the future source reduction may retain the complete secret rather than forcing a
   suffix-only LWE interpretation.

4. A necessary candidate-capacity screen is favorable.  Restricting coefficients to
   \(\{-1,0,1\}\), the first row counts providing 128 bits of cardinality slack are 8036 for the
   suffix-only target space and 20756 for the full-secret target space.  Their worst-case squared
   row norms are the same numbers, both below \(3104^2\).  The corresponding no-slack thresholds
   are 7955 and 20675.  These counts refer to source samples available to a reduction, not to the
   number of ciphertext rows stored in the implementation.

The fourth point is deliberately only a first-moment feasibility check.  It says that the noise
ball contains enough formal candidates to cover the target space by cardinality.  It proves
neither that a random matrix has a preimage nor that one can find a preimage efficiently.

## Research question 1: high-probability short-preimage existence

For a finite prescribed target set \(T\subseteq(\mathbb Z/Q\mathbb Z)^d\), prove a theorem of the
following form:

\[
 \Pr_A\!\left[
   \forall t\in T,\ \exists \ell_t\in\{-1,0,1\}^m\setminus\{0\},\
   \ell_t^{\mathsf T}A=t
 \right]
 \ge 1-\varepsilon.
\]

A stronger and ultimately useful version should also control the matrix
\(L=(\ell_t^{\mathsf T})_{t\in T}\):

\[
  \frac{\sigma_E^2}{S^2}LL^{\mathsf T}
  \preceq \Sigma_{\mathrm{target}}.
\]

The first moment is immediate because every nonzero ternary row contains a unit coefficient and
therefore maps a uniform \(A\) to a uniform target.  It is not enough for high-probability
existence.  Pairwise dependencies are substantial: signs collapse modulo two, and pairs of
candidate rows have different Smith invariants over a power-of-two ring.  A satisfactory proof
probably needs a second-moment, higher-moment, or leftover-hash argument that is aware of these
support and Smith-type clusters.  It must then be strengthened from one target to the complete
correlated gadget family.

This is an information-theoretic question; no efficient algorithm is required yet.

## Research question 2: efficient public short-preimage generation

Construct a probabilistic polynomial-time public algorithm

\[
  \mathsf{Solve}(A,T;\rho)=L
\]

which, except with probability \(\varepsilon\), simultaneously satisfies

\[
  LA=T\pmod Q
  \quad\text{and}\quad
  \frac{\sigma_E^2}{S^2}LL^{\mathsf T}
  \preceq \Sigma_{\mathrm{target}}.
\]

For a completely uniform matrix with no auxiliary information, this is an inhomogeneous SIS or
random modular subset-sum search problem.  The favorable cardinality calculation does not make
that search polynomial time.  Meet-in-the-middle or exhaustive enumeration would establish only
an exponential-time simulator and therefore cannot support the desired reduction.

There are two credible resolution forms:

- a new polynomial-time algorithm exploiting the very wide, power-of-two instance while proving
  the required joint norm bound; or
- a dual-mode public-matrix generator with a trapdoor, statistically or computationally close to
  the uniform LWE mask distribution, together with a short preimage sampler.

The second option need not use NTRU.  A standard LWE gadget-trapdoor construction is conceptually
eligible, but it must be checked at the exact dimensions and, more importantly, must output a
whole matrix whose Gram bound fits the narrow target noise.  The reduction must charge the matrix
distribution replacement explicitly and may not assume a trapdoor for the original uniform
matrix.

## Research question 3: full-secret joint BRK/KSK reduction

The row identity above should be lifted to a complete game theorem.  The desired statement is
roughly:

> Given a source LWE challenge under the complete secret \(y=(x,z)\), a successful public
> factorization of every required BRK and KSK target row, and a joint derived-error comparison,
> the adversary's view of the complete cloud key is close to its real view with one
> factorization-failure charge and one joint noise charge.

This theorem must preserve all correlations:

- the BRK and KSK rows use the same two secret components;
- many gadget rows reuse the same public source matrix or trapdoor;
- the subset KSK target includes both a random prefix mask and a selected suffix coordinate; and
- the complete circular-security hybrid must replace the two cloud-key families consistently.

Proving rows independently and applying a large union bound is not automatically sound for the
noise law, and it may discard useful shared structure.  The target theorem should therefore be
stated for the whole retained solver state and the whole error vector.

## Research question 4: a joint rounded-noise comparison

Even a spectrally short \(L\) produces correlated errors.  The implementation target, however,
uses separately sampled rounded torus errors.  One needs either an exact equality or a quantified
distance

\[
  \Delta\!\left(
    \operatorname{Round}(LE/S)+F,
    E_{\mathrm{target}}
  \right)
  \le \eta
\]

for the complete vector, conditional on all retained public solver data.  The proof must account
for rounding, wraparound, off-diagonal covariance, and any correction sampler.  A continuous
Gaussian covariance calculation alone does not identify this finite distribution.

There are two clean specifications:

- replace the implementation sampler by a fully specified finite distribution for which the
  convolution can be proved; or
- formalize the exact PRNG-to-output algorithm and bound its finite table against the analytic
  reference law.

The finite convolution and data-processing infrastructure is already routine.  Deriving a tight,
implementation-valid comparison bound is the remaining analytic part.

## Research question 5: standard-assumption correlated-key KDM closure

After the joint simulator is constructed, the final theorem still has to relate its source game
to a standard assumption without introducing NTRU.  The needed source statement exposes several
affine functions of the complete secret together with the BRK/KSK cross-key structure.  Ordinary
SubspaceLWE directly handles public affine projections of one hidden secret, but it does not by
itself turn products of independently sampled secret components into affine queries.

A successful endpoint could be one of the following:

1. a correlated-key quadratic-KDM theorem derived from standard LWE or module-LWE;
2. a sequence of hybrids that makes every exposed function affine before invoking SubspaceLWE;
3. a dual-mode/trapdoor theorem whose simulated branch removes the secret-secret products and
   whose public matrices remain indistinguishable from the standard source distribution.

The theorem must state its joint-leakage loss for the complete cloud key.  Replacing each row with
an independent KDM invocation and summing losses is likely too expensive and may misrepresent the
shared-key game.

## What no longer appears promising

The following modifications do not resolve the current gap on their own.

- More precise analysis of the lifted invertible-minor solver: its minimum nonzero variance
  already exceeds the entire target budget.
- Merely increasing the number of source rows: it improves algebraic rank and candidate capacity
  but does not yield an efficient short-preimage algorithm or a joint spectral bound.
- Noise flooding at the target: it can make covariance completion possible only by changing the
  implementation parameters and correctness analysis.
- SubspaceLWE alone: it covers affine leakage, not the unresolved cross-secret products.
- An NTRU-style assumption: it may supply a short relation, but it is intentionally outside the
  present target assumption set.

## Recommended order

1. Prove or refute the high-probability short-preimage existence statement for one target and then
   for the complete target family.
2. If existence is favorable, test an LWE gadget-trapdoor generator and preimage sampler against
   the exact Gram-matrix noise budget.
3. State and prove the full-secret joint BRK/KSK game reduction around that solver interface.
4. Complete the rounded finite-noise comparison for the chosen sampler.
5. Close the correlated-key KDM endpoint under the selected standard LWE-style assumption.

The first two steps are the decisive ones.  If no efficient, jointly short preimage mechanism
fits the covariance budget, further refinements of the final hybrid cannot make the current
parameter provable by this route.
