# Native TRGSW hard-theorem composition

The mathematical note separates game composition from the existence of a new complete-view
cryptographic simulator. The former is now formalized in
`FormalProof4FHE.TFHE.NativeTRGSWHardTheoremComposition`; the latter remains an explicit
research boundary.

## Reused aggregate algebra

The imported aggregate modules already establish:

* the canonical signed high-pass table and its Jordan decomposition;
* normalized positive and negative mask laws;
* Walsh transform zero through the cutoff and one above it;
* the exact aggregate identity

  \[
    \mathsf{SignedTail}_d
    =
    \lambda_d(a_+-a_-);
  \]

* the normalization estimate

  \[
    2\lambda_d
    \le
    1+\sqrt{N_{\le d}};
  \]

* exact support-sensitive low-frequency accounting; and
* deterministic and stochastic lower bounds for natural projected-translation leakage.

The new module does not duplicate these results.

## Hard Theorem A: conditional one-shot reduction

Let \(a_+,a_-\) be the ideal aggregate acceptances. Let \(r_+,r_-\) be the acceptances after the
two public constructors are applied to a real joint source, and let \(u_+,u_-\) be their uniform
source acceptances. Assume

\[
\begin{aligned}
  |r_+-a_+|&\le\rho_+,\\
  |r_--a_-|&\le\rho_-,\\
  |(r_+-r_-)-(u_+-u_-)|&\le2\varepsilon_{\mathrm{src}},\\
  |u_+-u_-|&\le\rho_{\mathrm U}.
\end{aligned}
\]

The theorem
`idealGap_le_two_mul_source_add_compilerDefects` proves

\[
  |a_+-a_-|
  \le
  2\varepsilon_{\mathrm{src}}+\rho_++\rho_-+\rho_{\mathrm U}.
\]

Combining this with the exact aggregate identity gives

\[
  |\mathsf{SignedTail}_d|
  \le
  2\lambda_d\varepsilon_{\mathrm{src}}
  +
  \lambda_d(\rho_++\rho_-+\rho_{\mathrm U}).
\]

The theorem
`abs_signedHighDegreeSum_le_polynomialNormalization` then substitutes the exact
normalization estimate:

\[
  |\mathsf{SignedTail}_d|
  \le
  (1+\sqrt{N_{\le d}})\varepsilon_{\mathrm{src}}
  +
  \lambda_d(\rho_++\rho_-+\rho_{\mathrm U}).
\]

This is one source reduction, not a sum over high-frequency supports.

## Hard Theorem B: constrained-batch implication

The theorem `constrainedBatchCompiler_advantage_le` proves the advertised implication from
the compiler premises:

\[
\begin{aligned}
  \operatorname{Adv}_{\mathrm{joint}}
  \le{}&
  2\operatorname{Adv}_{\mathrm{source}}
  +2\varepsilon_{\mathrm{fac}}
  +2\varepsilon_{\mathrm{noise}}\\
  &+\varepsilon_{\mathrm U}
  +\varepsilon_{\mathrm{aux},1}
  +\varepsilon_{\mathrm{aux},0}.
\end{aligned}
\]

Each real-branch defect is charged once per branch. A defect already included in a joint
statistical comparison must not be supplied again as an auxiliary defect.

This implication does not construct the factorization. The module separately formalizes the SIS
obstruction. If ternary vectors \(\ell_0,\ell_1\) satisfy

\[
  f(\ell_0)=g,
  \qquad
  f(\ell_1)=B g,
  \qquad
  B\ge2,
\]

and \(\ell_0\ne0\), then

\[
  h=B\ell_0-\ell_1
\]

is nonzero, lies in the kernel of \(f\), and satisfies the coefficient bound

\[
  |h_i|\le B+1.
\]

This is `scaledTernaryPreimages_yield_shortKernel`. Thus a generic efficient short
factorization procedure for a uniform public map contains a corresponding SIS solver.

## Approximate prefix recovery

The note's large-good-set concentration statement is also explicit. For any nonnegative finite
joint mass table with a uniform prefix marginal and deterministic decoder \(\widehat P\), let

\[
  s=\Pr[\widehat P(L)=P].
\]

Then

\[
  |\mathcal P|s^2
  \le
  \left(\sum_\ell\sqrt{\Pr[L=\ell]}\right)^2.
\]

Consequently, decoder failure at most \(\beta\) gives

\[
  C_{1/2}(L)\ge|\mathcal P|(1-\beta)^2.
\]

These are
`card_mul_decoderSuccessMass_sq_le_halfRenyiJointMass_of_uniformPrefix` and
`card_mul_one_sub_failure_sq_le_halfRenyiJointMass_of_uniformPrefix`. For a uniform
binary prefix, \(|\mathcal P|=2^t\).

## Hard Theorem C: hidden-mode composition

For acceptance probabilities along the chain

\[
  \mathsf{View}_1
  \to C_1^0
  \to C_1^1
  \to C_0^1
  \to C_0^0
  \to \mathsf{View}_0,
\]

`hiddenModeComposition_advantage_le` proves

\[
\begin{aligned}
  \operatorname{Adv}_{\mathrm{joint}}
  \le{}&
  \varepsilon_{\mathrm{cmp},1}
  +\varepsilon_{\mathrm{mode},1}
  +\varepsilon_{\mathrm{loss}}\\
  &+\varepsilon_{\mathrm{mode},0}
  +\varepsilon_{\mathrm{cmp},0}
  +\varepsilon_{\mathrm{samp}}.
\end{aligned}
\]

The sampler term is the total finite-sampler comparison cost used in the central lossiness hop.
The theorem contains no trapdoor witness. If a public compiler itself needs the witness, its
public-mode indistinguishability must be established separately.

## Combined support-sensitive theorem

`jointSecurity_le_supportSum_add_completeViewCompiler` composes Hard Theorem A with the
existing low-degree affine-source certificate and the independent-message endpoint:

\[
\begin{aligned}
  \operatorname{Adv}_{\mathrm{joint}}
  \le{}&
  \sum_{j=1}^{d}
    \binom tj
    \sqrt{2^{j+1}\delta}\\
  &+
  2\lambda_d\varepsilon_{\mathrm{src}}
  +\lambda_d(\rho_++\rho_-+\rho_{\mathrm U})
  +\varepsilon_{\mathrm{endpoint}}.
\end{aligned}
\]

The companion polynomial-source-loss theorem replaces \(2\lambda_d\) by
\(1+\sqrt{N_{\le d}}\). No worst-case cutoff bound is reintroduced.

## Exact remaining boundary

The following implications are complete:

1. aggregate compiler premises imply the one-shot tail bound;
2. constrained-batch compiler premises imply the joint BRK/KSK bound;
3. scaled ternary preimages imply a short nonzero kernel witness;
4. hidden-mode premises imply the full hybrid bound; and
5. the one-shot bound composes with support-sensitive leakage removal and the endpoint.

The following objects are not constructed:

1. a public complete-view aggregate compiler whose real branches approximate the two Jordan games
   and whose uniform branches agree;
2. a short factorization for the actual public source matrix whose complete transformed error law
   matches the required KSK law; and
3. an ordinary/lossy dual-mode generator with a witness-independent public compiler and
   conditional lossiness for the complete retained view and actual finite sampler.

These are existential cryptographic construction problems. Treating them as hypotheses is
mathematically honest, but does not certify the current native TFHE parameter by itself.
