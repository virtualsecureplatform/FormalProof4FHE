# The source-aligned BRK/KSK joint-law problem

## Current status

The modified source-aligned cloud-key route described below now has a formal complete-view
reduction theorem. Under explicit public constructors for one batched suffix-RLWE source and two
batched prefix-LWE sources, plus the complete-vector error-replacement distance, its loss is

\[
  2\epsilon_Z+4\epsilon_P+2\epsilon_{\mathrm{sm}}+\epsilon_{\mathrm{aux}}.
\]

An exact correlated-error target removes the smudging term. This is a conditional reduction: a
concrete scheme must still instantiate the constructors and prove the finite error-law premise.
It is not a proof that the independently sampled native TFHE KSK has the widened fresh aligned
law.

The native-preserving part remains open quantitatively, but its obstruction is now exact. For a
deterministic compiler `U ↦ UD`, the compiled mask is uniform on the public row image and

\[
  \Delta(U_ND,U_B)
  =1-\left(\frac{|\operatorname{im}(u\mapsto uD)|}{q^M}\right)^n.
\]

When the native width is smaller, this gives the stated
`1 - q^{-n(M-K)}` lower bound, so exact factorization `HD = G` cannot justify a fresh-law
replacement. What remains viable is the evaluator-level route: the noiseless discrepancy is a
kernel vector and the error discrepancy is its inner product with native KSK error. The finite
MGF-to-subgaussian tail and reachable-factor union bound are formalized; supplying concrete
reachable-factor covariance and correctness bounds remains implementation-specific work.

One correction to the notation below is important. The concrete TFHE formalization does not use
one self-dual coefficient map: reciprocal coefficients scalarize masks and factors, while
ordinary coefficients scalarize secrets and bodies. The adjoint identity is proved with those two
compatible conventions.

## Purpose

This note isolates the remaining research problem in the source-aligned approach to TFHE
circular security. All dimensions and parameters below are symbolic. The issue is not a
particular parameter value, nor is it the finite algebra of blind rotation or sample extraction.
It is the security of the complete, correlated bootstrapping-key and key-switching-key view.

The technical construction already gives three facts:

1. all bootstrapping-key row masks can be collected as the columns of one ring matrix;
2. coefficient extraction canonically turns that ring matrix into a compatible scalar matrix;
   and
3. factors attached to different controls occupy disjoint blocks, so their squared energies add
   exactly.

Moreover, the complete tensor of bootstrapping-key masks is jointly uniform as a ring matrix for
fixed secrets and messages. Its induced scalar matrix is consequently uniform over the
corresponding structured block-negacyclic family, not over all scalar matrices of the same
dimensions. The unresolved problem begins after these facts: the key-switching key required by
the source-aligned analysis is wider than the native key-switching key and depends on those
bootstrapping-key masks.

## 1. Algebraic setup

Let

\[
  R_q=\mathbb Z_q[X]/(X^N+1)
\]

be the ring used for the ring ciphertexts. Let

- \(p\in\mathbb Z_q^n\) be the scalar secret;
- \(z\in R_q^r\) be the ring secret; and
- \(J\) be the finite set of all bootstrapping-key rows, including every control, component,
  and gadget level.

Write a bootstrapping-key row as

\[
  B_j=(a_j,b_j),
  \qquad
  a_j\in R_q^r,
\]

with phase equation

\[
  b_j-\langle z,a_j\rangle=m_j(p)+e_j.
  \tag{1}
\]

Here \(m_j(p)\) is the appropriate gadget multiple of a scalar-secret coordinate and \(e_j\)
is the row error. Collect the masks as columns of

\[
  A_B=(a_j)_{j\in J}:R_q^J\longrightarrow R_q^r.
  \tag{2}
\]

Let

\[
  E_k:R_q^k\overset{\sim}{\longrightarrow}\mathbb Z_q^{kN}
\]

be the coefficient-extraction equivalence, including the reciprocal-coefficient convention used
by sample extraction. Define the induced scalar gadget

\[
  G_B=E_r\circ A_B\circ E_J^{-1}:
  \mathbb Z_q^{|J|N}\longrightarrow\mathbb Z_q^{rN}.
  \tag{3}
\]

Consequently, for every ring factor \(d\in R_q^J\),

\[
  E_r(A_Bd)=G_BE_J(d).
  \tag{4}
\]

Equation (4) is exact. Thus compatibility between blind rotation and sample extraction is no
longer an assumption.

## 2. The source-aligned key-switching key

Put \(s=E_r(z)\in\mathbb Z_q^{rN}\) and \(M=|J|N\). A fresh source-aligned key-switching key for
the induced gadget has the form

\[
  K_{\mathrm{align}}(B;p,z)
  = (U_B,c_B),
  \tag{5}
\]

where

\[
  U_B\leftarrow \mathbb Z_q^{n\times M},
  \qquad
  c_B=U_B^{\mathsf T}p+G_B^{\mathsf T}s+\eta_B.
  \tag{6}
\]

For a factor \(x=E_J(d)\), source-aligned key switching consumes \(x\) directly. Its phase is
the phase before switching minus

\[
  \langle x,\eta_B\rangle.
  \tag{7}
\]

This is the desired behavior: the same factor propagated through blind rotation controls the
key-switching error, without solving a new modular preimage problem at the end.

The important point is that \(G_B\) is a deterministic function of the complete BRK mask tensor.
Therefore (6) is not an ordinary independently parameterized KSK distribution. Its encrypted
message is selected by the BRK itself.

## 3. The native key-switching key

Let

\[
  H:\mathbb Z_q^K\longrightarrow\mathbb Z_q^{rN}
\]

be the ordinary coordinate-by-level key-switch gadget. The native key-switching key has the form

\[
  K_{\mathrm{nat}}(p,z)=(U_N,c_N),
  \tag{8}
\]

where

\[
  U_N\leftarrow\mathbb Z_q^{n\times K},
  \qquad
  c_N=U_N^{\mathsf T}p+H^{\mathsf T}s+\eta_N.
  \tag{9}
\]

Conditional on \((p,z)\), the native KSK masks and errors are sampled independently of the BRK
coins. Native key switching first decomposes its input under \(H\), then combines the rows of
(9). Usually \(K\) is much smaller than \(M\), and the two public key formats are visibly
different.

It is therefore not meaningful to claim raw indistinguishability between
\(K_{\mathrm{nat}}\) and \(K_{\mathrm{align}}\). Their layouts have different lengths. A valid
native-preserving theorem must specify a common public representation, an efficient public
compiler, or an evaluator-level coupling. Otherwise a distinguisher can identify the branch from
the format alone.

## 4. Why uniform BRK masks are insufficient

The complete mask matrix \(A_B\) is jointly uniform over ring matrices when the secrets and
messages are fixed. Its coefficient recoding \(G_B\) is therefore uniform over the image of this
recoding: a structured family of block-negacyclic scalar matrices. It is not uniform over the
space of all \((rN)\)-by-\((|J|N)\) scalar matrices. Even the uniformity that does hold is only a
marginal statement.

The BRK bodies satisfy

\[
  b=A_B^{\mathsf T}z+m(p)+e.
  \tag{10}
\]

Thus the public pair \((A_B,b)\) is an LWE-type joint distribution. In addition, the aligned KSK
bodies contain

\[
  G_B^{\mathsf T}E_r(z).
  \tag{11}
\]

The same ring secret occurs in (10) and (11), while the scalar secret encrypted by the BRK occurs
as the target key in (6). This is the complete circular correlation.

Uniformity of \(A_B\) says neither that \(A_B\) is independent of \(b\) nor that
\(G_B^{\mathsf T}E_r(z)\) is harmless in the presence of \(b\). Even in the noiseless toy example

\[
  A\leftarrow U,
  \qquad
  y=A^{\mathsf T}z,
\]

the marginal of \(A\) is perfectly uniform, while the pair \((A,y)\) exposes an exact relation to
\(z\). Replacing one component because its marginal is uniform would destroy that relation and
would not preserve the joint law.

Likewise, row-by-row security is not enough. An adversary receives all BRK rows, all KSK rows, and
any retained auxiliary material at once, and may test relations across every component.

## 5. A concrete public compiler candidate

Assume first that the ordinary gadget \(H\) gives an exact full-width representation of every
scalar vector. One can then compute a public matrix \(D_B\) satisfying

\[
  H D_B=G_B.
  \tag{12}
\]

For example, the columns of \(D_B\) can be obtained by exact gadget decomposition of the columns
of \(G_B\). Multiplying the native KSK by \(D_B\) gives

\[
\begin{aligned}
  U_D &= U_ND_B,\\
  c_D &= D_B^{\mathsf T}c_N\\
      &= U_D^{\mathsf T}p+G_B^{\mathsf T}s+D_B^{\mathsf T}\eta_N.
\end{aligned}
\tag{13}
\]

Therefore (13) is an exact algebraic source-aligned KSK in the full-width setting. Computing it
is technical, public, and efficient. It can be treated as proof-side derived data, so merely
constructing it does not require changing an implementation.

If the native gadget uses a truncated or approximate decomposition, define the public residual

\[
  R_B=G_B-HD_B.
  \tag{12a}
\]

Then the transformed body is

\[
  c_D=U_D^{\mathsf T}p+G_B^{\mathsf T}s-R_B^{\mathsf T}s
      +D_B^{\mathsf T}\eta_N.
  \tag{13a}
\]

A native bridge must bound the residual term as well. Approximate decomposition therefore adds
an explicit technical defect; it does not remove the joint-law problem described below.

However, (13) does not have the fresh law in (6):

- \(U_ND_B\) need not be uniform over \(\mathbb Z_q^{n\times M}\);
- its support and correlations depend on \(B\) through \(D_B\);
- \(D_B^{\mathsf T}\eta_N\) is generally correlated across columns and need not have the target
  error law; and
- its covariance and tails depend on the complete Gram matrix
  \(D_B^{\mathsf T}\Sigma_ND_B\), not just on individual column norms.

There is also an evaluator-level discrepancy. Native key switching uses

\[
  \operatorname{Dec}_H(G_Bx),
\]

whereas the linearly compiled aligned key uses

\[
  D_Bx.
\]

In the exact full-width setting, both map through \(H\) to \(G_Bx\), but digit decomposition is
not linear in general. Their difference

\[
  \rho_B(x)=\operatorname{Dec}_H(G_Bx)-D_Bx
  \tag{14}
\]

lies in \(\ker H\). Thus the noiseless message cancels, but the two procedures can accumulate
different KSK errors. Controlling \(\langle\rho_B(x),\eta_N\rangle\) for the factors reachable in
a complete blind rotation is an additional quantitative requirement. With approximate
decomposition, \(H\rho_B(x)\) is instead the difference of the two decomposition residuals, which
must also be retained in the bound.

Equation (12) therefore solves the matrix-existence problem, not the joint-security and
correctness problem.

## 6. Native-preserving target theorem

A proof that leaves the native scheme unchanged should establish a theorem of the following
form. First define the complete native endpoints

\[
\begin{aligned}
  \mathsf V_{\mathrm{nat,real}}
    &=\bigl(B_{\mathrm{real}}(p,z),K_{\mathrm{nat}}(p,z),
      \mathsf{Aux}(p,z)\bigr),\\
  \mathsf V_{\mathrm{nat,zero}}
    &=\bigl(B_{\mathrm{zero}}(z),K_{\mathrm{nat,zero}}(p),
      \mathsf{Aux}_0(p,z)\bigr),
\end{aligned}
\tag{15}
\]

where the zero KSK retains its honestly sampled target-key masks and errors but encrypts zero.
Set

\[
  \operatorname{Adv}_{\mathrm{native}}(D)
  =\left|
    \Pr[D(\mathsf V_{\mathrm{nat,real}})=1]
    -\Pr[D(\mathsf V_{\mathrm{nat,zero}})=1]
  \right|.
  \tag{16}
\]

> **Native source-aligned bridge theorem.** There are efficient public algorithms
> \(\mathsf{Compile}\) and \(\mathsf{Relate}\) such that, for the prescribed secret and error
> samplers:
>
> 1. \(\mathsf{Compile}(B,K_{\mathrm{nat}})\) produces an aligned object satisfying the exact
>    gadget and phase equations;
> 2. \(\mathsf{Relate}\) couples the actual native key-switch output to the source-aligned output,
>    with an explicit bound \(\varepsilon_{\mathrm{eval}}\) on the resulting correctness or
>    distributional defect; and
> 3. for every efficient distinguisher \(D\) of the complete native cloud-key experiment, one can
>    construct an efficient adversary \(\mathcal A_D\) for a stated standard assumption such that
>
>    \[
>      \operatorname{Adv}_{\mathrm{native}}(D)
>      \le
>      \operatorname{Adv}_{\mathrm{assumption}}(\mathcal A_D)
>      +\varepsilon_{\mathrm{joint}}
>      +\varepsilon_{\mathrm{eval}}.
>      \tag{17}
>    \]

The experiment in (17) must retain the full BRK, the full native KSK, all auxiliary evaluation
keys, and their genuine shared secrets. The compiler must use public information only. A hidden
trapdoor may support the analysis of one hybrid, but it cannot be silently supplied to an
algorithm operating on the native public view.

For the candidate (13), the genuinely hard part is proving an acceptable
\(\varepsilon_{\mathrm{joint}}\) for the BRK-dependent masks and transformed joint error, together
with an acceptable bound for (14). Exact factorization alone does not imply either bound.

## 7. Modified-scheme target theorem

The alternative is to change cloud-key generation so that it samples (6) directly and publishes
the widened aligned KSK. In that case the central security experiment is same-format and can be
stated more directly. Define

\[
\begin{aligned}
  \mathsf V_{\mathrm{real}}
    &=\bigl(B_{\mathrm{real}}(p,z),
       U_B,
       U_B^{\mathsf T}p+G_{B_{\mathrm{real}}}^{\mathsf T}E_r(z)+\eta_B,
       \mathsf{Aux}(p,z)\bigr),\\
  \mathsf V_{\mathrm{zero}}
    &=\bigl(B_{\mathrm{zero}}(z),
       U_B,
       U_B^{\mathsf T}p+\eta_B,
       \mathsf{Aux}_0(p,z)\bigr).
\end{aligned}
\tag{18}
\]

The zero branch and auxiliary material may instead be connected through a common uniform
endpoint, but every retained correlation must be stated explicitly.

The required theorem is:

> **Aligned joint cloud-key theorem.** Under a precisely named assumption, for every efficient
> distinguisher \(D\),
>
> \[
>   \left|
>     \Pr[D(\mathsf V_{\mathrm{real}})=1]
>     -\Pr[D(\mathsf V_{\mathrm{zero}})=1]
>   \right|
>   \le \varepsilon_{\mathrm{joint}},
>   \tag{19}
> \]
>
> where \(\varepsilon_{\mathrm{joint}}\) is negligible or quantitatively small enough for the
> complete security budget.

Statement (19) is a circular or auxiliary-input KDM statement. Ordinary single-ciphertext
IND-CPA security does not automatically imply it, because the KSK messages depend on the secret
and on a public matrix extracted from another ciphertext family under the opposite key.

This route makes the algebra and factor-noise analysis clean, but it changes the public key
layout and usually the key-switching procedure. It therefore proves security of a modified
scheme unless a separate native-equivalence theorem is supplied.

## 8. Why this is a genuine research problem

The following operations are routine once their inputs and assumptions are fixed:

- building \(G_B\) from \(A_B\);
- checking (4), (12), and (13);
- carrying factors through public linear operations;
- calculating covariance from a fixed transformation matrix; and
- performing the final symbolic or numerical correctness calculation.

The unresolved step is qualitatively different. It must simultaneously provide:

1. **A common public experiment.** Different raw layouts cannot be compared without an encoding,
   compiler, or modified sampler.
2. **A full joint law.** Correct row marginals do not control cross-row or cross-key tests.
3. **Circular-secret consistency.** The same \(p\) and \(z\) must be retained throughout every
   hybrid.
4. **An efficient public reduction.** Nonconstructive preimages or a hidden witness unavailable
   in one branch do not define a reduction.
5. **A quantitative loss.** The proof must not hide a loss proportional to an infeasible number
   of correlated rows.
6. **A joint error bound.** Covariance, tails, rounding, and correlations after transformation
   must fit the correctness budget.

No currently established marginal theorem supplies these six items. Proving them from ordinary
LWE/RLWE, constructing an appropriate dual-mode or trapdoor distribution, or identifying a
minimal additional joint-KDM assumption is the hard mathematical problem.

## 9. Plausible research routes

### Route A: analyze the public compiler directly

Use (12)--(14), retain the native cloud key exactly, and prove that the compiled masks and errors
are secure and sufficiently small conditional on the complete BRK. This route changes no public
sampler, but it must overcome the structured-mask and joint-error problems.

### Route B: a dual-mode or trapdoor gadget

Replace the common gadget by a distribution that is computationally indistinguishable from the
native uniform marginal but has a hidden trapdoor supporting short, distribution-controlled
preimages. The proof must still compile the complete public view without giving the hidden
witness to the public simulator. An NTRU-style construction is one possibility, but the theorem
must state exactly which assumption supplies the joint replacement.

### Route C: prove a direct auxiliary-input KDM theorem

Treat the complete BRK as correlated auxiliary input and prove security of the aligned KSK
messages \(G_B^{\mathsf T}E_r(z)\) under the scalar key. This is the most direct theorem statement,
but it may require a stronger assumption than ordinary LWE/RLWE.

### Route D: modify the cloud-key format

Publish the widened source-aligned KSK directly and prove (19). This removes the native layout
comparison but changes the scheme. Performance is a separate question; even an inefficient
parameter set cannot be certified until the joint theorem is available.

## 10. Updated stopping point

The modified-scheme joint theorem (19) is now available as a conditional complete-view reduction,
including exact correlated-error and complete-vector-smudging variants. The deterministic native
compiler cannot provide the native bridge theorem (17) by fresh-law replacement because of its
exact public support distance. The remaining native route is therefore evaluator-level: install
the concrete finite MGF certificate, bound the residual covariance over reachable factors, and
test the final correctness margin. Establishing that these concrete bounds fit an implementation
parameter set is still outstanding.
