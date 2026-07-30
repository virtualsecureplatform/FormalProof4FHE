# The witness-independent full-view compiler premise

## Purpose

This note isolates the central research premise in the hidden-NTRU route to security of the
joint TFHE bootstrapping-key and key-switching-key view.

The hidden-NTRU argument already explains how a structured public coefficient distribution can
make an HNF recovery experiment lossy while remaining computationally indistinguishable from
uniform coefficients. What is not supplied by that argument is an efficient reduction from the
complete TFHE public experiment to the HNF recovery experiment. Constructing that reduction is
the full-view compiler problem.

The word *compiler* denotes proof machinery. It need not be part of the implemented encryption
scheme. Nevertheless, it must be an efficient public algorithm: nonconstructive existence or
access to a hidden NTRU witness is insufficient.

## 1. The two public TFHE experiments

Write the complete master secret as

\[
  K=(P,Z),
\]

where the split records the portions occurring in the bootstrapping-key and key-switching-key
cycle. The relevant public distributions are

\[
\begin{aligned}
  \mathsf V_{\mathrm{real}}
    &=\bigl(\mathsf{BRK}_{K}(P),\mathsf{KSK}_{P}(Z),\mathsf{Aux}(K)\bigr),\\
  \mathsf V_{\mathrm{zero}}
    &=\bigl(\mathsf{BRK}_{K}(0),\mathsf{KSK}_{P}(Z),\mathsf{Aux}(K)\bigr),\\
  \mathsf V_{\mathrm{unif}}
    &=\bigl(U_{\mathrm{BRK}},\mathsf{KSK}_{P}(Z),\mathsf{Aux}(K)\bigr).
\end{aligned}
\]

The retained KSK and auxiliary objects have their genuine joint correlations in all three
experiments. In particular, the uniform experiment does not resample them under a fresh or
independent secret.

For every public distinguisher \(D\),

\[
  \operatorname{Adv}_{\mathrm{real},\mathrm{zero}}(D)
  \le
  \operatorname{Adv}_{\mathrm{real},\mathrm{unif}}(D)
  +
  \operatorname{Adv}_{\mathrm{zero},\mathrm{unif}}(D).
  \tag{1}
\]

The hidden-NTRU HNF route is intended to bound the first term. The second remains a genuine
zero-message endpoint with the same correlated public material.

## 2. The HNF recovery source

Let \(R\) be a finite commutative ring. A source state consists of

\[
  (S,\mathbf E,\Lambda),
\]

where \(S\in R\) is the entropic source secret, \(\mathbf E=(E_j)_j\) is the complete error
vector, and \(\Lambda\) is arbitrary public leakage correlated with both of them. Independently
sample \(X\leftarrow U(R)\) and a public coefficient tuple \(\mathbf a=(a_j)_j\). The HNF
transcript is

\[
  \mathsf H
  =
  \left(
    \Lambda,
    b_0=X-S,
    \{(a_j,d_j=a_jX+E_j)\}_j
  \right).
  \tag{2}
\]

The search objective is to recover \(X\). Eliminating the public anchor gives

\[
  d_j-a_jb_0=a_jS+E_j.
  \tag{3}
\]

Thus recovery of \(X\) is equivalent to recovery of \(S\) from the entropic channel, once the
independent anchor is accounted for.

## 3. Exact reduction premise

The required statement is the following.

> **Full-view compiler/recovery premise.** For every efficient public distinguisher \(D\) for
> \(\mathsf V_{\mathrm{real}}\) versus \(\mathsf V_{\mathrm{unif}}\), there is an efficient HNF
> recovery algorithm \(\mathcal A_D\), executable from the public transcript \(\mathsf H\) alone,
> such that
>
> \[
>   \operatorname{Adv}_{\mathrm{real},\mathrm{unif}}(D)
>   \le
>   \Pr[\mathcal A_D(\mathsf H)=X]
>   +\varepsilon_{\mathrm{red}}(D).
>   \tag{4}
> \]

The reduction loss \(\varepsilon_{\mathrm{red}}(D)\) must explicitly include every discrepancy
introduced by the construction, such as mode changes, shifted evaluations, candidate testing,
amplification, imperfect simulation, and sampler replacement.

The statement allows the TFHE decision view and HNF search view to have completely different
types. It does not, however, create a compiler automatically. A proof of (4) must give the actual
algorithm \(\mathcal A_D\) and prove the displayed quantitative inequality.

## 4. Meaning of “full view”

The algorithm underlying \(\mathcal A_D\) must give \(D\) a complete, consistently generated
TFHE public view. It must account for all of the following simultaneously:

- every BRK row, decomposition block, and gadget level;
- the complete KSK rather than independently correct row marginals;
- the shared prefix and suffix portions of the master secret;
- every retained auxiliary key or public object;
- correlations among all source errors, derived errors, and correction errors;
- ring changes, modulus switching, rounding, and finite-word effects;
- the real and uniform branches used in the distinguishing experiment; and
- the procedure that turns distinguishing information into a guess for \(X\).

It is not enough for each generated ciphertext to have the correct marginal distribution. An
adversary receives the whole public key cycle and may test correlations across its components.
The compiler therefore needs either exact equality of the complete joint laws or an explicit
total-variation or computational bound for their difference.

There are three basic treatments of retained KSK and auxiliary material:

1. Derive it publicly from the HNF samples.
2. Include it in the correlated leakage \(\Lambda\) and forward it unchanged.
3. Generate it separately and prove that the resulting joint law has the required correlation.

The first treatment creates the short-factorization problem below. The second transfers the
burden to proving HNF lossiness conditioned on the entire retained key material. The third is
valid only with a coupling or replacement theorem; independent resampling is not generally
correct.

## 5. Witness independence

Suppose the structured coefficient generator samples

\[
  (\mathbf a,\tau)\leftarrow\mathsf{NGen},
\]

where \(\mathbf a\) is public and \(\tau\) is a short-ratio or NTRU descriptor. For example,

\[
  a_j=f_j^{-1}h_j,
  \qquad
  \tau=\{(f_j,h_j)\}_j.
  \tag{5}
\]

The public coefficient hybrid gives its distinguisher a tuple \(\mathbf a\) that is either
uniform or sampled from the structured public marginal. It does not give the distinguisher
\(\tau\). Consequently, the executable reduction must have the form

\[
  \mathbf a
  \longmapsto
  \mathsf H
  \longmapsto
  \text{TFHE full-view compiler}
  \longmapsto
  D,
  \tag{6}
\]

with no hidden-witness input on this path.

The descriptor may be revealed in the information-theoretic analysis of the structured branch.
Indeed, it yields the bijective channel transformation

\[
  f_j(a_jS+E_j)=h_jS+f_jE_j,
  \tag{7}
\]

which is useful for proving lossiness. This analytical use does not make \(f_j\) or \(h_j\)
available to the public compiler.

If the compiler depends on \(\tau\), it cannot be evaluated on a uniform coefficient challenge,
so ordinary public-marginal NTRU pseudorandomness no longer proves the coefficient hybrid.
Computational indistinguishability is closed under efficient public postprocessing of
\(\mathbf a\); it is not automatically closed under a transformation that also consumes a
secret witness available in only one branch.

## 6. The affine KSK barrier

The KSK part exposes a necessary algebraic condition. Suppose the public HNF-derived source body
has the form

\[
  Y=AZ+E,
  \tag{8}
\]

where \(A:V_Z\to W\) is public. The required noiseless KSK message is \(G(Z)\), where
\(G:V_Z\to T\) is the gadget map.

Consider a public affine compiler

\[
  \mathsf{Comp}(Y)=C+L(Y),
  \tag{9}
\]

with linear postprocessing \(L:W\to T\). If its target offset is \(C'\), exact noiseless
correctness for every \(Z\) requires

\[
  C+L(AZ)=C'+G(Z).
  \tag{10}
\]

Taking \(Z=0\) gives \(C=C'\). Removing the common offset then gives

\[
  \boxed{L\circ A=G.}
  \tag{11}
\]

In matrix notation, every target gadget row \(g_i\) therefore needs a public preimage
\(\ell_i\) satisfying

\[
  \ell_i^{\mathsf T}A=g_i^{\mathsf T}.
  \tag{12}
\]

Correct algebra is only the first requirement. The output error contains

\[
  L(E),
  \tag{13}
\]

so \(L\) must also be short or have a compatible joint Gram matrix. For source covariance
\(\Sigma_E\), the continuous derived covariance is

\[
  L\Sigma_E L^{\mathsf T},
  \tag{14}
\]

possibly followed by the scaling and rounding map used by the implementation. A large arbitrary
solution of (11) generally destroys the target noise budget.

For a uniform public matrix \(A\), efficiently finding short solutions of (12) is an
inhomogeneous-SIS or random modular subset-sum problem. Counting arguments can prove that short
solutions exist, and disjoint support can provide a favorable joint Gram matrix, but exhaustive
finite search is not an efficient public compiler.

The affine result is a barrier, not an impossibility theorem. It does not rule out an efficient
short-preimage algorithm for the particular parameter family, nor does it cover genuinely
nonlinear compilers. It shows exactly what every affine solution must construct.

## 7. What hidden NTRU does and does not supply

The hidden-NTRU mode can supply two components of the security proof:

1. A computational hybrid from uniform public coefficients to the structured public marginal.
2. An information-theoretic recovery bound in the structured mode, after using the hidden
   descriptor to analyze the complete entropic channel.

It does not by itself supply:

- a public short-preimage matrix \(L\);
- a compiler for the complete BRK/KSK view;
- a proof that transformed errors match the implementation sampler;
- the zero-message-versus-uniform endpoint; or
- permission to give the hidden descriptor to the reduction.

In particular, the fact that \(\tau\) would make equation (12) easy is not enough. Using it in
the simulator requires a different dual-mode theorem whose assumption covers the trapdoor-aided
output distribution.

## 8. Honest ways to discharge the premise

### 8.1 Public short-preimage construction

Give an efficient public algorithm that constructs the complete matrix \(L\), proves
\(L\circ A=G\), controls its joint norm or Gram matrix, and proves that the complete transformed
error law is correct or explicitly close to the target law.

This would close the affine route without exposing an NTRU witness. A favorable count of
candidate preimages is not enough; the algorithm and its running-time bound are essential.

### 8.2 Genuinely nonlinear compiler

Construct a public compiler whose dependence on the source body is nonlinear, so that the affine
factorization theorem does not apply. One must still prove exact message correctness, the full
joint output distribution, efficient evaluation, and a usable noise bound.

Nonlinearity is therefore a possible escape from equation (11), not a security proof by itself.

### 8.3 Trapdoor-augmented dual mode

Use a structured generator that retains a simulation trapdoor and state a stronger assumption or
reduction covering the complete trapdoor-generated simulated view. Schematically, the required
claim must compare a distribution involving

\[
  (A,\mathsf{Sim}(A,\tau))
\]

with the appropriate ordinary public experiment, while \(\tau\) remains hidden from the final
adversary. Pseudorandomness of the marginal \(A\) alone does not imply this joint statement when
\(\mathsf{Sim}\) depends on \(\tau\).

This route can remain proof-only and need not change TFHE behavior, but it is a stronger and more
specific cryptographic premise than an ordinary NTRU-ratio assumption.

### 8.4 Retain the KSK as leakage

Place the genuine KSK and auxiliary material in \(\Lambda\), allowing the reduction to forward
them without reconstruction. The resulting lossiness theorem must then remain true after
conditioning on this complete correlated leakage. If that material nearly determines the source
secret information-theoretically, this orientation cannot provide a useful lossiness bound
without another computational hybrid.

### 8.5 Change the public source distribution or implementation

Use a trapdoor-generated source matrix, a known gadget-trapdoor distribution, or a larger
correctness budget compatible with a constructive factorization. This may make preimage sampling
efficient, but it changes the scheme or its parameter distribution and therefore needs a new
correctness and security analysis.

## 9. Other obligations after constructing the compiler

Even a successful full-view compiler is not by itself a parameter certificate. The following
items must be instantiated for the same parameter family and error law.

### Source-state identification

Specify which object is \(S\), how \((P,Z)\) is encoded, which errors form \(\mathbf E\), and which
retained public objects form \(\Lambda\). Prove equality or explicit closeness between this source
sampler and the complete implementation-level sampler.

### Conditional analytic lossiness

Prove the required smoothing, singular-value, or conditional-guessing estimate for
\((S,\mathbf E,\Lambda)\). Entropy of \(S\) alone is insufficient when the errors or leakage are
correlated with it.

### Joint computational assumption

State the exact structured and reference coefficient distributions, number of samples, allowed
adversary class, and reduction loss. The assumption must cover the complete coefficient tuple
consumed by the induced HNF solver, not only its row marginals.

### Zero-message endpoint

Bound

\[
  \operatorname{Adv}_{\mathrm{zero},\mathrm{unif}}(D)
\]

while retaining the genuine KSK and auxiliary material. Ordinary RLWE without that correlated
auxiliary input cannot silently replace this experiment.

### Exact sampler comparison

If the analytic argument uses an ideal Gaussian or continuous covariance model, compare it with
the actual wrapped, rounded, finite implementation sampler. The comparison must cover the full
joint error vector and its total replacement loss.

## 10. Completion criterion

The full hidden-NTRU proof is complete for a parameter family only when all of the following have
been supplied:

1. An efficient witness-independent construction of \(\mathcal A_D\) for every allowed \(D\).
2. A proof of inequality (4) with an explicit negligible \(\varepsilon_{\mathrm{red}}(D)\).
3. A precise joint NTRU/DSPR coefficient bound for the induced solver.
4. A conditional structured-channel guessing bound for the complete source state.
5. A bound for the correlated zero-message endpoint.
6. A joint comparison with the implementation sampler.
7. A correctness proof for the same parameters and error law.

These yield the final bound

\[
  \operatorname{Adv}_{\mathrm{real},\mathrm{zero}}(D)
  \le
  \varepsilon_{\mathrm{NTRU}}
  +\varepsilon_{\mathrm{loss}}
  +\varepsilon_{\mathrm{red}}(D)
  +\varepsilon_0.
  \tag{15}
\]

Each loss appears once.

## Conclusion

The central research premise is an executable public bridge between two different objects: the
rank-one HNF recovery transcript and the complete correlated TFHE key cycle. Hidden NTRU
structure can justify coefficient pseudorandomness and conditional lossiness, but its witness is
not public simulator input under the ordinary marginal assumption.

For affine KSK compilation, exact correctness forces the public equation \(L\circ A=G\), together
with a stringent shortness or covariance requirement. Resolving that public batch-preimage
problem, avoiding it with a proved nonlinear construction, or adopting a stronger
trapdoor-augmented dual mode is the substantive open step.
