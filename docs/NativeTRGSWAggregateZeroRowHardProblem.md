# Native aggregate zero-row reduction and concentration problem

## Purpose

The native aggregate games are now mathematically explicit. What remains is to justify their
computational security from an accepted zero-row RLWE problem with a quantitatively useful loss.

There are two different tasks here:

1. instantiate the full-key match-and-square construction for the complete native transcript;
2. avoid the exponential cost of guessing the complete key.

The first task may become distributional proof work once an exact source problem has been fixed.
The second is the genuinely hard cryptographic problem. A full-key construction with an
exponential loss is not yet a practical polynomial-hardness proof.

## 1. Native aggregate games

Let the complete master key be

\[
  K=(P,Z)\leftarrow\chi_K,
\]

where $P\in\{0,1\}^t$ is the binary control-key prefix and $Z$ is the remaining ring-key
material. Let $S(K)\in R_q$ be the corresponding ring secret. Write

\[
  \mathsf{View}_K(M)
\]

for the complete public cloud-key transcript generated under $S(K)$ with BRK message vector
$M$. This view includes the complete native TRGSW bootstrapping key, the correlated KSK, and
every retained auxiliary object.

For a cutoff $d<t$, let $Q_d^+$ and $Q_d^-$ be the positive and negative normalized Jordan
laws of the canonical Walsh high-pass measure. The aggregate games are

\[
  \mathsf{Agg}_d^b:
  \quad K=(P,Z)\leftarrow\chi_K,
  \quad C\leftarrow Q_d^b,
  \quad \text{output }\mathsf{View}_K(P\oplus C),
  \qquad b\in\{+,-\}.
\]

The mask $C$ is private challenger randomness. The security quantity to be bounded is

\[
  \operatorname{Adv}_{\mathrm{agg},d}(D)
  =\left|
      \Pr[D(\mathsf{Agg}_d^+)=1]
      -\Pr[D(\mathsf{Agg}_d^-)=1]
    \right|.
\]

The Fourier argument needs this one signed aggregate advantage; it does not require separate
bounds for every high-degree Fourier coefficient.

## 2. Candidate zero-row source

Let one complete native BRK require $m_{\mathrm B}$ zero-ring rows. The real source supplies two
conditionally independent batches under one hidden master key:

\[
  \mathsf{ZR}_{\mathrm R}(K)
  =\left\{
      (A_\rho,A_\rho S(K)+E_\rho)
    \right\}_{\rho=1}^{2m_{\mathrm B}}.
\]

The uniform source replaces every pair by an independent uniform ring pair:

\[
  \mathsf{ZR}_{\mathrm U}
  =\left\{
      (A_\rho,U_\rho)
    \right\}_{\rho=1}^{2m_{\mathrm B}}.
\]

The two halves must be independent conditioned on $K$, because match-and-square multiplies the
signed responses of two independently constructed views.

An accepted source theorem must specify all of the following:

- the exact ring and modulus family;
- the mixed binary/ternary secret law induced by $K$;
- the error law used by every zero row;
- the number of rows exposed under one secret; and
- whether any public auxiliary information is included in the source experiment.

Calling this source merely “RLWE” is insufficient if its secret, sample count, error law, or
auxiliary transcript differs from the standard assumption being invoked.

## 3. Full-key diagonal builder

For a known fake key \(\widehat K=(\widehat P,\widehat Z)\), a source half \(\mathcal R\), and a
sign $b$, consider a builder

\[
  \mathsf{Build}_b(\widehat K,\mathcal R).
\]

It should:

1. sample $C\leftarrow Q_d^b$ and set \(\widehat M=\widehat P\oplus C\);
2. add the public native TRGSW gadget offsets for the known vector \(\widehat M\) to the zero
   rows in \(\mathcal R\);
3. generate the KSK and all auxiliary objects using \(\widehat K\), or replace them with an exact
   complete-view simulator; and
4. return only the public cloud-key view, not $C$ or \(\widehat K\).

The builder must satisfy two complete-view properties.

### Diagonal correctness

When the fake key equals the hidden source key,

\[
  \mathsf{Build}_b(K,\mathsf{ZR}_{\mathrm R}(K))
  \approx_{\sigma_b}
  \mathsf{View}_K(P\oplus C_b),
  \qquad C_b\leftarrow Q_d^b.
\]

The distance or computational defect \(\sigma_b\) must cover the entire transcript. Equality of
the BRK marginal alone is not enough.

### Uniform-source sign erasure

For every fixed fake key,

\[
  \mathsf{Build}_+(\widehat K,\mathsf{ZR}_{\mathrm U})
  \equiv_d
  \mathsf{Build}_-(\widehat K,\mathsf{ZR}_{\mathrm U}),
\]

or the two laws must have an explicitly bounded defect. This normally follows because translating
a uniform row by a public gadget offset preserves uniformity, while the fake-key KSK is sampled
identically in the two sign branches.

Once the exact source transcript is fixed, proving these two properties for the full-key builder
may be technical rather than conceptually new. It nevertheless must preserve the joint BRK/KSK
law, the native nonce and body blocks, row independence, and all auxiliary fields.

## 4. Current match-and-square theorem

Let

\[
  p_k=\Pr[K=k],
  \qquad
  C_{1/2}(K)=\left(\sum_k\sqrt{p_k}\right)^2.
\]

Sample the fake key from the square-root tilted law

\[
  q_k=\frac{\sqrt{p_k}}{\sum_u\sqrt{p_u}}.
\]

For actual key $k$ and fake key \(\widehat k\), let

\[
  \delta(\widehat k,k)
  =\Pr[D(\mathsf{Build}_+(\widehat k,\mathsf{ZR}_{\mathrm R}(k)))=1]
   -\Pr[D(\mathsf{Build}_-(\widehat k,\mathsf{ZR}_{\mathrm R}(k)))=1].
\]

Diagonal correctness identifies the aggregate gap with the weighted diagonal

\[
  \sum_k p_k\delta(k,k),
\]

up to \(\sigma_++\sigma_-\). Squaring two independent source halves and applying weighted
Cauchy--Schwarz gives

\[
  \boxed{
  \operatorname{Adv}_{\mathrm{agg},d}(D)
  \le
  \sigma_++\sigma_-
  +\sqrt{
      2C_{1/2}(K)\,
      \operatorname{Adv}_{\mathrm{ZR}}(B)
    }.
  }
\]

This is a valid complexity-leveraging theorem if the builder and source alignment are proved.
Its problem is quantitative.

## 5. Why the concentration loss is fundamental to this method

For any covering fake-key distribution $q$, weighted Cauchy--Schwarz incurs

\[
  \Gamma(p,q)=\sum_k\frac{p_k}{q_k}.
\]

The square-root tilted law minimizes this expression, and

\[
  \Gamma(p,q)\ge C_{1/2}(K).
\]

Therefore changing the fake-key sampler cannot improve the full-key match-and-square loss. The
problem is not a loose choice of $q$; it is that diagonal correctness is obtained only on the
event \(\widehat K=K\).

For a uniform binary prefix and an independent uniform ternary suffix,

\[
  C_{1/2}(K)=2^t3^r.
\]

For a binary-only key the ternary factor disappears, but $C_{1/2}(K)=2^t$ is still exponential.
Changing the error sampler, modulus, gadget base, or correctness bound does not alter this key-law
factor.

To obtain aggregate advantage at most \(2^{-\lambda}\), the zero-row advantage must satisfy a
condition of the form

\[
  -\log_2\operatorname{Adv}_{\mathrm{ZR}}(B)
  \ge
  \log_2 C_{1/2}(K)+2\lambda+O(1).
\]

Thus ordinary “negligible RLWE advantage” is not a sufficient quantitative statement. The
underlying source must be hard enough to pay for the complete key's order-$1/2$ entropy.

## 6. Precise improvement target: projected leakage

The cleanest possible improvement would replace full-key matching by a lower-entropy value

\[
  L(K)\in\mathcal L.
\]

The desired theorem would construct builders \(\mathsf{Build}_b(\ell,\mathcal R)\) satisfying:

1. **projected diagonal correctness:** when \(\ell=L(K)\), the real-source builder gives the
   aggregate native view, up to a stated defect;
2. **uniform-source sign erasure:** the plus and minus laws are identical or close on a uniform
   source for every fixed \(\ell\);
3. **complete-view preservation:** the BRK, KSK, and auxiliary objects retain their joint law;
4. **efficient construction:** sampling \(L(K)\), the aggregate mask, and the constructed view is
   polynomial time; and
5. **small concentration:** \(C_{1/2}(L(K))\) is polynomial or otherwise small enough for the
   desired security level.

The same proof would then give

\[
  \boxed{
  \operatorname{Adv}_{\mathrm{agg},d}(D)
  \le
  \sigma_{\mathrm{agg}}
  +\sqrt{
      2C_{1/2}(L(K))\,
      \operatorname{Adv}_{\mathrm{ZR}}(B)
    }.
  }
\]

This statement pinpoints the research question:

> Can the complete native aggregate view be programmed from zero rows using only a
> low-concentration projection of the hidden master key?

The KSK is the main difficulty. Generating it honestly normally requires the complete fake key.
Generating it from the hidden-key source without learning that key requires a new joint simulator
or a stronger source interface.

## 7. Plausible research routes

### Blockwise or progressive matching

Partition the master key and try to program only one block at a time. A successful theorem must
show that the aggregate game decomposes into polynomially many block games and that the complete
KSK correlation survives each transition. Merely applying full-key matching independently to
every block can reintroduce the same exponential product.

### Source-provided correlated KSK

Strengthen the zero-row source so that it also supplies a pseudorandom KSK correlated with the
hidden key. This avoids generating the KSK from a guessed full key, but the resulting assumption
is a joint auxiliary-input RLWE problem rather than ordinary zero-row RLWE. A useful result must
either reduce this joint source to standard assumptions or state the stronger premise explicitly.

### Dual-mode or trapdoor programming

Use a computationally indistinguishable key-generation mode in which the reduction can program
the KSK and native gadget rows without knowing the hidden key. This could eliminate full-key
guessing, but it introduces a new trapdoor or dual-mode assumption and requires a complete-view
mode-indistinguishability proof.

### Direct circular or KDM assumption

Assume security of the complete native aggregate transcript directly. This yields a clean
conditional theorem but does not reduce the scheme to ordinary RLWE. It is a valid stopping point
only if the stronger assumption is accepted and stated precisely.

### Complexity leveraging without loss improvement

Keep the exponential factor and select a source problem whose concrete advantage is smaller by
the required entropy margin. This may give a logically valid parameter family, but it does not
remove the proof loss and may require impractical dimensions or noise ratios.

## 8. Known approaches that are insufficient

The following do not solve the hard problem by themselves:

- optimizing the fake-key distribution, because the square-root tilt is already optimal;
- replacing ternary keys by binary keys, because the remaining binary concentration is still
  exponential;
- proving BRK and KSK marginal security separately, because their joint transcript can reveal
  relations hidden by both marginals;
- invoking subspace LWE without a simulator that actually depends only on the claimed subspace
  projection;
- changing CBD, Gaussian, modulus, or gadget parameters, because these affect correctness and
  source hardness but not the full-key matching entropy;
- returning to statistical posterior spectral decay, which is incompatible with reliable
  complete-key and BRK decoding in the small-noise native regime; or
- bounding high-frequency coefficients one at a time, which restores an exponential collection
  of reductions.

## 9. What counts as a resolution

A positive standard-assumption resolution must provide all of the following:

1. an exact definition of the zero-row source and its accepted hardness assumption;
2. a polynomial-time complete-view builder;
3. diagonal correctness for the actual native aggregate games;
4. plus/minus equality on the uniform source;
5. preservation of the correlated BRK, KSK, and auxiliary transcript;
6. a quantitative reduction loss that is subexponential, or a proof that the remaining
   complexity-leveraging requirement is satisfiable; and
7. explicit composition with mask-sampler and other finite-distribution defects.

A negative result would also be valuable: for example, a black-box lower bound showing that any
builder with the current source interface must effectively match the complete key. Such a theorem
would justify moving to a joint auxiliary-input assumption, a dual-mode construction, or a
modified cloud-key format.

The immediate proof target is therefore not another Fourier estimate or parameter calculation.
It is either a projected-leakage complete-view constructor, or a lower bound explaining why no
such constructor exists for the current native source interface.
