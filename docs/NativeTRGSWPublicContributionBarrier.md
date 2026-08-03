# Native secret-message TRGSW public-contribution barrier

## Status

The remaining source-aligned BRK/KSK step is a cryptographic research problem, not merely an
implementation or proof-assistant task. The correlated KSK row formula and its cancellation law
are algebraically exact. What remains is to connect the native secret-message TRGSW distribution
to the public-linear BRK distribution required by the ordinary RLWE/LWE reduction.

This note explains the mismatch precisely. It is not an impossibility theorem for every possible
reduction. It shows that the currently desired *exact public-linear normal form* does not directly
describe the native nonce rows.

## 1. Setting

Work in a negacyclic ring

\[
  R_q = \mathbb Z_q[X]/(X^N+1).
\]

Split the ring secret as

\[
  s = E(p)+O(z),
\]

where $p$ is the binary prefix secret, $z$ is the independent suffix secret, and $E,O$
are the public embeddings of the two blocks. A bootstrapping-key entry encrypts the control bit

\[
  m=p_i
\]

as a TRGSW ciphertext under $s$. Let $h$ be one public gadget value. Use the rank-one TRLWE
convention

\[
  b=a s+e,
\]

so that its phase is $b-a s=e$.

The source-aligned theorem seeks a public map $B$, computed from the displayed gadget or mask,
such that the prefix-dependent part of every BRK body is

\[
  B(A)^{\mathsf T}p.
  \tag{1}
\]

Expression (1) is linear in $p$. This permits the prefix part to be replaced by an ordinary
binary-secret LWE hybrid while the suffix part is replaced by ordinary ternary RLWE.

## 2. Body rows are publicly linear

A body row adds $h p_i$ to the body component:

\[
  A=a,
  \qquad
  b=a s+e+h p_i.
\]

After splitting $s$,

\[
  b
  =A O(z)+e+A E(p)+h p_i.
  \tag{2}
\]

For a fixed displayed mask $A$, both $A E(p)$ and $h p_i$ are public linear functions of
$p$. Thus body rows admit the required contribution map.

## 3. Nonce rows contain secret products

A nonce row adds the message gadget to the mask rather than the body. If $a$ is the mask of the
underlying zero encryption, the displayed mask and body are

\[
  A=a+h p_i,
  \qquad
  b=a s+e.
\]

Eliminating the hidden raw mask $a=A-hp_i$ gives

\[
\begin{aligned}
  b
    &=(A-hp_i)s+e \\
    &=A O(z)+A E(p)+e
      -h p_i O(z)-h p_i E(p).
\end{aligned}
\tag{3}
\]

The last two terms are the obstruction:

- $p_i O(z)$ is bilinear in the prefix and suffix secrets;
- $p_i E(p)$ contains quadratic products $p_i p_j$.

Neither term is generally representable by a public matrix applied linearly to $p$. Moreover,
the raw uniform mask $a=A-hp_i$ cannot be recovered from the displayed mask without knowing
$p_i$. Treating $a$ as though it were public would therefore give the reduction information
that is absent from the actual public transcript.

## 4. Why correctness does not prove security

During honest key generation, both $p$ and $z$ are available. The generator can evaluate the
complete native message phase, including the terms in (3), and form a correlated KSK row whose
body is

\[
  \langle U,p\rangle+b-\mathsf{messagePhase}+F,
  \tag{4}
\]

where $U$ is an independent uniform prefix mask and $F$ is an independent fresh correction.
Equation (4) gives exact phase cancellation and hence correctness.

A security reduction is in a different position. It normally receives an LWE or RLWE challenge
without at least one corresponding secret block. A suffix-RLWE reduction may sample and know
$p$, while a prefix-LWE reduction may sample and know $z$; neither fact supplies the exact
public-linear normal form required by the current two-hop theorem. In particular, the
prefix-LWE hop cannot evaluate the quadratic prefix products. A different reduction might
reparameterize some mixed terms rather than evaluate them, but that would be a new joint-law
argument. The simulator also cannot silently receive the honest key generator's complete private
witness. Consequently, an exact implementation of (4) does not by itself instantiate the public
map required by (1).

## 5. Why a binary prefix does not remove the problem

For binary $p$, the diagonal identity $p_i^2=p_i$ simplifies some quadratic terms. It does not
remove

\[
  p_i p_j \quad (i\ne j)
  \qquad\text{or}\qquad
  p_i z_j.
\]

Thus restricting the prefix secret to binary does not turn the nonce-row distribution into an
ordinary linear LWE/RLWE source. The mixed prefix-suffix products remain even when the suffix is
binary; a ternary suffix is not the cause of this obstruction.

## 6. The missing bridge theorem

Let

\[
  \mathsf{Native}_{\mathrm{real}},\quad
  \mathsf{Native}_{\mathrm{zero}}
\]

be the complete native cloud-key experiments, and let

\[
  \mathsf{Aligned}_{\mathrm{real}},\quad
  \mathsf{Aligned}_{\mathrm{zero}}
\]

be the source-aligned experiments covered by the ordinary ternary-RLWE and binary-LWE theorem.
A sufficient bridge would construct efficient reductions satisfying

\[
\begin{aligned}
  \Delta(\mathsf{Native}_{\mathrm{real}},
         \mathsf{Aligned}_{\mathrm{real}})&\le \varepsilon_{\mathrm{real}},\\
  \Delta(\mathsf{Native}_{\mathrm{zero}},
         \mathsf{Aligned}_{\mathrm{zero}})&\le \varepsilon_{\mathrm{zero}},
\end{aligned}
\tag{5}
\]

where $\Delta$ is statistical distance or the advantage of an explicitly stated computational
game. Combining (5) with the aligned theorem would give a bound of the form

\[
  \operatorname{Adv}_{\mathrm{native}}
  \le
  \varepsilon_{\mathrm{real}}
  +2\varepsilon_{\mathrm{RLWE}}
  +4\varepsilon_{\mathrm{LWE}}
  +\varepsilon_{\mathrm{zero}}.
  \tag{6}
\]

The bridge must retain the complete correlated BRK, KSK, and auxiliary-key transcript. Proving
only a one-row marginal statement is insufficient, because an adversary can test relations
between rows and between the two key families.

## 7. Why this is a hard proof

The desired bridge has to solve several cryptographic problems simultaneously:

1. It must consistently simulate or reparameterize the mixed products $p_i z_j$ across the
   suffix and prefix hybrids, while the quadratic products $p_i p_j$ remain unavailable to the
   ordinary prefix-LWE reduction.
2. It must preserve the complete joint distribution rather than only individual ciphertext
   marginals.
3. It must avoid a hybrid loss proportional to the very large number of scalarized rows.
4. It must retain the shared secret and shared-error correlations needed for cancellation.
5. It must use an assumption that actually implies circular or quadratic-KDM security; ordinary
   IND-CPA security alone does not generally imply such security.
6. Its transformed errors must still satisfy the correctness budget.

These are mathematical security-reduction requirements. Formalizing a valid bridge in a proof
assistant would be technical work after the bridge is discovered, but discovering and proving the
bridge itself is research-level work.

## 8. Plausible routes

### Direct quadratic or circular-KDM reduction

Prove that the complete family of native terms in (3), supplied as correlated auxiliary input,
is pseudorandom under a standard ring assumption. This is the most direct route, but it needs a
multi-row joint theorem with mixed prefix-suffix products and quantitative loss independent of
the transcript width.

### Dual-mode or trapdoor distribution

Replace or augment the public gadget distribution with a computationally indistinguishable mode
that gives the simulator a hidden mechanism for programming the secret-product rows. An
NTRU-style trapdoor is one possible realization, but any such route must state the additional
assumption and prove complete-view indistinguishability.

### Modified TRGSW or cloud-key format

Change the scheme so that the published BRK contribution is public-linear by construction. This
may remove the bridge problem, but it proves a modified scheme and requires a new functionality,
correctness, and performance analysis.

### Explicit joint-KDM assumption

State the complete native BRK/KSK distribution directly as a joint auxiliary-input KDM
assumption. This gives a clean conditional theorem, but it is a stronger and less standard
premise than ordinary RLWE/LWE.

## 9. Current stopping point

The following parts are technical and already resolved at the mathematical interface:

- exact correlated-row generation after the BRK is fixed;
- reuse and cancellation of the BRK error;
- independent fresh-correction sampling;
- factor-weighted key-switch algebra; and
- equality of the conditional executable sampler with the aligned real view.

The unresolved part is precisely (5): a standard-assumption bridge from native secret-message
TRGSW nonce rows to that aligned view. Until such a theorem or an explicit stronger assumption is
provided, the source-aligned result does not establish native TFHE circular security.

The companion [native TRGSW spectral-boundary note](NativeTRGSWBarrierAndSpectralBoundary.md)
formalizes this row-local obstruction and the alternative conditional Walsh/posterior route.  Its
remaining premise is complete-channel diagonal spectral decay, not a recovered public raw mask.
