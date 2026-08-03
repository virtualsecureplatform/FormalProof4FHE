# Remaining hard proofs for the native TRGSW spectral route

> Status update: `NativeTRGSWSpectralInfeasibility.lean` now resolves the feasibility check from
> hard problem 2 conditionally in the negative, formalizes hard problem 3 as a two-hop corollary,
> and packages hard problem 1 as one heterogeneous complete-batch affine assumption with the
> bounded-leakage loss. See `NativeTRGSWSpectralInfeasibility.md`. The positive statistical-decay
> route described below should therefore be read as superseded whenever the concrete native KSK
> satisfies the stated typical-set separation and correctness bounds. The remaining research
> targets are a reduction for the joint affine source, a zero-row RLWE reduction for the now
> concrete native aggregate experiments, and improvement of its full-key concentration loss.
> `NativeTRGSWConcreteSuffixSeparation.lean` and
> `NativeTRGSWConcreteBRKRecovery.lean` now discharge those KSK and correct-key BRK conditions
> for the proof-aligned bounded-CBD model, so this is no longer only a hypothetical feasibility
> warning for that model. `NativeTRGSWAggregateSecurityAndComplexityLeveraging.lean` now supplies
> the aggregate high-pass replacement and its optimal match-and-square reduction. The remaining
> aggregate research issue is narrower: reduce the complete native constructor to an accepted
> source and avoid its exponential full-key Renyi-half concentration loss.
> See `NativeTRGSWAggregateZeroRowHardProblem.md` for the exact builder conditions, the
> full-key-loss theorem, and the projected-leakage improvement target.

## Scope

This note isolates the mathematical research problems that remain after constructing the exact
native shared-prefix/suffix channel. It does not list routine formalization, parameter arithmetic,
or sampler-conformance work.

Let

```text
p ∈ {0,1}^t,   z ∈ {0,1}^(N-t),   s = Nest(p,z),
```

where `p` is the scalar prefix key, `z` is the independent suffix, and `s` is the resulting ring
key. For a binary BRK message vector `m`, write

```text
V(p,z;m) = (BRK_s(m), KSK_p(z)).
```

The complete view retains the BRK and KSK together. Their shared key material may not be erased by
replacing the two components through separate marginal arguments.

The following layer is already resolved exactly. Once `m` is fixed and known to the reduction,
each normalized native TGSW body has the affine form

```text
<s, A - H_mask(m)> + H_body(m) + e.
```

This equality holds for the complete BRK and remains valid while retaining the real correlated
KSK and sampling the suffix. The remaining questions concern the security of that joint affine
source and the proposed spectral tail, not the TGSW row algebra.

## Hard problem 1: joint affine BRK/KSK source security

### Target statement

For every nonempty Walsh support `S ⊆ [t]` with `|S| ≤ d`, reveal only the restricted prefix
value

```text
λ = p restricted to S.
```

The desired theorem must turn the corresponding low-frequency correlation of the complete view
into a leakage-removal experiment whose advantage is at most `δ_d`.

Equivalently, for every efficient complete-view distinguisher, it should construct efficient
ordinary-assumption adversaries satisfying

```text
Adv_joint-affine(S)
  ≤ Adv_RLWE(B_S) + Adv_LWE(K_S) + ε_S,
```

where `ε_S` is a proved reduction loss and the reductions reproduce the joint law, not merely its
BRK and KSK marginals. A uniform bound on the right-hand side for every `|S| ≤ d` would supply
`δ_d`.

The conditioned source has two coupled parts:

```text
(A_j, A_j s + u_j(m) + e_j)_j
```

for the affine ring rows, and

```text
(U, Uᵀ p + Hᵀ z + e_K)
```

for the KSK. The first uses the combined key `s = Nest(p,z)`; the second encrypts an affine
function of `z` under `p`. Both occur in the same adversarial view.

### Why this is not a marginal hybrid

Ordinary RLWE does not automatically remain secure after giving the adversary a KSK computed from
the same `p,z`. Conversely, ordinary LWE does not automatically remain secure after giving the
adversary ring samples under `s = Nest(p,z)`. Either replacement would supply the underlying
assumption with secret-dependent auxiliary input that is absent from its ordinary game.

The known-message affine normalization removes the native TGSW bilinear phase, but it does not
remove this auxiliary-input correlation. Existing direct multi-key affine reductions also do not
apply verbatim: the BRK uses structured ring multiplication, whereas the KSK uses scalar masks and
coefficient messages.

### What would resolve it

Any one of the following would suffice, provided the complete experiment is matched exactly.

1. A heterogeneous master-mask reduction combining structured RLWE rows and scalar LWE rows while
   preserving the shared prefix/suffix key law.
2. A reduction through a common module representation that proves the ring-mask structure and
   scalar KSK challenges remain distributed exactly as required.
3. A clearly stated joint auxiliary-input RLWE/LWE assumption for this affine source, followed by
   a separate justification that the assumption is acceptable.

The first two would be reductions to standard assumptions. The third is a sound conditional
theorem but leaves a nonstandard cryptographic premise.

## Hard problem 2: high-frequency posterior spectral decay

### Target statement

Let `W(v | p,m)` be the complete conditional channel, including suffix sampling, BRK, KSK, and
every retained correlated value. Define the uniform-input view mass

```text
μ(v) = 2^(-2t) · sum_(p,m) W(v | p,m).
```

For a Walsh support `S ⊆ [t]`, define the totalized posterior parity

```text
           sum_(p,m) W(v | p,m) χ_S(p) χ_S(m)
g_S(v) =  -------------------------------------
                sum_(p,m) W(v | p,m)
```

when the denominator is nonzero, and define `g_S(v) = 0` otherwise. Its posterior spectral radius
is

```text
θ_S = sqrt(sum_v μ(v) g_S(v)^2).
```

The current statistical route requires a degree `d` and a small bound `τ_d` satisfying

```text
sum_(S : |S| > d) θ_S ≤ τ_d.                 (Spectral decay)
```

For an asymptotic security theorem, the complete bound after including the number of low supports
must be negligible.

### Why this is particularly difficult

This is an information-theoretic statement. The posterior is allowed unlimited computation.
Ordinary LWE or RLWE asserts computational difficulty; it does not say that the secret remains
statistically ambiguous after all samples are observed.

If some decoder predicts the diagonal parity

```text
χ_S(p) χ_S(m)
```

with probability at least `1 - ε`, then necessarily

```text
θ_S ≥ 1 - 2ε.
```

Thus sufficiently informative small-noise transcripts can make the desired tail bound false even
when recovering the secret is computationally expensive. A large number of evaluation-key rows
makes this possibility especially important. Computational lattice hardness cannot be used as a
proof of the statistical inequality above.

### What would resolve it

There are three logically distinct outcomes.

1. **Positive statistical theorem.** Prove the spectral-decay inequality for the actual channel
   by showing substantial posterior ambiguity remains even for an unbounded observer.
2. **Infeasibility theorem.** Construct decoders or posterior lower bounds showing that the sum is
   large for the intended channel. This would rule out the present statistical route rather than
   certify it.
3. **Computational replacement.** Replace `θ_S` by a notion restricted to efficient tests and
   prove a new tail theorem. Bounding each coefficient separately is insufficient: the original
   inequality sums exponentially many high-frequency coefficients. The replacement must avoid an
   exponential collection of reductions, for example through a direct randomized-frequency or
   aggregate-tail game.

The third outcome is plausibly the most relevant for practical small-noise TFHE, but it is a new
cryptographic theorem rather than a change of constants in the existing proof.

## Hard problem 3: independent-message to zero-message endpoint

### Target statement

Let `p,z,m` be independent binary samples and let `0` denote the all-zero BRK message. For every
efficient distinguisher `D`, prove

```text
|Pr[D(V(p,z;m)) = 1] - Pr[D(V(p,z;0)) = 1]| ≤ ε_0,
```

with `ε_0` negligible under the selected assumptions.

### Classification

This endpoint is mostly a technical corollary after a satisfactory joint affine-source theorem is
available: the reduction samples `m`, applies the known-message affine normalization, and uses the
joint source replacement.

Without hard problem 1, however, the endpoint is not ordinary BRK IND-CPA security. The retained
KSK is secret-dependent auxiliary input correlated with the same ring key, so a direct appeal to a
BRK or RLWE marginal theorem is insufficient. In that setting the endpoint inherits the same
hard auxiliary-input issue as the joint affine source.

## Dependency and recommended order

The logical dependency is

```text
joint affine-source theorem ──▶ low-degree certificate
             │
             └───────────────▶ random-message/zero endpoint

posterior spectral decay or a computational replacement ──▶ high-degree bound

low-degree bound + high-degree bound + endpoint ──▶ native circular-security bound
```

The recommended research order is:

1. determine whether statistical spectral decay is even plausible by seeking explicit posterior
   or decoder lower bounds;
2. reduce the formalized concrete native aggregate games to a complete zero-row source and seek
   a subexponential concentration loss before doing more parameter work;
3. separately pursue the heterogeneous joint affine BRK/KSK reduction; and
4. derive the random/zero endpoint only after the joint theorem fixes the admissible assumption.

The spectral feasibility check comes first because a negative result would invalidate the current
tail route independently of any success on the low-degree reduction.

## Statements that do not solve these problems

The following facts are useful but insufficient on their own:

- security estimates for the BRK and KSK marginals;
- public xor normalization of the native BRK;
- the known-message affine row identity;
- exact equality of the conditioned view with the joint affine view;
- a small finite leakage carrier;
- correctness or noise-overflow estimates; and
- ordinary computational LWE/RLWE hardness used as if it implied statistical posterior entropy.

Once hard problems 1 and 2 are resolved in an appropriate form, instantiating the finite
certificate, composing the endpoint, and checking concrete parameter inequalities are technical
tasks.
