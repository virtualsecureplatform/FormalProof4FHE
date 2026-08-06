# A minimal circular-security assumption for native self-key TFHE

This note gives a self-contained security statement for a native, rank-one, shared-key TFHE
cloud key. Its purpose is to isolate the single nonstandard circular assumption from the
ordinary message-hiding part of the proof.

The conclusion is a concrete game bound:

```text
native TFHE advantage
  <= circular-correlation advantage + standard endpoint advantage.
```

Correctness is a separate requirement and is not implied by this confidentiality theorem.

## 1. Parameters and keys

Let `N=t+u` and

```text
R_q = Z_q[X] / (X^N + 1)
```

be the rank-one negacyclic RLWE ring. Split the binary secret coefficients into a prefix of
length `t` and a suffix of length `u`:

```text
P = (p_0,...,p_{t-1}) in {0,1}^t,
Z = (z_0,...,z_{u-1}) in {0,1}^u.
```

The complete ring secret is

```text
S(P,Z) = sum_i p_i X^i + sum_j z_j X^(t+j) in R_q.
```

The prefix `P` is also the scalar TLWE key encrypted by the bootstrapping key. Thus there is one
master secret, not an independent input key and bootstrapping key.

Fix the following public parameters as part of a parameter tuple `Theta`:

- the modulus and ring dimension;
- the prefix and suffix dimensions;
- the TRGSW and key-switch gadget vectors;
- the complete ring-error and scalar-error laws;
- the row ordering and representation conventions; and
- any prescribed public auxiliary transcript sampler.

No concrete numerical values are required by the theorem.

## 2. Native bootstrapping rows

Let `g_l` be a TRGSW gadget value and let `m_i` be the bit encrypted at control coordinate `i`.
For independently uniform masks `a^N_(i,l), a^B_(i,l) in R_q` and prescribed errors
`e^N_(i,l), e^B_(i,l)`, the rank-one native nonce and body rows are

```text
N_(i,l) = (a^N_(i,l) + g_l m_i,
           a^N_(i,l) S + e^N_(i,l)),

B_(i,l) = (a^B_(i,l),
           a^B_(i,l) S + e^B_(i,l) + g_l m_i).
```

For a ring row `(A,B)`, use phase convention

```text
phi_S(A,B) = B - A S.
```

Direct substitution gives

```text
phi_S(N_(i,l)) = e^N_(i,l) - g_l m_i S,
phi_S(B_(i,l)) = e^B_(i,l) + g_l m_i.
```

Consequently, when `m_i=p_i`, the native BRK contains both the hidden coefficient `p_i` and the
coefficient product `p_i S`. This is precisely the circular relation that ordinary public-affine
RLWE does not remove.

Write

```text
BRK(P,Z;M)
```

for the complete collection of these rows under `S(P,Z)` with message vector
`M=(m_0,...,m_{t-1})`. All masks and errors are sampled jointly according to the fixed law in
`Theta`.

## 3. Retained native key-switch key

The suffix key is switched to the scalar prefix key. For a key-switch gadget value `k_r`, a
suffix coordinate `z_j`, a uniform scalar mask `v_(j,r) in Z_q^t`, and scalar error
`eta_(j,r)`, the corresponding TLWE row has the form

```text
KSK_(j,r) = (v_(j,r), <v_(j,r),P> + eta_(j,r) + k_r z_j).
```

Let

```text
KSK(P,Z)
```

denote the complete native table. The same genuine KSK is retained in every security game. It is
not independently resampled under an unrelated key, and joint security is not inferred from a
separate KSK marginal.

Define the native cloud key with control message `M` by

```text
CK(P,Z;M) = (BRK(P,Z;M), KSK(P,Z)).
```

## 4. Optional ciphertext or auxiliary transcript

Let `A(P)` be a fixed probabilistic transcript sampler whose private randomness is independent of
the BRK/KSK randomness conditional on `P`. It may contain:

- a base TLWE ciphertext challenge under `P`;
- public metadata; or
- their product.

The complete public view is

```text
View(P,Z;M) = (CK(P,Z;M), A(P)).
```

Taking `A(P)` to be empty gives the cloud-key-only theorem. More complicated state correlated
with cloud-key randomness requires a genuinely joint definition of `View`, or an explicit
sampler-distance term.

## 5. The three games

All secret samples below are mutually independent unless equality is explicitly written.

### Self game

```text
P <- uniform {0,1}^t
Z <- uniform {0,1}^u
return View(P,Z;P)
```

The BRK encrypts the prefix of its own ring encryption key. This is the real native self-key
cloud-key distribution. Concatenation is a bijection between `(P,Z)` and a binary coefficient
vector of length `N`, so independent uniform `P` and `Z` give exactly the ordinary uniform binary
ring-key law.

### Independent-control game

```text
P <- uniform {0,1}^t
M <- uniform {0,1}^t, independently of P
Z <- uniform {0,1}^u
return View(P,Z;M)
```

The encryption key remains `S(P,Z)`, but the BRK control message is an independent binary vector.
The KSK and auxiliary transcript retain their genuine dependence on `(P,Z)` and `P`,
respectively.

### Zero game

```text
P <- uniform {0,1}^t
Z <- uniform {0,1}^u
return View(P,Z;0)
```

Only the BRK message is zeroed. The genuine suffix KSK and the prescribed transcript remain.

For samplers `G_0,G_1` and a probabilistic distinguisher `D`, define

```text
Adv(G_0,G_1;D)
  = |Pr[D(G_0)=1] - Pr[D(G_1)=1]|.
```

## 6. Minimal circular assumption

The sole nonstandard assumption is the following.

### Native coefficient-product correlation assumption

For every allowed efficient distinguisher `D`,

```text
Adv(Self,Independent;D) <= epsilon_corr.
```

Equivalently, replacing the self control vector `P` by an independent vector `M` is hard even
when the distinguisher receives the complete native BRK, the genuine same-key suffix KSK, and the
prescribed transcript.

This assumption is deliberately narrow:

- it concerns one fixed native batch;
- it permits only the fixed key-message vector used by the BRK;
- it is nonadaptive;
- it contains one key cycle; and
- it does not assert security for arbitrary KDM functions or arbitrary leakage.

It is still a genuine cryptographic assumption. The theorem below does not derive it from
ordinary RLWE.

## 7. Standard endpoint

Let `Ideal` be the final confidentiality experiment on the same public-view carrier. Assume

```text
Adv(Independent,Ideal;D) <= epsilon_std.
```

This is the standard part because the reduction samples `M` itself and therefore knows every
BRK plaintext. It can be split into two transitions:

```text
Independent -> Zero -> Ideal.
```

If

```text
Adv(Independent,Zero;D) <= epsilon_ind0
```

and

```text
Adv(Zero,Ideal;D) <= epsilon_0,
```

then the triangle inequality gives

```text
Adv(Independent,Ideal;D) <= epsilon_ind0 + epsilon_0.
```

Thus one may take `epsilon_std = epsilon_ind0 + epsilon_0`.

For a fixed known bit `m_i`, a homogeneous RLWE row `(A,A S+e)` is converted publicly into the
body and nonce rows by

```text
body:  (A,A S+e) -> (A,A S+e+g_l m_i),
nonce: (A,A S+e) -> (A+g_l m_i,A S+e).
```

Both maps are translations and therefore permutations on a uniform row source. Applying them
coordinatewise handles the complete BRK in one batch while preserving its full error vector.

Using a real-versus-uniform complete-batch RLWE source, public known-message translation gives the
typical bound

```text
epsilon_ind0
  <= 2 epsilon_RLWE + epsilon_layout + epsilon_aux.
```

The factor two is the usual single-challenge branch-selection cost. It is independent of the
number of BRK rows when the complete batch is replaced in one source game. Because the genuine
KSK and transcript are retained, the source theorem must include them as challenge-safe state or
as part of one explicitly stated joint RLWE/LWE source; separate marginal assumptions do not by
themselves establish this endpoint.

## 8. Security theorem

### Theorem

Under the native coefficient-product correlation assumption and the standard endpoint,

```text
Adv(Self,Ideal;D) <= epsilon_corr + epsilon_std.
```

If an implementation sampler `Real` differs from `Self` by at most `epsilon_samp`, then

```text
Adv(Real,Ideal;D)
  <= epsilon_samp + epsilon_corr + epsilon_std.
```

With the split standard endpoint, this becomes

```text
Adv(Real,Ideal;D)
  <= epsilon_samp
     + epsilon_corr
     + 2 epsilon_RLWE
     + epsilon_layout
     + epsilon_aux
     + epsilon_0.
```

### Proof

Insert the independent-control game between the self and ideal games:

```text
Adv(Self,Ideal;D)
  <= Adv(Self,Independent;D)
     + Adv(Independent,Ideal;D)
  <= epsilon_corr + epsilon_std.
```

For a nonexact implementation sampler, insert `Self` after `Real` and apply the triangle
inequality once more. Substituting the two standard endpoint bounds yields the expanded formula.

No row-count hybrid, square-root concentration loss, or hidden projection step occurs in this
composition.

## 9. From the public view to evaluated ciphertexts

Include the base ciphertext challenge in `A(P)`. Any public TFHE evaluation algorithm, including
blind rotation and CMUX, is post-processing of the complete public view. Therefore a
distinguisher for an evaluated ciphertext induces a distinguisher for that view with the same
advantage. Public evaluation introduces no additional confidentiality assumption.

This observation does not establish correctness. Noise growth, rounding, decoding, and failure
probability must be bounded separately for the selected parameters.

## 10. Why the assumption is close to minimal

A shorter-looking direct assumption would assert

```text
Self approximately equals Zero.
```

That is sufficient but stronger: it combines the circular correlation and ordinary message
hiding into one opaque premise.

The correlation assumption isolates only

```text
View(P,Z;P) -> View(P,Z;M).
```

After this step, all BRK messages are independently sampled and known to the reduction.

For the unchanged native CMUX format, replacing this premise by security of only an aggregate
encryption of `S^2` is insufficient. Aggregation discards the individual encrypted control rows
used by CMUX. Likewise, assuming security only for nonce rows omits the body rows encrypting the
hidden coefficients `p_i`.

Thus the coefficient-product correlation game is the narrowest assumption currently connected
to the complete unchanged native view by exact transformations.

## 11. Formal correspondence

The mathematical objects above correspond to the following checked definitions and theorems:

- the reusable `Self -> Independent -> Zero` structure is `ThreeGameExperiment`;
- the literal cloud-key games are packaged by `nativeCloudKeyExperiment`;
- the three sampler identities are
  `nativeCloudKeyExperiment_selfSampler_eq_diagonalNativeView`,
  `nativeCloudKeyExperiment_independentSampler_eq_independentMessageNativeView`, and
  `nativeCloudKeyExperiment_zeroSampler_eq_zeroMessageNativeView`;
- equality of `Self` with the native real cloud-key law is
  `nativeCloudKeyExperiment_selfSampler_evalDist_eq_realCloudKeyView`;
- the cloud-key-only conclusion is
  `nativeCloudKeySecurity_le_correlation_add_standard`; and
- the version retaining `A(P)` is
  `nativeCompleteViewSecurity_le_correlation_add_standard`.

These formal results introduce no additional cryptographic axiom. The correlation and standard
endpoint bounds are ordinary proposition parameters supplied to the final theorem.
