# Block-categorical self-circular TFHE

`FormalProof4FHE.TFHE.Native.BlockCategoricalSelfCircular` formalizes the finite theorem chain in
`block_categorical_self_circular_tfhe.tex` for a same-key, no-IKS native TFHE view. A block of
length `ell` has `L = ell + 1` categories: zero or one selected coordinate.

## Exact results

The proof-only categorical completion contains one object at every category label. Lean proves
that relabeling this table by a public permutation moves the active one-hot category exactly.
The same relabeling is an explicit equivalence on complete tables, so it preserves the uniform
carrier. The deterministic theorem also tracks the category-indexed coin table pointwise; no
ciphertext arithmetic or error transformation is hidden in this step.

`permutationEvaluation_uniform_evalDist` first proves that evaluation of a uniform finite
permutation is uniform, using an explicit permutation/orbit decomposition.
`candidateStabilizerImage_uniform_evalDist` then represents a candidate stabilizer as the full
permutation group on the candidate's complement and proves that a wrong actual category has a
uniform complement orbit. `compatibleWrongCandidates` counts the resulting candidate/image
pairs. Its cardinality is `L - 1` on the diagonal and `L - 2` off the diagonal. After
normalization by the two complement choices,
`countedWrongCandidateKernel_eq` proves the exact transition probabilities. The checked identity
is

```text
K_L = lambda_L I + (1 - lambda_L) J,
lambda_L = 1 / (L - 1)^2.
```

For `L >= 3`, Lean then proves

```text
L / (1 - lambda_L) = (L - 1)^2 / (L - 2)
```

and derives the signed category-prediction identity, the exact independent-uniform baseline
`1 / L`, and the block-hybrid telescope. The telescope sums local block prediction excesses; it
does not contain the full-key factor `L^k`.

The contextual hint-removal step is checked in two equivalent forms. The scalar squared-bias
theorem turns `Pi^2 <= 2 L epsilon` into `Pi <= sqrt (2 L epsilon)`. The game-level theorem
`categoricalLeakageRemovalBridge` specializes the existing finite leakage-removal theorem to a
single `L`-valued block category. The isolated-block and final-block ordinary-source corollaries
are also explicit.

`blockCategoricalSelfCircular_le` composes the local terms with the independent-message-to-zero
CVZR endpoint. `realToIdealBlockCategorical_le` then applies a second triangle to the correlated
zero-BRK endpoint. Its result is the manuscript's bound

```text
coefficient(L) * sum_b sqrt (2 L epsilon_ctx,b)
  + 2 epsilon_CVZR
  + 2 epsilon_zero_source
  + epsilon_sampler,
```

where `coefficient(L) = (L - 1)^2 / (L - 2)`. Every finite representation, sampler, and auxiliary
defect is supplied explicitly and charged once.

For the correlated endpoint, reciprocal negacyclic sample extraction is proved bijective from its
checked involution, so a uniform ring mask becomes an exactly uniform scalar mask. For the
original `ell`-ciphertext representation, Lean constructs the integer simplex affine action,
proves its action on every category vertex, and gives a barycentric equivalence with an explicit
inverse over every additive coefficient carrier. This supplies the constructive unimodularity
certificate and exact preservation of a finite uniform carrier. Any mismatch of the transformed
joint error law remains, correctly, a representation defect.

## Baseline and boundary

The full uniform block key has order-half Renyi concentration `(ell + 1)^blockCount`, recovering
the exponential match-and-square baseline.

The translation-only lower bound in the TeX manuscript needs a stronger premise than its stated
single nonperiodic category pair. Recovering every future category requires pairwise separation
of all target laws, or directly that equal leakage values imply equal future tuples. Lean proves
the corrected implication in `futureCategories_separated_of_exactCompiler` and then proves the
concentration lower bound for a uniform product key. A single separated pair cannot justify the
stronger conclusion.

Finally, `opaqueTokenEqualityGap_pos` and `no_zeroSource_blackBoxBound` formalize the concrete
oracle countermodel: equality distinguishes a repeated uniform key token from two independent
tokens with positive gap `1 - L^(-k)`, while an ordinary source term and an equivariance defect
can both be zero. The metamathematical phrase “no relativizing theorem” is not encoded as an
internal proposition; the explicit countermodel is.

## Remaining cryptographic premise

The file does not construct or assume an ordinary-RLWE reduction for the contextual two-copy
source retaining future genuine secret-message blocks and same-key auxiliary state. Its
advantages are parameters of the final Lean theorem. Proving them small from standard
block-binary RLWE requires additional algebra of the native negacyclic channel, a hidden
lossy/dual mode, an acyclic key graph, or an explicit contextual auxiliary-input assumption.
