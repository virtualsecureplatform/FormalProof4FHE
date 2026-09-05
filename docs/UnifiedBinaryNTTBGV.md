# Unified Binary-NTT BGV manuscript audit

Source: `sketch/unified_binary_ntt_bgv_proofs.tex`.
New declarations: `FormalProof4FHE/RLWE/UnifiedBinaryNTTBGV.lean`.

## Checked additions

- `randomMaskMap_real` and `randomMaskMap_uniform`: two source rows per
  output yield the complete random-mask automorphism table. The output exposes
  both masks. The error is exactly the sum of one source error and an
  automorphed second error. Uniformity is proved for the entire table by a
  surjective additive homomorphism, without assuming independent NTT errors.
- `alignedTransition_phase`: the existing affine compiler produces the
  correct row between two distinct operational keys whenever the source and
  target witnesses are aligned. Uniformity follows from the existing compiler
  bijection for this concrete affine form.
- `aligned_charge`, `transition_charge`, `discrepancy_comp`, and
  `pathDiscrepancy_telescope`: group identities for aligned edges, arbitrary
  edges, and finite chronological paths.
- `physicalDiscrepancy_witness` and `normalizedDiscrepancy_witness`: corrected
  witness-coordinate identities, valid even for noncommutative groups.
- `skewOperator_basis` and `skewOperator_unique`: a free permutation family
  has a unique expansion with diagonal coefficients, proved by basis tests.
- `identityOutput_support`: the support conclusion from explicitly assumed
  charge reachability. A complete circuit-syntax induction and cardinality
  lower bound are not asserted by this lemma.

These extend the prior consolidation module. They do not prove fixed-mask
CMAS, instantiate every manuscript theorem, or validate the current paper's
claim that the scalar trace directory is already secure.

## Required qualifications in the manuscript

### HolCMAS coordinates

With group composition acting on the left, put
`delta = y^-1 * lambda * x`. The correct generic identities are

```
(lambda*x*y^-1)(y(T)) = lambda(x(T)),
y^-1(lambda(x(T))) = delta(T).
```

The physical discrepancy is `y*delta*y^-1`. Writing `delta(y(T))` directly
requires commuting automorphisms, as in the cyclotomic group. The new Lean
identities state this distinction explicitly.

### Alignment on a directed graph

Equality of products along all directed paths with the same endpoints is
necessary but insufficient on a general directed graph. For example, orient
all four edges of a square from two source vertices to two sink vertices.
There are no distinct directed paths sharing endpoints. Label three edges by
identity and the fourth by a nonidentity group element. The path condition
holds, but equations `label(v) = operation(e)*label(u)` are inconsistent.

A sufficient general condition is trivial product around every closed walk
in the underlying graph, interpreting a reversed edge by the inverse
operation. Alternatively impose a graph hypothesis, such as a directed root
reaching every vertex, and prove the directed-path formulation under it.
The current Lean addition proves telescoping for paths; it does not assert
the manuscript's unrestricted equivalence.

### Conditional covariance in the affine barrier

An unconditional output covariance bound implies an average multiplier-energy
bound. It does not imply a bound for every mask realization. The proof's
pointwise sparsity/counting argument requires a conditional covariance bound
for each successful mask realization, together with independence of source
errors from masks and the stated independence of fresh correction noise.
This qualification must be explicit before formalizing that probability bound.

### Fourier counterexample scope

In the black-box example `X_s=(A,A xor s)`, the secret is recoverable from the
view as `A xor B`. Thus its marginal uniformity and XOR closure do not imply
fixed-parity hardness. This example refutes extraction from those weaker
properties, but does not itself refute an extractor additionally promised
fixed-parity hardness. The earlier delta-spectrum lemma is a separate
counterexample to a universal heavy-coefficient inference.

### Native correctness and public cover entry

The full-cover compiler algebra is available. A complete refresh theorem must
still instantiate the native decryption/recryption circuit on the actual
cover phases and errors. A diagonal-input circuit identity alone does not
establish correctness on arbitrary noisy cover inputs.

The proposed descent-plus-bottom-cover evaluator uses completion descriptors
publicly. Its security proof must include those descriptors in the published
joint view, although the preceding full-cover proof treats completion coins
as private reduction randomness. The exact public entry/exit phase formulas
are useful, but do not establish that joint distribution automatically.

Coset-cover source assembly, its secret completion law, and the final public
transcript reduction also require explicit instantiation before claiming
security for that redesign. None changes the fixed-mask CMAS status for the
current scalar implementation.
