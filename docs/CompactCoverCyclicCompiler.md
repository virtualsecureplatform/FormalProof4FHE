# Compact-cover cyclic compiler

`CompactCoverCyclicCompiler.lean` formalizes the new derivation in
`sketch/proof-compact-cover.md`.

The central normal form represents every cross-frontier message in its target
frontier as

```text
messageConstant - messageCoefficient*embeddedWitness.
```

The target secret has the same form with a unit coefficient. A fresh ordinary
source row can therefore absorb the message coefficient and target pivot by
one affine mask permutation.

Lean proves:

- concrete regular-frontier relabeling is a ring homomorphism;
- relabeling is covariant with the common embedded base witness;
- admissible maps carry affine witness decompositions exactly;
- arbitrary public linear combinations remain witness-affine;
- the cyclic compiler has the claimed real-row phase;
- the compiler row and complete row-family maps have explicit inverses;
- complete uniform endpoints are preserved exactly;
- restriction, branch creation, duplication, alignment, and cyclic return use
  the same admissible-map interface;
- the multi-source gadget transition has the exact scheduled output phase and
  explicit digit-weighted transition error; and
- pivot failure and challenge-masking terms compose with the ordinary-source
  advantage exactly as stated.

The compiler permits cycles because every frontier pivot and transition row is
generated jointly from fresh rows sharing one hidden Binary-NTT witness. The
final return to the advertised key is not assumed separately.

The remaining degree-65536 work is concrete instantiation:

1. encode the complete extracted Magma gate manifest as admissible maps and
   public affine combinations;
2. insert gadget bases, RNS levels, rounding rules, and error widths into the
   native recurrence; and
3. verify strict refresh contraction for a selected parameter set.

These are schedule validation and parameter work rather than a remaining
circular-security theorem. Independent review of the new multi-frontier
compiler remains appropriate.

For the scalar-only payload, `CompactCoverBGV65536Instantiation.lean` records
both the non-contraction boundary of bare phase lifting and the corrected
endpoint. The genuine construction uses a one-limb-to-23-limb phase lift, a
16-stage normalized constant trace with two level drops, bounded carry
removal, and exact division by `p`. The deterministic certificate also closes
one multiplication between bootstraps. This path needs neither packed
coefficient-to-slot maps nor the width-368 frontier.

`CompactCoverBGVScalarSecurity.lean` indexes the two phase-lift rows and the
sixteen groups of trace rows as one 370-row directory, appends any finite batch
of symmetric encryption queries, and proves that the left/right advantage is
bounded by two joint Binary-NTT source advantages. The theorem never splits
the directory into circular-security marginals.

`CompactCoverBGVAdaptiveSecurity.lean` upgrades that finite table to the usual
query-bounded symmetric encryption oracle. Message pairs may be selected after
the evaluation directory and previous answers are known. The eager table and
online oracle are distributionally identical, and the uniform endpoint wins
with probability exactly one half.

Principal declarations:

- `AdmissibleMap`
- `frontierRelabel`
- `frontierRelabelAdmissible`
- `WitnessAffine`
- `affineCombination_value`
- `mapWitnessAffine_value`
- `compiler_phase`
- `compilerRow_bijective`
- `compilerBatch_uniform_evalDist`
- `transitionCiphertext_phase`
- `JointReductionCertificate.target_le_source_add_failure`
- `indCpa_le_source_add_failure_add_masking`
