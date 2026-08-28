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

For the scalar-only payload, `CompactCoverBGV65536Instantiation.lean` gives a
smaller concrete endpoint: phase lifting from `p` to `p²`, one width-one
full-modulus transition, and exact division by `p`. This path needs neither the
packed coefficient-to-slot maps nor the width-368 frontier. Its selected
15-limb certificate and exact phase/division identities are checked, and the
matching TFHEpp test executes repeated N=65536 bootstraps.

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
