# Associated-type equality controls and recursive counterexamples

`control.rs` exercises an abstract associated root type, an explicit `Root=u64`
constraint and a second conversion whose root equals the first output type.
The three extracted functions and five kernel theorems check these equalities
and preserve success/failure composition. These are compiler controls, not native
field or cryptographic assumptions.

`cycle.rs` reduces the NTT interface problem to two mutually dependent traits.
`equality-cycle.rs` also retains the plan-equals-self constraint. Both are valid
Rust and remain unsupported. Aeneas can emit errors and truncated output while
returning zero; the gate checks logs and complete namespace output as well as
exit status, so neither case becomes an accepted proof.

The controls are regenerated and checked by
`scripts/extract-hasteboots-metadata-mono`. No trait clause or associated-type
constraint is manually removed, no LLBC is rewritten, and no associated type is
replaced by an axiom.
