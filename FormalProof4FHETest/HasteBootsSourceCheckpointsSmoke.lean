module

public import FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints
import all FormalProof4FHE.HasteBoots.NativeCheckpointBoundary
import all FormalProof4FHE.HasteBoots.NativeCheckpointProgram
import all FormalProof4FHE.HasteBoots.RecordRoots

@[expose] public section

open FormalProof4FHE.HasteBoots
open OracleSpec OracleComp

namespace SourceCheckpointTest

-- Test interpretation for checking unchanged native hashes and ghost-record
-- order. Canonical cache/snapshot soundness is covered by the support proofs.
inductive Event where
  | hash (input digest : InputIndexedOracle.Input)
  | record (tag : ℕ) (root : InputIndexedOracle.Input)
  deriving DecidableEq

noncomputable def handler {Cfg : Type} (index : Cfg → ℕ) (world : InputIndexedOracle.World) :
    QueryImpl (CheckpointExecution.Spec unifSpec Cfg InputIndexedOracle.Input NativeRootMessage.Digest)
      (WriterT (List Event) Id) := fun request => match request with
  | .inl size => pure ⟨0,by omega⟩
  | .inr (.inl input) =>
    let answer := InputIndexedOracle.sha512 world input
    WriterT.mk (answer,[.hash input (List.ofFn answer)])
  | .inr (.inr (tag,root)) => WriterT.mk ((),[.record (index tag) (List.ofFn root)])

end SourceCheckpointTest

/-- info: 'FormalProof4FHE.HasteBoots.NativeHashPrefix.bind_hashOnly' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHashPrefix.bind_hashOnly

/-- info: 'FormalProof4FHE.HasteBoots.NativeHashPrefix.compile_independent' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHashPrefix.compile_independent

/-- info: 'FormalProof4FHE.HasteBoots.NativeHashPrefix.observations_hashes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeHashPrefix.observations_hashes

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.context' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.context

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.contexts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.contexts

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.frame

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.step

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.loop

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.preflight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.preflight

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.register' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.register

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHashPrefix.prepare

/-- info: 'FormalProof4FHE.HasteBoots.NativeCheckpointBoundary.freeze_independent' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeCheckpointBoundary.freeze_independent

/-- info: 'FormalProof4FHE.HasteBoots.NativeCheckpointBoundary.freeze_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeCheckpointBoundary.freeze_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeCheckpointBoundary.freeze_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeCheckpointBoundary.freeze_recorded

/-- info: 'FormalProof4FHE.HasteBoots.NativeCheckpointBoundary.program_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeCheckpointBoundary.program_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeCheckpointBoundary.native_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeCheckpointBoundary.native_replay

/-- info: 'FormalProof4FHE.HasteBoots.NativeCheckpointBoundary.program_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeCheckpointBoundary.program_recorded

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.roots_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.roots_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.root_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.root_mem

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.tagged_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.tagged_mem

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.native_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.native_eq

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.freeze_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.freeze_independent

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.native_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.native_replay

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.recorded_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpoints.recorded_sources
