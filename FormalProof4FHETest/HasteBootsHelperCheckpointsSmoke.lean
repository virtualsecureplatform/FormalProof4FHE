module

import all FormalProof4FHE.HasteBoots.NativeProgramComposition
import all FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints
import all FormalProof4FHE.HasteBoots.NativeSharedLookupChildCheckpoints
import all FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpointExecution

/-- info: 'FormalProof4FHE.HasteBoots.NativeProgramComposition.bind_assoc' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeProgramComposition.bind_assoc

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints.native_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints.native_eq

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints.gate_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints.gate_spec

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints.root_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints.root_mem

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints.native_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints.native_replay

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints.recorded_helpers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupHelperCheckpoints.recorded_helpers

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupChildCheckpoints.native_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupChildCheckpoints.native_eq

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupChildCheckpoints.native_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupChildCheckpoints.native_replay

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupChildCheckpoints.recorded_helpers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupChildCheckpoints.recorded_helpers

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpointExecution.origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpointExecution.origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpointExecution.native_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpointExecution.native_replay

/-- info: 'FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpointExecution.recorded_families' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeSharedLookupCheckpointExecution.recorded_families
