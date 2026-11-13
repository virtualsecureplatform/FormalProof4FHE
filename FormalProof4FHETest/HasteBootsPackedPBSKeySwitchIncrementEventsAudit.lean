module
import all FormalProof4FHE.HasteBoots.PackedPBSKeySwitchIncrementEvents

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchIncrementEvents.ExecutionResult' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchIncrementEvents.ExecutionResult

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchIncrementEvents.CorrectOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchIncrementEvents.CorrectOutput

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchIncrementEvents.AcceptedFalse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchIncrementEvents.AcceptedFalse

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchIncrementEvents.TailFailure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchIncrementEvents.TailFailure

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchIncrementEvents.accepted_false_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchIncrementEvents.accepted_false_event_le
