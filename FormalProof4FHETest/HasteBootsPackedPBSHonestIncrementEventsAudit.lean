module
import all FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents.ExecutionResult' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents.ExecutionResult

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents.CorrectOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents.CorrectOutput

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents.AcceptedFalse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents.AcceptedFalse

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents.TailFailure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents.TailFailure

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents.accepted_false_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents.accepted_false_event_le

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents.accepted_false_implies_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents.accepted_false_implies_failure
