module
import all FormalProof4FHE.HasteBoots.PackedPBSFirstHalfJointBound
import all FormalProof4FHE.HasteBoots.PackedPBSDecompositionJointBound
import all FormalProof4FHE.HasteBoots.PackedPBSSecondHalfJointBound
import all FormalProof4FHE.HasteBoots.PackedPBSBothHalvesJointBound


/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSFirstHalfJointBound.native_safe_joint_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSFirstHalfJointBound.native_safe_joint_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSDecompositionJointBound.safe_joint_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSDecompositionJointBound.safe_joint_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSDecompositionJointBound.risk_or_bad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSDecompositionJointBound.risk_or_bad_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondHalfJointBound.native_risk_or_bad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondHalfJointBound.native_risk_or_bad_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSBothHalvesJointBound.native_risk_or_bad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSBothHalvesJointBound.native_risk_or_bad_bound
