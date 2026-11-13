module
import all FormalProof4FHE.HasteBoots.RetainedPaddedExtractionProbability
import all FormalProof4FHE.HasteBoots.RetainedPaddedExtractionNativeBound
import all FormalProof4FHE.HasteBoots.RetainedPaddedExtractionJointBound
import all FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtractionBound
import all FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtractionNativeJointBound

/-- info: 'FormalProof4FHE.HasteBoots.RetainedPaddedExtractionProbability.selected_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RetainedPaddedExtractionProbability.selected_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.RetainedPaddedExtractionNativeBound.safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RetainedPaddedExtractionNativeBound.safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.RetainedPaddedExtractionJointBound.safe_joint_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RetainedPaddedExtractionJointBound.safe_joint_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtractionBound.safe_extraction_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtractionBound.safe_extraction_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtractionNativeJointBound.native_safe_joint_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtractionNativeJointBound.native_safe_joint_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtractionNativeJointBound.native_risk_or_bad_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtractionNativeJointBound.native_risk_or_bad_bound
