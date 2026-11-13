module
import all FormalProof4FHE.HasteBoots.DependentStageSupport
import all FormalProof4FHE.HasteBoots.CheckpointHistoryChain
import all FormalProof4FHE.HasteBoots.RetainedComparisonHistory
import all FormalProof4FHE.HasteBoots.RetainedExtractionHistory
import all FormalProof4FHE.HasteBoots.PackedPBSKeySwitchReconstructionSupport
import all FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisonsHistory
import all FormalProof4FHE.HasteBoots.PackedPBSKeySwitchFinalHistory

/-- info: 'FormalProof4FHE.HasteBoots.DependentStageSupport.predecessor_supported_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DependentStageSupport.predecessor_supported_bind

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointHistoryChain.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CheckpointHistoryChain.trans

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointHistoryChain.append_retains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CheckpointHistoryChain.append_retains

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointHistoryChain.family_recorded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CheckpointHistoryChain.family_recorded

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointHistoryChain.families_of_retains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CheckpointHistoryChain.families_of_retains

/-- info: 'FormalProof4FHE.HasteBoots.CheckpointHistoryChain.Retains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CheckpointHistoryChain.Retains

/-- info: 'FormalProof4FHE.HasteBoots.RetainedComparisonHistory.predecessor_supported_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RetainedComparisonHistory.predecessor_supported_bind

/-- info: 'FormalProof4FHE.HasteBoots.RetainedComparisonHistory.propagate_retains_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RetainedComparisonHistory.propagate_retains_bind

/-- info: 'FormalProof4FHE.HasteBoots.RetainedExtractionHistory.predecessor_supported_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RetainedExtractionHistory.predecessor_supported_bind

/-- info: 'FormalProof4FHE.HasteBoots.RetainedExtractionHistory.propagate_retains_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RetainedExtractionHistory.propagate_retains_bind

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchReconstruction.predecessor_supported_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchReconstruction.predecessor_supported_witness

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchReconstruction.ntt_retains_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchReconstruction.ntt_retains_witness

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisons.predecessor_supported_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisons.predecessor_supported_witness

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisons.ntt_retains_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisons.ntt_retains_witness

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.ntt_retains_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.ntt_retains_witness

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.ntt_family_retains_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.ntt_family_retains_witness
