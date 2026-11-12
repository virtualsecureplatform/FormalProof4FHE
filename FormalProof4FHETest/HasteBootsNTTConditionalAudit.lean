module
import all FormalProof4FHE.HasteBoots.CommittedPrefixSafeBound
import all FormalProof4FHE.HasteBoots.CommittedBatchSafeBound
import all FormalProof4FHE.HasteBoots.NTTConditionalSoundness

/-- info: 'FormalProof4FHE.HasteBoots.CommittedPrefixSafeBound.event_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CommittedPrefixSafeBound.event_bound

/-- info: 'FormalProof4FHE.HasteBoots.CommittedBatchSafeBound.soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CommittedBatchSafeBound.soundness

/-- info: 'FormalProof4FHE.HasteBoots.NTTConditionalSoundness.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTConditionalSoundness.witness

/-- info: 'FormalProof4FHE.HasteBoots.NTTConditionalSoundness.fresh_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTConditionalSoundness.fresh_recorded

/-- info: 'FormalProof4FHE.HasteBoots.NTTConditionalSoundness.audited_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTConditionalSoundness.audited_witness

/-- info: 'FormalProof4FHE.HasteBoots.NTTConditionalSoundness.truth_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTConditionalSoundness.truth_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.NTTConditionalSoundness.opening_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTConditionalSoundness.opening_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.NTTConditionalSoundness.original_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTConditionalSoundness.original_safe_bound
