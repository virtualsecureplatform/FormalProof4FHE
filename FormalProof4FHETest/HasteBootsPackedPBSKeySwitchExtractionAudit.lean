module
import all FormalProof4FHE.HasteBoots.RetainedPaddedExtraction
import all FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction

/-- info: 'FormalProof4FHE.HasteBoots.RetainedPaddedExtraction.select' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RetainedPaddedExtraction.select

/-- info: 'FormalProof4FHE.HasteBoots.RetainedPaddedExtraction.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RetainedPaddedExtraction.reached

/-- info: 'FormalProof4FHE.HasteBoots.RetainedPaddedExtraction.reached_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RetainedPaddedExtraction.reached_bind

/-- info: 'FormalProof4FHE.HasteBoots.RetainedPaddedExtraction.earlier_safe_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RetainedPaddedExtraction.earlier_safe_event_le

/-- info: 'FormalProof4FHE.HasteBoots.RetainedPaddedExtraction.audited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RetainedPaddedExtraction.audited

/-- info: 'FormalProof4FHE.HasteBoots.RetainedPaddedExtraction.audited_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.RetainedPaddedExtraction.audited_bind

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.get

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.get_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.get_spec

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.endpoint

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.witness

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.finalState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.finalState

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.audited_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction.audited_witness
