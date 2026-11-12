module
import all FormalProof4FHE.HasteBoots.AmbientNTT
import all FormalProof4FHE.HasteBoots.AmbientNTTSequence
import all FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness
import all FormalProof4FHE.HasteBoots.AmbientMonomialNTT

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTT.source_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTT.source_evaluation

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTT.accepted_implies_risks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTT.accepted_implies_risks

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTT.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTT.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTT.fresh_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTT.fresh_recorded

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTT.audited_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTT.audited_witness

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTT.retains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTT.retains

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTT.bad_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTT.bad_persistent

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTT.fresh_risk_implies_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTT.fresh_risk_implies_original

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTT.truth_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTT.truth_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTT.opening_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTT.opening_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTT.original_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTT.original_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTTSequence.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTTSequence.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.child_audited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.child_audited

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.safe_union_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.safe_union_bound

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.bad_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.bad_persistent

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.child_bad_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.child_bad_persistent

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.accepted_indices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.accepted_indices

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.retained_child_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.retained_child_support

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.retains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.retains

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.audited_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.audited_witness

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.original_safe_le_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.original_safe_le_local

/-- info: 'FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.derived_original_safe_union_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientNTTSequenceSoundness.derived_original_safe_union_bound

/-- info: 'FormalProof4FHE.HasteBoots.AmbientMonomialNTT.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientMonomialNTT.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.AmbientMonomialNTT.child_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientMonomialNTT.child_roots

/-- info: 'FormalProof4FHE.HasteBoots.AmbientMonomialNTT.retained_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientMonomialNTT.retained_roots

/-- info: 'FormalProof4FHE.HasteBoots.AmbientMonomialNTT.original_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientMonomialNTT.original_safe_bound
