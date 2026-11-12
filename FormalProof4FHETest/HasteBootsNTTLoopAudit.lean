module
import all FormalProof4FHE.HasteBoots.NTTSequence
import all FormalProof4FHE.HasteBoots.NTTSequenceSoundness
import all FormalProof4FHE.HasteBoots.NTTLoopProbability

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequence.ActualResult' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequence.ActualResult

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequence.Child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequence.Child

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequence.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequence.step

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequence.program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequence.program

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequence.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequence.witness

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequence.erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequence.erase

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequence.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequence.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequenceSoundness.Trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequenceSoundness.Trace

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequenceSoundness.LocalSafeRisk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequenceSoundness.LocalSafeRisk

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequenceSoundness.AnySafeRisk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequenceSoundness.AnySafeRisk

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequenceSoundness.child_audited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequenceSoundness.child_audited

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequenceSoundness.safe_union_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequenceSoundness.safe_union_bound

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequenceSoundness.bad_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequenceSoundness.bad_persistent

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequenceSoundness.child_bad_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequenceSoundness.child_bad_persistent

/-- info: 'FormalProof4FHE.HasteBoots.NTTSequenceSoundness.accepted_indices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTSequenceSoundness.accepted_indices

/-- info: 'FormalProof4FHE.HasteBoots.NTTLoopProbability.AnyRisk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTLoopProbability.AnyRisk

/-- info: 'FormalProof4FHE.HasteBoots.NTTLoopProbability.original_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTLoopProbability.original_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.NTTLoopProbability.native_original_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NTTLoopProbability.native_original_risk_bound
