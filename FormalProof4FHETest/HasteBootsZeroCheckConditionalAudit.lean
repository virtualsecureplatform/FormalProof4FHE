module
import all FormalProof4FHE.HasteBoots.CommittedStoppingSafeBound
import all FormalProof4FHE.HasteBoots.CommittedOpeningSafeBound
import all FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness
import all FormalProof4FHE.HasteBoots.HadamardConditionalSoundness

/-- info: 'FormalProof4FHE.HasteBoots.CommittedStoppingSafeBound.soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CommittedStoppingSafeBound.soundness

/-- info: 'FormalProof4FHE.HasteBoots.CommittedOpeningSafeBound.soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CommittedOpeningSafeBound.soundness

/-- info: 'FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.witness

/-- info: 'FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.accepted_implies_risks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.accepted_implies_risks

/-- info: 'FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.truth_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.truth_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.opening_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.opening_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.fresh_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.fresh_recorded

/-- info: 'FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.audited_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.audited_witness

/-- info: 'FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.original_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ZeroCheckConditionalSoundness.original_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.HadamardConditionalSoundness.native_original_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HadamardConditionalSoundness.native_original_safe_bound
