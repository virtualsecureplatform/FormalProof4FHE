module
import all FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons
import all FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonProbability
import all FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonSoundness

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.shared_program' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.shared_program

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.project_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.project_before

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.reached_comparisons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.reached_comparisons

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.comparison_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.comparison_sources

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.comparison_digit_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.comparison_digit_roots

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.retains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.retains

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.bad_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.bad_persistent

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.audited_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.audited_witness

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.final_bad_le_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons.final_bad_le_charge

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonProbability.earlier_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonProbability.earlier_event_le

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonProbability.earlier_safe_event_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonProbability.earlier_safe_event_le

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonProbability.safe_comparison_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonProbability.safe_comparison_bound

/-- info: 'FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonSoundness.original_false_comparison_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonSoundness.original_false_comparison_bound
