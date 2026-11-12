module
import all FormalProof4FHE.HasteBoots.CrossStageSourceCoherence

/-- info: 'FormalProof4FHE.HasteBoots.CrossStageSourceCoherence.source_trans' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CrossStageSourceCoherence.source_trans

/-- info: 'FormalProof4FHE.HasteBoots.CrossStageSourceCoherence.tables_eq_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CrossStageSourceCoherence.tables_eq_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.CrossStageSourceCoherence.ntt_hadamard_eq_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CrossStageSourceCoherence.ntt_hadamard_eq_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.CrossStageSourceCoherence.ntt_hadamard_family_eq_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CrossStageSourceCoherence.ntt_hadamard_family_eq_or_bad
