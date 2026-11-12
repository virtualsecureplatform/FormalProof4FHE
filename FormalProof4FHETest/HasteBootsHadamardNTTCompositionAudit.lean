module
import all FormalProof4FHE.HasteBoots.ShortCircuitStageHistory
import all FormalProof4FHE.HasteBoots.HadamardNTTComposition

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitStageHistory.program' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ShortCircuitStageHistory.program

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitStageHistory.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ShortCircuitStageHistory.witness

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitStageHistory.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ShortCircuitStageHistory.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitStageHistory.reached_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ShortCircuitStageHistory.reached_second

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitStageHistory.same_request_sources_eq_or_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ShortCircuitStageHistory.same_request_sources_eq_or_bad

/-- info: 'FormalProof4FHE.HasteBoots.ShortCircuitStageHistory.source_drift_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ShortCircuitStageHistory.source_drift_bound

/-- info: 'FormalProof4FHE.HasteBoots.HadamardNTTComposition.program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HadamardNTTComposition.program

/-- info: 'FormalProof4FHE.HasteBoots.HadamardNTTComposition.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HadamardNTTComposition.witness

/-- info: 'FormalProof4FHE.HasteBoots.HadamardNTTComposition.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.HadamardNTTComposition.project_witness
