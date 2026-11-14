module
import all FormalProof4FHE.HasteBoots.DependentStageContinuationProjection

/-- info: 'FormalProof4FHE.HasteBoots.DependentStageContinuationProjection.eraseOutcome' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DependentStageContinuationProjection.eraseOutcome

/-- info: 'FormalProof4FHE.HasteBoots.DependentStageContinuationProjection.program' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DependentStageContinuationProjection.program

/-- info: 'FormalProof4FHE.HasteBoots.DependentStageContinuationProjection.project_finish' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DependentStageContinuationProjection.project_finish

/-- info: 'FormalProof4FHE.HasteBoots.DependentStageContinuationProjection.project_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DependentStageContinuationProjection.project_bind

/-- info: 'FormalProof4FHE.HasteBoots.DependentStageContinuationProjection.terminal_event_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.DependentStageContinuationProjection.terminal_event_eq
