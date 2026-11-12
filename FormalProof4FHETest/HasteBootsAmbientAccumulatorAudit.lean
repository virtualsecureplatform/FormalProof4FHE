module
import all FormalProof4FHE.HasteBoots.AmbientDependentBatchOpening
import all FormalProof4FHE.HasteBoots.PackedAccumulatorOracle
import all FormalProof4FHE.HasteBoots.AmbientAccumulator

/-- info: 'FormalProof4FHE.HasteBoots.AmbientDependentBatchOpening.soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientDependentBatchOpening.soundness

/-- info: 'FormalProof4FHE.HasteBoots.PackedAccumulatorOracle.truthful_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedAccumulatorOracle.truthful_check

/-- info: 'FormalProof4FHE.HasteBoots.PackedAccumulatorOracle.values_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedAccumulatorOracle.values_eq

/-- info: 'FormalProof4FHE.HasteBoots.PackedAccumulatorOracle.program_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedAccumulatorOracle.program_checked

/-- info: 'FormalProof4FHE.HasteBoots.PackedAccumulatorOracle.truthful_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PackedAccumulatorOracle.truthful_bound

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.fold_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.fold_cast

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.factors_complete' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.factors_complete

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.sources_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.sources_context

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.source_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.source_tables

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.fold_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.fold_table

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.values_truthful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.values_truthful

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.witness_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.witness_checked

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.retains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.retains

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.audited_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.audited_witness

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.bad_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.bad_persistent

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.fresh_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.fresh_recorded

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.truth_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.truth_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.opening_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.opening_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.AmbientAccumulator.false_acceptance_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientAccumulator.false_acceptance_safe_bound
