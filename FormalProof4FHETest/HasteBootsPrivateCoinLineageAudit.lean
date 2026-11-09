module
import FormalProof4FHE.HasteBoots.PrivateCoinByteFailure

/-- info: 'FormalProof4FHE.HasteBoots.InstructionClock.single_log_length' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.InstructionClock.single_log_length

/-- info: 'FormalProof4FHE.HasteBoots.InstructionClock.take_resume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.InstructionClock.take_resume

/-- info: 'FormalProof4FHE.HasteBoots.InstructionClock.history_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.InstructionClock.history_replay

/-- info: 'FormalProof4FHE.HasteBoots.InstructionClock.history_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.InstructionClock.history_zero

/-- info: 'FormalProof4FHE.HasteBoots.InstructionClock.history_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.InstructionClock.history_resume

/-- info: 'FormalProof4FHE.HasteBoots.InstructionClock.history_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.InstructionClock.history_prefix

/-- info: 'FormalProof4FHE.HasteBoots.InstructionClock.history_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.InstructionClock.history_succ

/-- info: 'FormalProof4FHE.HasteBoots.InstructionClock.first_flip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.InstructionClock.first_flip

/-- info: 'FormalProof4FHE.HasteBoots.InstructionClock.recover_at_flip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.InstructionClock.recover_at_flip

/-- info: 'FormalProof4FHE.HasteBoots.InstructionClock.coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.InstructionClock.coverage

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteRequest.lift_exact' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteRequest.lift_exact

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteRequest.command_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteRequest.command_exact

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteRequest.take_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteRequest.take_exact

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteRequest.tick_log_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteRequest.tick_log_length

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteRequest.firstRead_of_tick' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteRequest.firstRead_of_tick

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteLineage.history_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteLineage.history_run

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteLineage.history_replay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteLineage.history_replay

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteLineage.scalar_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteLineage.scalar_run

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteLineage.coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteLineage.coverage

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteNativeCoverage.accepted_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteNativeCoverage.accepted_coverage

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteFailure.witness_iff_analysis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteFailure.witness_iff_analysis

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteFailure.failure_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteFailure.failure_covered

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteFailure.finite_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteFailure.finite_measurable

/-- info: 'FormalProof4FHE.HasteBoots.PrivateCoinByteFailure.failure_measurable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PrivateCoinByteFailure.failure_measurable
