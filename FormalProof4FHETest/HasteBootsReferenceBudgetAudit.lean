module
import all FormalProof4FHETest.HasteBootsReferenceBudgetSmoke

/-- info: 'FormalProof4FHE.HasteBoots.ProgramObservationClock.complete_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ProgramObservationClock.complete_length
/-- info: 'FormalProof4FHE.HasteBoots.ProgramObservationClock.request_after_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ProgramObservationClock.request_after_length
/-- info: 'FormalProof4FHE.HasteBoots.ProgramObservationClock.score_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ProgramObservationClock.score_sum
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.parent_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.parent_card
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.context_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.context_bytes
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.receipt_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.receipt_bytes
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.parent_risk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.parent_risk
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.context_risk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.context_risk
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.fresh_risk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.fresh_risk
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.collision_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.collision_risk
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.risk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.risk
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.risk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.risk_le
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.lowRisk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.lowRisk
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.rate
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.lowRisk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.lowRisk_le
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.lowRisk_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.lowRisk_absent
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.totalLowCharge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.totalLowCharge
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.total_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.total_le_log
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.closed_charge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.closed_charge
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.private_charge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.private_charge
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.privateLifetimeCharge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.privateLifetimeCharge
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.private_lifetime_charge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.private_lifetime_charge
/-- info: 'FormalProof4FHE.HasteBoots.ReferenceRiskBudget.private_expected_charge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceRiskBudget.private_expected_charge
/-- info: '_private.FormalProof4FHETest.HasteBootsReferenceBudgetSmoke.0.FormalProof4FHE.HasteBoots.ReferenceBudgetSmoke.naming_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceBudgetSmoke.naming_bytes
/-- info: '_private.FormalProof4FHETest.HasteBootsReferenceBudgetSmoke.0.FormalProof4FHE.HasteBoots.ReferenceBudgetSmoke.zero_threshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceBudgetSmoke.zero_threshold
/-- info: '_private.FormalProof4FHETest.HasteBootsReferenceBudgetSmoke.0.FormalProof4FHE.HasteBoots.ReferenceBudgetSmoke.completed_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ReferenceBudgetSmoke.completed_suffix
