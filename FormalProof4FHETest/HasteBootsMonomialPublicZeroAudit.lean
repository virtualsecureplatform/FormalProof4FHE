module
import all FormalProof4FHE.HasteBoots.AmbientSingleChecks
import all FormalProof4FHE.HasteBoots.AmbientCommittedOpeningSafeBound
import all FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck
import all FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck

/-- info: 'FormalProof4FHE.HasteBoots.AmbientSingleChecks.wrong_implies_arithmetic_or_disagreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientSingleChecks.wrong_implies_arithmetic_or_disagreement

/-- info: 'FormalProof4FHE.HasteBoots.AmbientCommittedOpeningSafeBound.step_arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientCommittedOpeningSafeBound.step_arithmetic_bound

/-- info: 'FormalProof4FHE.HasteBoots.AmbientCommittedOpeningSafeBound.soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientCommittedOpeningSafeBound.soundness

/-- info: 'FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.project_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.project_witness

/-- info: 'FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.fresh_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.fresh_recorded

/-- info: 'FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.retains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.retains

/-- info: 'FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.audited_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.audited_witness

/-- info: 'FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.bad_persistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.bad_persistent

/-- info: 'FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.fresh_risk_implies_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.fresh_risk_implies_original

/-- info: 'FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.accepted_implies_risks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.accepted_implies_risks

/-- info: 'FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.truth_risk_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.truth_risk_bound

/-- info: 'FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.opening_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.opening_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.original_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.original_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.native_original_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.AmbientPublicZeroCheck.native_original_safe_bound

/-- info: 'FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.expression_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.expression_eq

/-- info: 'FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.vanishes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.vanishes_iff

/-- info: 'FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.fold_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.fold_table

/-- info: 'FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.fold_eq_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.fold_eq_evaluate

/-- info: 'FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.public_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.public_source

/-- info: 'FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.original_vanishes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.original_vanishes_iff

/-- info: 'FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.witness_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.witness_roots

/-- info: 'FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.original_safe_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.MonomialPublicZeroCheck.original_safe_bound
