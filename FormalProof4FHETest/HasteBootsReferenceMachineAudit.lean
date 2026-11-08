module
import all FormalProof4FHE.HasteBoots.NativeReferenceMachine

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Reference' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Reference

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.State' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.State

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.ledger' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.ledger

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.empty' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.empty

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access.layout' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access.layout

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access.mode' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access.mode

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Op' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Op

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.rawPermission' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.rawPermission

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.rawPermissions' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.rawPermissions

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.setPointers' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.setPointers

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.grant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.grant

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.prepare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.prepare

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.perform' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.perform

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.access' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.access

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.execute' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.execute

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.run

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Reachable

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.WellFormed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.WellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.prepare_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.prepare_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.perform_projects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.perform_projects

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.pointer_runs_trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.pointer_runs_trans

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.grant_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.grant_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.access_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.access_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.access_projects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.access_projects

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.execute_projects' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.execute_projects

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_pointers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_pointers

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.SameAuthority' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.SameAuthority

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.perform_authority' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.perform_authority

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.AuthorityEffect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.AuthorityEffect

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.execute_authority' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.execute_authority

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.empty_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.empty_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.stable_wellFormed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.stable_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.grant_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.grant_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.end_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.end_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.execute_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.execute_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.execute_counter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.execute_counter

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.execute_keeps_revoked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.execute_keeps_revoked

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Runs

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.runs_counter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.runs_counter

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.runs_keep_revoked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.runs_keep_revoked

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.missing_access' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.missing_access

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.reference_born_before_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.reference_born_before_counter

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.access_binding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.access_binding

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.end_reference_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.end_reference_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.ended_reference_never_access' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.ended_reference_never_access

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.runs_trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.runs_trans

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_birth_borrow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_birth_borrow

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_reference_borrow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_reference_borrow

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.run_reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.run_reachable

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.run_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.run_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.raw_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.raw_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.raw_permission_selected' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.raw_permission_selected

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.raw_free_no_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.raw_free_no_overlap

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_unique_birth_tags' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_unique_birth_tags

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.run_reference_borrow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.run_reference_borrow

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_pointer_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_pointer_origin

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.pointer_execute_keeps_register' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.pointer_execute_keeps_register

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.pointer_runs_keep_register' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.pointer_runs_keep_register

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_lease_registered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.reachable_lease_registered

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.prepare_of_registered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.prepare_of_registered

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.prepare_resident_lease' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.prepare_resident_lease

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Reference.mk' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Reference.mk

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Reference.tag' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Reference.tag

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.mk' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.mk

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.pointers' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.pointers

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.nextTag' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.nextTag

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.leases' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.leases

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.references' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.references

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.births' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.births

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.outputs' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.State.outputs

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access.read' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access.read

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access.writeBytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access.writeBytes

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access.loadPointer' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access.loadPointer

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access.storePointer' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Access.storePointer

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Op.raw' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Op.raw

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Op.borrow' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Op.borrow

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Op.reborrow' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Op.reborrow

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Op.endBorrow' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Op.endBorrow

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Op.access' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Op.access

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.AuthorityEffect.stable' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.AuthorityEffect.stable

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.AuthorityEffect.granted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.AuthorityEffect.granted

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.AuthorityEffect.ended' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.AuthorityEffect.ended

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Reachable.empty' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Reachable.empty

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Reachable.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Reachable.step

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Runs.refl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Runs.refl

/-- info: 'FormalProof4FHE.HasteBoots.NativeReferenceMachine.Runs.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeReferenceMachine.Runs.step
