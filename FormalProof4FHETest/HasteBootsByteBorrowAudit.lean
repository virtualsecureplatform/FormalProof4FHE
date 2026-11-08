module
import all FormalProof4FHE.HasteBoots.NativeByteBorrow

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.Mode' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.Mode

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.Lease' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.Lease

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.State' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.State

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.empty' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.empty

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.lookup' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.lookup

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.Overlap' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.Overlap

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.Compatible' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.Compatible

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.ancestor' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.ancestor

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.rawAllowed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.rawAllowed

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.throughAllowed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.throughAllowed

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.parentAllowed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.parentAllowed

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.borrow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.borrow

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.endBorrow' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.endBorrow

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.rawRead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.rawRead

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.rawWrite' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.rawWrite

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.read

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.write' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.write

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.allocate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.allocate

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.deallocate' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.deallocate

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.lookup_selected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.lookup_selected

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.overlap_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.overlap_symm

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.empty_no_overlap' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.empty_no_overlap

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.rawAllowed_selected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.rawAllowed_selected

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.raw_exclusive_no_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.raw_exclusive_no_overlap

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.through_selected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.through_selected

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.borrow_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.borrow_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.borrow_geometry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.borrow_geometry

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.root_exclusive_separated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.root_exclusive_separated

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.parent_checked' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.parent_checked

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.shared_parent_no_upgrade' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.shared_parent_no_upgrade

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.lookup_filtered_tag' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.lookup_filtered_tag

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.endBorrow_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.endBorrow_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.endBorrow_no_children' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.endBorrow_no_children

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.ended_read_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.ended_read_rejected

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.ended_write_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.ended_write_rejected

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.rawWrite_success' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.rawWrite_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.write_success' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.write_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.read_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.read_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.read_exact_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.read_exact_length

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.write_changes_memory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.write_changes_memory

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.deallocate_success' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.deallocate_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.deallocate_no_borrow_overlap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.deallocate_no_borrow_overlap

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.deallocate_removes_allocation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.deallocate_removes_allocation

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.allocate_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.allocate_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.Within' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.Within

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.LedgerValid' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.LedgerValid

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.WellFormed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.WellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.empty_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.empty_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.ledger_transport' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.ledger_transport

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.borrow_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.borrow_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.endBorrow_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.endBorrow_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.rawWrite_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.rawWrite_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.write_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.write_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.allocate_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.allocate_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.deallocate_wellFormed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.deallocate_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.Step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.Step

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.Reachable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.Reachable

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.step_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.step_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.reachable_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.reachable_wellFormed

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.missing_read' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.missing_read

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.missing_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.missing_write

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.rawRead_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.rawRead_success

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.rawRead_exclusive_conflict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.rawRead_exclusive_conflict

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.rawWrite_conflict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.rawWrite_conflict

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.deallocate_conflict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.deallocate_conflict

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.through_exclusive_unrelated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.through_exclusive_unrelated

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.borrowSlice' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.borrowSlice

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.lookup_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.lookup_none_iff

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.endBorrow_found' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.endBorrow_found

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.step_counter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.step_counter

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.step_keeps_revoked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.step_keeps_revoked

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.Runs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.Runs

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.runs_keep_revoked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.runs_keep_revoked

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.ended_tag_never_returns' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.ended_tag_never_returns

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.ParentPath' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.ParentPath

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.ancestor_sound' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.ancestor_sound

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.parent_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.parent_before

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.parentPath_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.parentPath_strict

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.ancestor_irreflexive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.ancestor_irreflexive

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.ancestor_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.ancestor_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeByteBorrow.ancestor_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeByteBorrow.ancestor_iff
