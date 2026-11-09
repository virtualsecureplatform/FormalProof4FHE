module
import FormalProof4FHE.HasteBoots.NativeBorrowFrontier

/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.Contained' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.Contained

/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.ExclusiveFrontier' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.ExclusiveFrontier

/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.disjoint_subrange' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.disjoint_subrange

/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.singleton_frontier' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.singleton_frontier

/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.frontier_transport' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.frontier_transport

/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.through_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.through_allowed

/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.parent_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.parent_allowed

/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.path_cons_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.path_cons_fresh

/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.borrow_frontier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.borrow_frontier

/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.borrow_subrange' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.borrow_subrange

/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.grant_subrange' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.grant_subrange

/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.index_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.index_complete


/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.grant_initialized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.grant_initialized

/-- info: 'FormalProof4FHE.HasteBoots.NativeBorrowFrontier.vec_header_grant_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeBorrowFrontier.vec_header_grant_complete
