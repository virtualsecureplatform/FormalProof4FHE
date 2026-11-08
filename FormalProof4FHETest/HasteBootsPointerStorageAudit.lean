module
import all FormalProof4FHE.HasteBoots.NativePointerStorage

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerStorage.readdress_provenance' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerStorage.readdress_provenance

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerStorage.readdress_original' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerStorage.readdress_original

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerStorage.pointer_fields' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerStorage.pointer_fields

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerStorage.cell_nonnull' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerStorage.cell_nonnull

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerStorage.read_head' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerStorage.read_head

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerStorage.read_without_provenance' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerStorage.read_without_provenance

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerStorage.read_null' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerStorage.read_null

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerStorage.read_selected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerStorage.read_selected

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerStorage.read_nonnull' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerStorage.read_nonnull

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerStorage.read_retired' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerStorage.read_retired

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerStorage.read_retire_other' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerStorage.read_retire_other

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerStorage.reused_address_stale' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerStorage.reused_address_stale

/-- info: 'FormalProof4FHE.HasteBoots.NativePointerStorage.reused_address_fresh' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativePointerStorage.reused_address_fresh
