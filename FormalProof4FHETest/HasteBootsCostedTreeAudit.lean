module
import FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability

/-- info: 'FormalProof4FHE.HasteBoots.StoredDigestView.view_store' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.StoredDigestView.view_store

/-- info: 'FormalProof4FHE.HasteBoots.StoredDigestView.store_view' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.StoredDigestView.store_view

/-- info: 'FormalProof4FHE.HasteBoots.StoredDigestView.fromVector_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.StoredDigestView.fromVector_value

/-- info: 'FormalProof4FHE.HasteBoots.StoredDigestView.view_fromVector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.StoredDigestView.view_fromVector

/-- info: 'FormalProof4FHE.HasteBoots.StoredDigestView.fromVector_cost' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.StoredDigestView.fromVector_cost

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleTree.absent_value' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleTree.absent_value

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleTree.absent_cost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleTree.absent_cost

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleTree.tree' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleTree.tree

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleTree.tree_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleTree.tree_value

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleTree.tree_value_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleTree.tree_value_raw

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleTree.tree_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleTree.tree_cost

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleTree.prepareTree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleTree.prepareTree

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleTree.prepareTree_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleTree.prepareTree_value

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleTree.prepareTree_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleTree.prepareTree_cost

/-- info: 'FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability.measuredTree_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability.measuredTree_eq

/-- info: 'FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability.cachedChildren_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability.cachedChildren_eq

/-- info: 'FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability.reconstruct_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability.reconstruct_get
