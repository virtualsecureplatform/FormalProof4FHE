module
import FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability

/-- info: 'FormalProof4FHE.HasteBoots.FixedByteReadCost.takeExact_parts' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FixedByteReadCost.takeExact_parts

/-- info: 'FormalProof4FHE.HasteBoots.FixedByteReadCost.read' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FixedByteReadCost.read

/-- info: 'FormalProof4FHE.HasteBoots.FixedByteReadCost.read_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FixedByteReadCost.read_cost

/-- info: 'FormalProof4FHE.HasteBoots.FixedByteReadCost.read_some' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FixedByteReadCost.read_some

/-- info: 'FormalProof4FHE.HasteBoots.FixedByteReadCost.ofFn_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FixedByteReadCost.ofFn_get

/-- info: 'FormalProof4FHE.HasteBoots.FixedByteReadCost.read_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.FixedByteReadCost.read_value

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleNode.read_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleNode.read_cost

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleNode.read_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleNode.read_sound

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleNode.read_as_native' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleNode.read_as_native

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleNode.decode' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleNode.decode

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleNode.decode_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleNode.decode_value

/-- info: 'FormalProof4FHE.HasteBoots.CostedMerkleNode.decode_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.CostedMerkleNode.decode_cost

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders.node' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders.node

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders.node_decode_eq_reference' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders.node_decode_eq_reference

/-- info: 'FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders.node_eq_analysis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders.node_eq_analysis

/-- info: 'FormalProof4FHE.HasteBoots.PreparedMerkleNodes.prepare_value' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PreparedMerkleNodes.prepare_value

/-- info: 'FormalProof4FHE.HasteBoots.PreparedMerkleNodes.prepare_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PreparedMerkleNodes.prepare_cost

/-- info: 'FormalProof4FHE.HasteBoots.PreparedMerkleNodes.lookup_value' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PreparedMerkleNodes.lookup_value

/-- info: 'FormalProof4FHE.HasteBoots.PreparedMerkleNodes.lookup_head_match' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PreparedMerkleNodes.lookup_head_match

/-- info: 'FormalProof4FHE.HasteBoots.PreparedMerkleNodes.lookup_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PreparedMerkleNodes.lookup_cost

/-- info: 'FormalProof4FHE.HasteBoots.PreparedMerkleNodes.resolve_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PreparedMerkleNodes.resolve_cost

/-- info: 'FormalProof4FHE.HasteBoots.PreparedMerkleNodes.lookup_prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PreparedMerkleNodes.lookup_prepare

/-- info: 'FormalProof4FHE.HasteBoots.PreparedMerkleNodes.lookup_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PreparedMerkleNodes.lookup_raw

/-- info: 'FormalProof4FHE.HasteBoots.PreparedMerkleNodes.resolve_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.PreparedMerkleNodes.resolve_raw

/-- info: 'FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability.cachedChildren_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability.cachedChildren_eq

/-- info: 'FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability.view_eq_analysis' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability.view_eq_analysis

/-- info: 'FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability.reconstruct_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability.reconstruct_get
