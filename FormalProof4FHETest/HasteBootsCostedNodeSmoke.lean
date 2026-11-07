module
import all FormalProof4FHE.HasteBoots.FixedByteReadCost
import all FormalProof4FHE.HasteBoots.CostedMerkleNode
import all FormalProof4FHE.HasteBoots.BytePrefixMatchCost
import all FormalProof4FHE.HasteBoots.IntegerEncodingCost
import all FormalProof4FHE.HasteBoots.RowEncodingCost
import all FormalProof4FHE.HasteBoots.CostedMerkleLeaf
import all FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders
import all FormalProof4FHE.HasteBoots.PreparedMerklePayloads
import all FormalProof4FHE.HasteBoots.BytePrefixCost
import all FormalProof4FHE.HasteBoots.IntegerPrefixCost
import all FormalProof4FHE.HasteBoots.UsizeVectorCost
import all FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
import all FormalProof4FHE.HasteBoots.NativeLookupRequestWire
import all FormalProof4FHE.HasteBoots.NativePrefixCodec
import all FormalProof4FHE.HasteBoots.NativeUsizeMessage
import all FormalProof4FHE.HasteBoots.NativeIntegerPrefix
import all FormalProof4FHE.HasteBoots.NativeFieldWire
import all FormalProof4FHE.HasteBoots.NativeTranscript
import all FormalProof4FHE.HasteBoots.TranscriptFrame
import all FormalProof4FHE.HasteBoots.NativeByteCodec
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all FormalProof4FHE.HasteBoots.PreparedMerkleNodes
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Input Byte)
private def left : NativeRootMessage.Digest := fun i => Fin.ofNat 256 i.val
private def right : NativeRootMessage.Digest := fun i => Fin.ofNat 256 (i.val+64)
private def label : NativeRootMessage.Digest := fun _ => 11
private def other : NativeRootMessage.Digest := fun _ => 12
private def input : Input := NativeGoldColumnAuthentication.nodeInput left right
private def bytes (node : CostedMerkleNode.Stored) : Input × Input := (node.1.toList,node.2.toList)
private def dummy : Vector Byte 64 := Vector.replicate 64 7

/-- info: true -/
#guard_msgs in
#eval let result := FixedByteReadCost.read 3 [1,2,3,4,5]
      decide (result.value.map (fun pair => (pair.1.toList,pair.2)) = some ([1,2,3],[4,5]) ∧ result.cost = 25)

/-- info: true -/
#guard_msgs in
#eval let result := FixedByteReadCost.read (2^64-1) [1,2,3]
      decide (result.value = none ∧ result.cost = 18)

/-- info: true -/
#guard_msgs in
#eval let result := FixedByteReadCost.read 0 [9]
      decide (result.value.map (fun pair => (pair.1.toList,pair.2)) = some ([],[9]) ∧ result.cost = 4)

/-- info: [9, 14, 324, 463, 468, 778, 914, 914] -/
#guard_msgs in
#eval [0,1,63,64,65,127,128,129].map (fun n => (CostedMerkleNode.decode (List.replicate n 0)).cost)

-- Check every byte of each stored child and of the native function views.
/-- info: true -/
#guard_msgs in
#eval let stored := CostedMerkleNode.read input
      let decoded := CostedMerkleNode.decode input
      decide (stored.value.map bytes = some (List.ofFn left,List.ofFn right) ∧ stored.cost = 911 ∧
        decoded.value.map (fun pair => (List.ofFn pair.1,List.ofFn pair.2)) = some (List.ofFn left,List.ofFn right) ∧
        decoded.cost = 914)

-- Exact-width completion rejects a large trailing suffix without traversing it.
/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleNode.decode (input++List.replicate 10000 99)
      decide (result.value.isNone ∧ result.cost = 914)

/-- info: true -/
#guard_msgs in
#eval let result := NativeMerkleRoleDecoders.node.decode input
      decide (result.map (fun pair => (List.ofFn pair.1,List.ofFn pair.2)) = some (List.ofFn left,List.ofFn right))

-- Every complete 128-byte spelling is canonical for two raw 64-byte digests.
/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleNode.read (List.replicate 128 255)
      decide (result.value.map bytes = some (List.replicate 64 255,List.replicate 64 255))

-- A malformed first matching response wins over a later valid node. Presence
-- is retained and resolution supplies the dummy children, matching tree lookup.
/-- info: true -/
#guard_msgs in
#eval let key := PreparedMerklePayloads.store label
      let prepared := PreparedMerkleNodes.prepare [([99],key),(input,key)]
      let found := PreparedMerkleNodes.lookup prepared.value key
      let resolved := PreparedMerkleNodes.resolve dummy prepared.value key
      decide (prepared.cost = 931 ∧ found.value = some none ∧ found.cost = 389 ∧
        resolved.value.map bytes = some (dummy.toList,dummy.toList) ∧ resolved.cost = 392)

-- No matching response remains absent, rather than creating dummy children.
/-- info: true -/
#guard_msgs in
#eval let key := PreparedMerklePayloads.store label
      let prepared := PreparedMerkleNodes.prepare [(input,key)]
      let resolved := PreparedMerkleNodes.resolve dummy prepared.value (PreparedMerklePayloads.store other)
      decide (resolved.value = none ∧ resolved.cost = 14)

-- A valid first match is not replaced by a later malformed response.
/-- info: true -/
#guard_msgs in
#eval let key := PreparedMerklePayloads.store label
      let prepared := PreparedMerkleNodes.prepare [(input,key),([99],key)]
      let resolved := PreparedMerkleNodes.resolve dummy prepared.value key
      decide (resolved.value.map bytes = some (List.ofFn left,List.ofFn right) ∧ resolved.cost = 392)

/-- info: true -/
#guard_msgs in
#eval let key := PreparedMerklePayloads.store label
      let prepared := PreparedMerkleNodes.prepare []
      let resolved := PreparedMerkleNodes.resolve dummy prepared.value key
      decide (prepared.cost = 1 ∧ resolved.value = none ∧ resolved.cost = 4)

-- Complete guarded reference equality includes both truncation and extra bytes.
/-- info: true -/
#guard_msgs in
#eval [[],[99],input,input++[0],input.dropLast,List.replicate 128 255].all (fun supplied =>
      let observed := NativeMerkleRoleDecoders.node.decode supplied
      let reference := (NativeMerkleRoleDecoders.guarded
        (fun pair : NativeRootMessage.Digest × NativeRootMessage.Digest =>
          NativeGoldColumnAuthentication.nodeInput pair.1 pair.2)
        NativeMerkleRoleDecoders.parseNode NativeMerkleRoleDecoders.parseNode_encode).decode supplied
      decide (observed.map (fun pair => (List.ofFn pair.1,List.ofFn pair.2)) =
        reference.map (fun pair => (List.ofFn pair.1,List.ofFn pair.2))))
