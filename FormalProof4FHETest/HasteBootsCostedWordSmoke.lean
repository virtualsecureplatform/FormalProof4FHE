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
import all FormalProof4FHE.HasteBoots.StoredDigestView
import all FormalProof4FHE.HasteBoots.CostedMerkleTree
import all VCVio.CryptoFoundations.MerkleTree.Extractor
import all ToMathlib.Data.IndexedBinaryTree.Perfect
import all ToMathlib.Data.IndexedBinaryTree.Basic
import all FormalProof4FHE.HasteBoots.MerkleLeafIndexCost
import all FormalProof4FHE.HasteBoots.CostedMerkleLeafAccess
import all FormalProof4FHE.HasteBoots.CostedMerkleWord
import all FormalProof4FHE.HasteBoots.NativeGoldRawAvailability
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Byte)
open BinaryTree
private def digest (value : Nat) : NativeRootMessage.Digest := fun _ => Fin.ofNat 256 value
private def key (value : Nat) := PreparedMerklePayloads.store (digest value)
private def dummy : Vector Byte 64 := Vector.replicate 64 7
private def node (root left right : Nat) : PreparedMerkleNodes.Entry :=
  ⟨key root,some (Vector.replicate 64 (Fin.ofNat 256 left),Vector.replicate 64 (Fin.ofNat 256 right))⟩
private def row (value : Nat) : NativeLookupRequestWire.Row := ⟨[Fin.ofNat (2^64) value],by simp⟩
private def payload (label value : Nat) : PreparedMerklePayloads.Entry := ⟨key label,some (row value)⟩
private def values {n : Nat} (result : Vector NativeLookupRequestWire.Row n) : List (List Nat) :=
  result.toList.map (fun entry => entry.val.map Fin.val)

/-- info: [1, 9, 20, 34, 51] -/
#guard_msgs in
#eval [0,1,2,3,4].map (fun height => (MerkleLeafIndexCost.path height 0).cost)

-- All eight leaf positions retain the native most-significant-bit-first order.
/-- info: true -/
#guard_msgs in
#eval (List.finRange 8).all (fun position =>
      decide ((SkeletonLeafIndex.perfectEquiv 3).symm (MerkleLeafIndexCost.path 3 position.val).value = position))

/-- info: true -/
#guard_msgs in
#eval let result := MerkleLeafIndexCost.power 4
      decide (result.value = 16 ∧ result.cost = 13)

-- Missing payload and missing internal responses retain empty-row fallback.
/-- info: true -/
#guard_msgs in
#eval let zero := CostedMerkleWord.word 0 dummy [] [] (key 10)
      let one := CostedMerkleWord.word 1 dummy [] [] (key 10)
      let two := CostedMerkleWord.word 2 dummy [] [] (key 10)
      decide (values zero.value = [[]] ∧ zero.cost = 11 ∧
        values one.value = [[],[]] ∧ one.cost = 44 ∧
        values two.value = [[],[],[],[]] ∧ two.cost = 129)

-- Leaf lookup skips a malformed matching response and keeps the first valid one.
/-- info: true -/
#guard_msgs in
#eval let malformed : PreparedMerklePayloads.Entry := ⟨key 10,none⟩
      let result := CostedMerkleWord.word 0 dummy [] [malformed,payload 10 9] (key 10)
      decide (values result.value = [[9]] ∧ result.cost = 788)

/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleWord.word 1 dummy [node 10 11 12] [payload 11 1,payload 12 2] (key 10)
      decide (values result.value = [[1],[2]] ∧ result.cost = 1876)

-- Internal lookup stops at a malformed first response and follows dummy labels.
/-- info: true -/
#guard_msgs in
#eval let malformed : PreparedMerkleNodes.Entry := ⟨key 10,none⟩
      let result := CostedMerkleWord.word 1 dummy [malformed,node 10 11 12]
        [payload 7 9,payload 11 1,payload 12 2] (key 10)
      decide (values result.value = [[9],[9]])

/-- info: true -/
#guard_msgs in
#eval let malformed : PreparedMerkleNodes.Entry := ⟨key 7,none⟩
      let result := CostedMerkleWord.word 2 dummy [malformed] [payload 7 9] (key 7)
      decide (values result.value = [[9],[9],[9],[9]] ∧ result.cost = 5877)

-- A partially available tree keeps original leaf positions and empty slots.
/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleWord.word 2 dummy [node 10 11 12,node 11 13 14]
        [payload 13 3,payload 14 4] (key 10)
      decide (values result.value = [[3],[4],[],[]])

/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleWord.prepareWord 0 dummy [] (key 10)
      decide (values result.value = [[]] ∧ result.cost = 16)

-- Compare direct leaf reads against recovery from the already-proved tree model.
/-- info: true -/
#guard_msgs in
#eval let nodes := [node 10 11 12,node 11 13 14]
      let payloads := [payload 13 3,payload 14 4]
      let tree := (CostedMerkleTree.tree 2 dummy nodes (key 10)).value
      (List.finRange 4).all (fun position =>
        let index := SkeletonLeafIndex.perfectEquiv 2 position
        let direct := CostedMerkleLeafAccess.leaf 2 dummy nodes payloads (key 10) index
        let reference := (MerkleTreeExtractor.recoverLeaf
          (CostedMerkleLeafAccess.resolvePayload payloads) tree index).getD NativeGoldRawAvailability.emptyRow
        decide (direct.value = reference))
