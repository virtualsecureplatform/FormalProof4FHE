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
open FormalProof4FHE.HasteBoots
open InputIndexedOracle (Byte)
open BinaryTree
private def digest (value : Nat) : NativeRootMessage.Digest := fun _ => Fin.ofNat 256 value
private def key (value : Nat) := PreparedMerklePayloads.store (digest value)
private def bytes (value : Nat) : List Byte := List.replicate 64 (Fin.ofNat 256 value)
private def dummy : Vector Byte 64 := Vector.replicate 64 7
private def node (root left right : Nat) : PreparedMerkleNodes.Entry :=
  ⟨key root,some (Vector.replicate 64 (Fin.ofNat 256 left),Vector.replicate 64 (Fin.ofNat 256 right))⟩
private def leaves (height : Nat) (tree : CostedMerkleTree.Tree height) : List (Option (List Byte)) :=
  (List.finRange (2^height)).map (fun i =>
    (tree.get (SkeletonLeafIndex.perfectEquiv height i).toNodeIndex).map List.ofFn)

/-- info: true -/
#guard_msgs in
#eval let value := StoredDigestView.fromVector dummy
      decide (value.value.val = bytes 7 ∧ value.cost = 129 ∧
        List.ofFn (StoredDigestView.view value.value) = bytes 7)

-- Height zero constructs only a root; it does not query the supplied node log.
/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleTree.tree 0 dummy (List.replicate 10000 (node 10 11 12)) (key 10)
      decide (result.cost = 3 ∧ leaves 0 result.value = [some (bytes 10)])

/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleTree.tree 1 dummy [node 10 11 12] (key 10)
      decide (result.cost = 663 ∧ leaves 1 result.value = [some (bytes 11),some (bytes 12)])

-- An absent response leaves both descendant labels absent, not dummy-valued.
/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleTree.tree 1 dummy [] (key 10)
      decide (result.cost = 11 ∧ leaves 1 result.value = [none,none] ∧
        result.value.getRootValue.map List.ofFn = some (bytes 10))

/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleTree.tree 2 dummy [] (key 10)
      decide (result.cost = 16 ∧ leaves 2 result.value = [none,none,none,none])

-- Ordered children and mixed present/absent subtrees preserve leaf positions.
/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleTree.tree 2 dummy [node 10 11 12,node 11 13 14] (key 10)
      decide (result.cost = 1361 ∧ leaves 2 result.value = [some (bytes 13),some (bytes 14),none,none])

-- A present malformed first response supplies dummy children, ignoring aliases.
/-- info: true -/
#guard_msgs in
#eval let malformed : PreparedMerkleNodes.Entry := ⟨key 10,none⟩
      let result := CostedMerkleTree.tree 1 dummy [malformed,node 10 11 12] (key 10)
      decide (result.cost = 663 ∧ leaves 1 result.value = [some (bytes 7),some (bytes 7)])

-- Dummy-label cycles terminate by skeleton height and remain fully populated.
/-- info: true -/
#guard_msgs in
#eval let malformed : PreparedMerkleNodes.Entry := ⟨key 7,none⟩
      let result := CostedMerkleTree.tree 2 dummy [malformed] (key 7)
      decide (result.cost = 1983 ∧ leaves 2 result.value = List.replicate 4 (some (bytes 7)))

/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleTree.absent 4
      decide (result.cost = 77 ∧ leaves 4 result.value = List.replicate 16 none)

/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleTree.prepareTree 0 dummy [] (key 10)
      decide (result.cost = 8 ∧ result.value.2.length = 0 ∧ leaves 0 result.value.1 = [some (bytes 10)])

-- Both role preparation passes and actual tree work contribute to the charge.
/-- info: true -/
#guard_msgs in
#eval let result := CostedMerkleTree.prepareTree 1 dummy [([],key 7)] (key 7)
      decide (result.cost = 688 ∧ result.value.2.length = 1 ∧
        leaves 1 result.value.1 = [some (bytes 7),some (bytes 7)])
