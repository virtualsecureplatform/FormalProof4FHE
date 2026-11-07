module
public import FormalProof4FHE.HasteBoots.MerkleLeafIndexCost
public import FormalProof4FHE.HasteBoots.NativeGoldRawAvailability
@[expose] public section

/-! Closed leaf access from stored root/dummy bytes and prepared role tables.
Traversal uses the concrete first-response node resolver; reached leaves use
first-valid payload lookup. Missing branches return the original empty row.
Incoming adapters and physical/compiler/backend refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.CostedMerkleLeafAccess
open InputIndexedOracle (Byte)
open NativeLookupRequestWire (Row)
open PreparedMerklePayloads (StoredDigest store)
open SolverOperationCost (Run)
open BinaryTree MerkleTreeExtractor

def resolvePayload (payloads : List PreparedMerklePayloads.Entry) (label : NativeRootMessage.Digest) : Option Row :=
  (PreparedMerklePayloads.scan payloads (store label)).value

theorem absent_leaf (height : ℕ) (index : SkeletonLeafIndex (Skeleton.perfect height)) :
    (CostedMerkleTree.absent height).value.get index.toNodeIndex = none := by
  induction height with
  | zero => cases index; rfl
  | succ height ih =>
    cases index <;> simp only [CostedMerkleTree.absent,SkeletonLeafIndex.toNodeIndex,FullData.get,ih]

def leaf : (height : ℕ) → Vector Byte 64 → List PreparedMerkleNodes.Entry →
    List PreparedMerklePayloads.Entry → StoredDigest →
    SkeletonLeafIndex (Skeleton.perfect height) → Run Row
  | 0,_,_,payloads,root,_ =>
    let found := PreparedMerklePayloads.scan payloads root
    ⟨found.value.getD NativeGoldRawAvailability.emptyRow,found.cost+3⟩
  | height+1,dummy,nodes,payloads,root,index =>
    let found := PreparedMerkleNodes.resolve dummy nodes root
    match found.value with
    | none => ⟨NativeGoldRawAvailability.emptyRow,found.cost+3⟩
    | some (left,right) =>
      match index with
      | .ofLeft next =>
        let label := StoredDigestView.fromVector left
        let rest := leaf height dummy nodes payloads label.value next
        ⟨rest.value,found.cost+label.cost+rest.cost+5⟩
      | .ofRight next =>
        let label := StoredDigestView.fromVector right
        let rest := leaf height dummy nodes payloads label.value next
        ⟨rest.value,found.cost+label.cost+rest.cost+5⟩

theorem leaf_value (height : ℕ) (dummy : Vector Byte 64) (nodes : List PreparedMerkleNodes.Entry)
    (payloads : List PreparedMerklePayloads.Entry) (root : StoredDigest)
    (index : SkeletonLeafIndex (Skeleton.perfect height)) :
    (leaf height dummy nodes payloads root index).value =
      (recoverLeaf (resolvePayload payloads) (CostedMerkleTree.tree height dummy nodes root).value index).getD
        NativeGoldRawAvailability.emptyRow := by
  induction height generalizing root with
  | zero =>
    cases index
    simp only [leaf,CostedMerkleTree.tree,recoverLeaf,FullData.get,SkeletonLeafIndex.toNodeIndex,
      Option.bind_some,resolvePayload,StoredDigestView.store_view]
  | succ height ih =>
    simp only [leaf,CostedMerkleTree.tree]
    cases found : (PreparedMerkleNodes.resolve dummy nodes root).value with
    | none =>
      cases index <;> simp only [recoverLeaf,SkeletonLeafIndex.toNodeIndex,FullData.get,
        absent_leaf,Option.bind_none,Option.getD_none]
    | some pair =>
      rcases pair with ⟨left,right⟩
      cases index <;> simp only [recoverLeaf,SkeletonLeafIndex.toNodeIndex,FullData.get,ih]

def leafBound (height nodeCount payloadCount : ℕ) :=
  (394*nodeCount+138)*height+394*payloadCount+4

theorem leaf_cost (height : ℕ) (dummy : Vector Byte 64) (nodes : List PreparedMerkleNodes.Entry)
    (payloads : List PreparedMerklePayloads.Entry) (root : StoredDigest)
    (index : SkeletonLeafIndex (Skeleton.perfect height)) :
    (leaf height dummy nodes payloads root index).cost ≤ leafBound height nodes.length payloads.length := by
  induction height generalizing root with
  | zero =>
    have bound := PreparedMerklePayloads.scan_cost payloads root
    simp only [leaf,leafBound]
    omega
  | succ height ih =>
    have resolved := PreparedMerkleNodes.resolve_cost dummy nodes root
    simp only [leaf]
    split
    · dsimp only [leafBound] at *; nlinarith
    · rename_i left right found
      cases index with
      | ofLeft next =>
        have rest := ih (StoredDigestView.fromVector left).value next
        simp only [StoredDigestView.fromVector_cost]
        dsimp only [leafBound] at *
        nlinarith
      | ofRight next =>
        have rest := ih (StoredDigestView.fromVector right).value next
        simp only [StoredDigestView.fromVector_cost]
        dsimp only [leafBound] at *
        nlinarith
end FormalProof4FHE.HasteBoots.CostedMerkleLeafAccess
