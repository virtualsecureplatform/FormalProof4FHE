module
public import FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders
public import FormalProof4FHE.HasteBoots.NativeGoldRawAvailability
public import FormalProof4FHE.HasteBoots.FiniteLinearSolver
public import FormalProof4FHE.HasteBoots.PreparedMerklePayloads
public import FormalProof4FHE.HasteBoots.PreparedMerkleNodes
public import FormalProof4FHE.HasteBoots.CostedMerkleTree
@[expose] public section

/-! Reconstruct a materialized raw column word from a supplied frozen public
hash log. No oracle queries or classical inverse searches occur at runtime.
Unknown leaf payloads use the existing empty-row fallback. -/
namespace FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeLookupRequestWire (Row)
open NativeGoldColumnAuthentication (encoding)
open BinaryTree MerkleTreeExtractor
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq
abbrev Log := QueryLog Input Digest

def view (dummy : Digest) : QueryView Input Unit Digest where
  address _ := ()
  input input := (NativeMerkleRoleDecoders.node.decode input).getD (dummy,dummy)

def resolvePrepared (payloads : List PreparedMerklePayloads.Entry) (label : Digest) : Option Row :=
  (PreparedMerklePayloads.scan payloads (PreparedMerklePayloads.store label)).value

def resolve (log : Log) : Digest → Option Row :=
  resolvePrepared (PreparedMerklePayloads.prepare log)

def cachedChildren (dummy : Vector InputIndexedOracle.Byte 64)
    (nodes : List PreparedMerkleNodes.Entry) (root : Digest) : Option (Digest × Digest) :=
  (PreparedMerkleNodes.resolve dummy nodes (PreparedMerklePayloads.store root)).value.map CostedMerkleNode.view

theorem cachedChildren_eq (dummy : Digest) (log : Log) :
    cachedChildren (Vector.ofFn dummy)
      (PreparedMerkleNodes.prepare (log.map (fun entry => (entry.1,PreparedMerklePayloads.store entry.2)))).value =
      children (view dummy) log () := by
  funext root
  have dummyEq : (Vector.ofFn dummy).get = dummy := by
    funext i
    exact FiniteLinearSolver.get_ofFn dummy i
  rw [cachedChildren,PreparedMerkleNodes.resolve_raw,dummyEq]
  change (log.find? (fun entry => decide (entry.2 = root))).map
      (fun entry => (NativeMerkleRoleDecoders.node.decode entry.1).getD (dummy,dummy)) = _
  simp only [children,view,beq_self_eq_true,Bool.true_and,Bool.beq_eq_decide_eq]
  cases log.find? (fun entry => decide (entry.2 = root)) <;> rfl

theorem measuredTree_eq (height : ℕ) (dummy : Vector InputIndexedOracle.Byte 64)
    (nodes : List PreparedMerkleNodes.Entry) (root : Digest) :
    (CostedMerkleTree.tree height dummy nodes (PreparedMerklePayloads.store root)).value =
      treeWith (fun _ label => cachedChildren dummy nodes label) (Skeleton.perfect height)
        (fun _ => ()) root := CostedMerkleTree.tree_value_raw height dummy nodes root

def reconstruct (height : ℕ) (dummy : Digest) (log : Log) (root : Digest) : Vector Row (2^height) :=
  let storedLog := log.map (fun entry => (entry.1,PreparedMerklePayloads.store entry.2))
  let prepared := CostedMerkleTree.prepareTree height (Vector.ofFn dummy) storedLog
    (PreparedMerklePayloads.store root)
  let partialTree := prepared.value.1
  let payloads := prepared.value.2
  Vector.ofFn (fun position =>
    (recoverLeaf (resolvePrepared payloads) partialTree (SkeletonLeafIndex.perfectEquiv height position)).getD NativeGoldRawAvailability.emptyRow)

theorem view_eq_analysis (dummy : Digest) : view dummy = (MerkleOracle.model encoding dummy).view := by
  simp only [view,MerkleOracle.model,NativeMerkleRoleDecoders.node_eq_analysis]
  rfl

theorem resolve_eq_analysis (log : Log) : resolve log = MerklePayload.resolve encoding log := by
  funext label
  simp only [resolve,resolvePrepared,PreparedMerklePayloads.scan_prepare,
    MerklePayload.resolve,MerklePayload.candidates,NativeMerkleRoleDecoders.leaf_eq_analysis]
  rfl

theorem reconstruct_get (height : ℕ) (dummy : Digest) (log : Log) (root : Digest) (position : Fin (2^height)) :
    (reconstruct height dummy log root).get position =
      MerkleAvailability.word encoding dummy NativeGoldRawAvailability.emptyRow height log root position := by
  have resolver : resolvePrepared (PreparedMerklePayloads.prepare log) = resolve log := rfl
  simp only [reconstruct,CostedMerkleTree.prepareTree_value,measuredTree_eq,
    PreparedMerklePayloads.prepareStoredWithCost_raw,cachedChildren_eq,
    FiniteLinearSolver.get_ofFn,resolver,view_eq_analysis,resolve_eq_analysis,
    MerkleAvailability.word,MerkleAvailability.payloadAt,MerkleAvailability.tree,
    MerkleTreeExtractor.tree,MerkleTreeExtractor.treeAt]
end FormalProof4FHE.HasteBoots.ExecutableMerkleAvailability
