module
public import FormalProof4FHE.HasteBoots.CostedMerkleLeafAccess
public import FormalProof4FHE.HasteBoots.SolverOperationErasure
@[expose] public section

/-! Materialized public column words from stored root/dummy bytes and prepared
role tables. Index construction, concrete path lookup, payload lookup and output
stores are charged. No arbitrary label/resolver callback runs in this producer.
Incoming adapters and physical/compiler/backend refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.CostedMerkleWord
open InputIndexedOracle (Input Byte)
open NativeLookupRequestWire (Row)
open PreparedMerklePayloads (StoredDigest store)
open SolverOperationCost (Run tabulate)
open scoped BigOperators
open BinaryTree MerkleTreeExtractor

def entry (height : ℕ) (dummy : Vector Byte 64) (nodes : List PreparedMerkleNodes.Entry)
    (payloads : List PreparedMerklePayloads.Entry) (root : StoredDigest) (position : ℕ) : Run Row :=
  let index := MerkleLeafIndexCost.path height position
  let result := CostedMerkleLeafAccess.leaf height dummy nodes payloads root index.value
  ⟨result.value,index.cost+result.cost+2⟩

theorem entry_value (height : ℕ) (dummy : Vector Byte 64) (nodes : List PreparedMerkleNodes.Entry)
    (payloads : List PreparedMerklePayloads.Entry) (root : StoredDigest) (position : ℕ) :
    (entry height dummy nodes payloads root position).value =
      (recoverLeaf (CostedMerkleLeafAccess.resolvePayload payloads)
        (CostedMerkleTree.tree height dummy nodes root).value (SkeletonLeafIndex.ofNat height position)).getD
          NativeGoldRawAvailability.emptyRow := by
  simp only [entry,CostedMerkleLeafAccess.leaf_value,MerkleLeafIndexCost.path_value]

def perLeaf (height nodeCount payloadCount : ℕ) :=
  MerkleLeafIndexCost.pathBound height+CostedMerkleLeafAccess.leafBound height nodeCount payloadCount+3

theorem entry_cost (height : ℕ) (dummy : Vector Byte 64) (nodes : List PreparedMerkleNodes.Entry)
    (payloads : List PreparedMerklePayloads.Entry) (root : StoredDigest) (position : ℕ) :
    (entry height dummy nodes payloads root position).cost+1 ≤ perLeaf height nodes.length payloads.length := by
  have index := MerkleLeafIndexCost.path_cost height position
  have accessed := CostedMerkleLeafAccess.leaf_cost height dummy nodes payloads root
    (MerkleLeafIndexCost.path height position).value
  simp only [entry,perLeaf]
  omega

def word (height : ℕ) (dummy : Vector Byte 64) (nodes : List PreparedMerkleNodes.Entry)
    (payloads : List PreparedMerklePayloads.Entry) (root : StoredDigest) : Run (Vector Row (2^height)) :=
  let count := MerkleLeafIndexCost.power height
  let result := tabulate (fun position : Fin count.value => entry height dummy nodes payloads root position.val)
  ⟨⟨result.value.toArray,by rw [Vector.size_toArray,MerkleLeafIndexCost.power_value]⟩,
    count.cost+result.cost+1⟩

theorem word_get (height : ℕ) (dummy : Vector Byte 64) (nodes : List PreparedMerkleNodes.Entry)
    (payloads : List PreparedMerklePayloads.Entry) (root : StoredDigest) (position : Fin (2^height)) :
    (word height dummy nodes payloads root).value.get position =
      (recoverLeaf (CostedMerkleLeafAccess.resolvePayload payloads)
        (CostedMerkleTree.tree height dummy nodes root).value (SkeletonLeafIndex.perfectEquiv height position)).getD
          NativeGoldRawAvailability.emptyRow := by
  simp only [word,SolverOperationCost.tabulate_value,Vector.get,
    Vector.getElem_toArray,Vector.getElem_ofFn,entry_value,SkeletonLeafIndex.perfectEquiv_apply]
  congr 3

theorem word_cost (height : ℕ) (dummy : Vector Byte 64) (nodes : List PreparedMerkleNodes.Entry)
    (payloads : List PreparedMerklePayloads.Entry) (root : StoredDigest) :
    (word height dummy nodes payloads root).cost ≤
      2^height*perLeaf height nodes.length payloads.length+3*height+3 := by
  have summed := Finset.sum_le_sum (fun position (_ : position ∈
      (Finset.univ : Finset (Fin (MerkleLeafIndexCost.power height).value))) =>
    entry_cost height dummy nodes payloads root position.val)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,Nat.mul_one] at summed
  simp only [word,SolverOperationCost.tabulate_cost,MerkleLeafIndexCost.power_cost]
  rw [MerkleLeafIndexCost.power_value] at *
  nlinarith

def prepareWord (height : ℕ) (dummy : Vector Byte 64) (log : List (Input × StoredDigest))
    (root : StoredDigest) : Run (Vector Row (2^height)) :=
  let payloads := PreparedMerklePayloads.prepareStoredWithCost log
  let nodes := PreparedMerkleNodes.prepare log
  let result := word height dummy nodes.value payloads.value root
  ⟨result.value,payloads.cost+nodes.cost+result.cost+3⟩

theorem prepareWord_get (height : ℕ) (dummy : Vector Byte 64) (log : List (Input × StoredDigest))
    (root : StoredDigest) (position : Fin (2^height)) :
    (prepareWord height dummy log root).value.get position =
      (recoverLeaf (CostedMerkleLeafAccess.resolvePayload (PreparedMerklePayloads.prepareStoredWithCost log).value)
        (CostedMerkleTree.tree height dummy (PreparedMerkleNodes.prepare log).value root).value
        (SkeletonLeafIndex.perfectEquiv height position)).getD NativeGoldRawAvailability.emptyRow :=
  word_get _ _ _ _ _ _

theorem prepareWord_cost (height : ℕ) (dummy : Vector Byte 64) (log : List (Input × StoredDigest))
    (root : StoredDigest) :
    (prepareWord height dummy log root).cost ≤
      208*(PreparedMerklePayloads.storedInputBytes log+log.length)+
      (9*NativeFieldWire.columnDomain.length+944)*log.length+
      2^height*perLeaf height log.length log.length+3*height+8 := by
  have payloads := PreparedMerklePayloads.prepareStoredWithCost_cost log
  have nodes := PreparedMerkleNodes.prepare_cost log
  have built := word_cost height dummy (PreparedMerkleNodes.prepare log).value
    (PreparedMerklePayloads.prepareStoredWithCost log).value root
  have nodeSize : (PreparedMerkleNodes.prepare log).value.length = log.length := by
    rw [PreparedMerkleNodes.prepare_value,List.length_map]
  have payloadSize : (PreparedMerklePayloads.prepareStoredWithCost log).value.length = log.length := by
    rw [PreparedMerklePayloads.prepareStoredWithCost_value,List.length_map]
  rw [nodeSize,payloadSize] at built
  simp only [prepareWord]
  nlinarith
end FormalProof4FHE.HasteBoots.CostedMerkleWord
