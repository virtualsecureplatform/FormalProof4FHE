module
public import FormalProof4FHE.HasteBoots.StoredDigestView
public import ToMathlib.Data.IndexedBinaryTree.Perfect
@[expose] public section

/-! Measured reconstruction from stored root/dummy bytes and prepared nodes.
Lookup is the concrete first-response resolver. Child-label copies and tree
construction are charged; no arbitrary resolver callback runs in this program.
Incoming digest adapters, leaf traversal and physical refinement are separate. -/
namespace FormalProof4FHE.HasteBoots.CostedMerkleTree
open InputIndexedOracle (Input Byte)
open NativeRootMessage (Digest)
open PreparedMerklePayloads (StoredDigest store)
open SolverOperationCost (Run)
open BinaryTree MerkleTreeExtractor

abbrev Tree (height : ℕ) := FullData (Option Digest) (Skeleton.perfect height)

def absent : (height : ℕ) → Run (Tree height)
  | 0 => ⟨.leaf none,2⟩
  | height+1 =>
    let left := absent height
    let right := absent height
    ⟨.internal none left.value right.value,left.cost+right.cost+3⟩

theorem absent_value (height : ℕ) :
    (absent height).value = populateDown (Skeleton.perfect height)
      (fun _ : Option Digest => (none,none)) none := by
  induction height with
  | zero => rfl
  | succ height ih => simp only [absent,Skeleton.perfect,populateDown,ih]

theorem absent_cost (height : ℕ) : (absent height).cost+3 = 5*2^height := by
  induction height with
  | zero => rfl
  | succ height ih => simp only [absent,Nat.pow_succ]; omega

def nativeChildren (dummy : Vector Byte 64) (nodes : List PreparedMerkleNodes.Entry)
    (root : Digest) : Option (Digest × Digest) :=
  (PreparedMerkleNodes.resolve dummy nodes (store root)).value.map CostedMerkleNode.view

def tree : (height : ℕ) → Vector Byte 64 → List PreparedMerkleNodes.Entry → StoredDigest → Run (Tree height)
  | 0,_,_,root => ⟨.leaf (some (StoredDigestView.view root)),3⟩
  | height+1,dummy,nodes,root =>
    let children := PreparedMerkleNodes.resolve dummy nodes root
    match children.value with
    | none =>
      let missing := absent height
      ⟨.internal (some (StoredDigestView.view root)) missing.value missing.value,children.cost+missing.cost+5⟩
    | some (left,right) =>
      let leftLabel := StoredDigestView.fromVector left
      let rightLabel := StoredDigestView.fromVector right
      let leftTree := tree height dummy nodes leftLabel.value
      let rightTree := tree height dummy nodes rightLabel.value
      ⟨.internal (some (StoredDigestView.view root)) leftTree.value rightTree.value,
        children.cost+leftLabel.cost+rightLabel.cost+leftTree.cost+rightTree.cost+7⟩

theorem tree_value (height : ℕ) (dummy : Vector Byte 64) (nodes : List PreparedMerkleNodes.Entry)
    (root : StoredDigest) :
    (tree height dummy nodes root).value =
      treeWith (fun _ : Unit => nativeChildren dummy nodes) (Skeleton.perfect height)
        (fun _ => ()) (StoredDigestView.view root) := by
  induction height generalizing root with
  | zero => rfl
  | succ height ih =>
    simp only [tree,treeWith,Skeleton.perfect,nativeChildren,StoredDigestView.store_view]
    cases found : (PreparedMerkleNodes.resolve dummy nodes root).value with
    | none => simp only [Option.map_none,absent_value]
    | some pair =>
      rcases pair with ⟨left,right⟩
      simp only [Option.map_some,CostedMerkleNode.view,ih,StoredDigestView.view_fromVector]

theorem tree_value_raw (height : ℕ) (dummy : Vector Byte 64) (nodes : List PreparedMerkleNodes.Entry)
    (root : Digest) :
    (tree height dummy nodes (store root)).value =
      treeWith (fun _ : Unit => nativeChildren dummy nodes) (Skeleton.perfect height) (fun _ => ()) root := by
  rw [tree_value,StoredDigestView.view_store]

def branchBound (length : ℕ) : ℕ := 394*length+269

theorem tree_cost (height : ℕ) (dummy : Vector Byte 64) (nodes : List PreparedMerkleNodes.Entry)
    (root : StoredDigest) :
    (tree height dummy nodes root).cost+branchBound nodes.length ≤
      (branchBound nodes.length+3)*2^height := by
  induction height generalizing root with
  | zero => simp only [tree,branchBound,Nat.pow_zero,Nat.mul_one]; omega
  | succ height ih =>
    have lookup := PreparedMerkleNodes.resolve_cost dummy nodes root
    have positive : 1 ≤ 2^height := by
      have nonzero : 0 < 2^height := pow_pos (by decide) _
      omega
    simp only [tree,Nat.pow_succ]
    split
    · have missing := absent_cost height
      have scaled := Nat.mul_le_mul_left (788*nodes.length) positive
      dsimp only [branchBound] at *
      nlinarith
    · rename_i left right found
      have first := ih (StoredDigestView.fromVector left).value
      have second := ih (StoredDigestView.fromVector right).value
      simp only [StoredDigestView.fromVector_cost]
      dsimp only [branchBound] at *
      nlinarith
/-- Prepare each strict role once and construct the tree after labels, root
and dummy are stored data. Leaf traversal/materialization is a separate phase. -/
def prepareTree (height : ℕ) (dummy : Vector Byte 64)
    (log : List (Input × StoredDigest)) (root : StoredDigest) :
    Run (Tree height × List PreparedMerklePayloads.Entry) :=
  let payloads := PreparedMerklePayloads.prepareStoredWithCost log
  let nodes := PreparedMerkleNodes.prepare log
  let built := tree height dummy nodes.value root
  ⟨(built.value,payloads.value),payloads.cost+nodes.cost+built.cost+3⟩

theorem prepareTree_value (height : ℕ) (dummy : Vector Byte 64)
    (log : List (Input × StoredDigest)) (root : StoredDigest) :
    (prepareTree height dummy log root).value =
      ((tree height dummy (PreparedMerkleNodes.prepare log).value root).value,
        (PreparedMerklePayloads.prepareStoredWithCost log).value) := rfl

theorem prepareTree_cost (height : ℕ) (dummy : Vector Byte 64)
    (log : List (Input × StoredDigest)) (root : StoredDigest) :
    (prepareTree height dummy log root).cost+branchBound log.length ≤
      208*(PreparedMerklePayloads.storedInputBytes log+log.length)+
      (9*NativeFieldWire.columnDomain.length+944)*log.length+
      (branchBound log.length+3)*2^height+5 := by
  have payloads := PreparedMerklePayloads.prepareStoredWithCost_cost log
  have nodes := PreparedMerkleNodes.prepare_cost log
  have built := tree_cost height dummy (PreparedMerkleNodes.prepare log).value root
  have size : (PreparedMerkleNodes.prepare log).value.length = log.length := by
    rw [PreparedMerkleNodes.prepare_value,List.length_map]
  rw [size] at built
  simp only [prepareTree]
  nlinarith
end FormalProof4FHE.HasteBoots.CostedMerkleTree
