module
public import FormalProof4FHE.HasteBoots.PreparedMerklePayloads
@[expose] public section

/-! Node preparation/lookup over stored labels. Presence and decoding failure
are distinct: the first matching response controls resolution even if malformed.
No response means no children; a malformed response supplies dummy children.
Digest adapters and physical/compiler/backend refinement are separate. -/
namespace FormalProof4FHE.HasteBoots.PreparedMerkleNodes
open InputIndexedOracle (Input Byte)
open NativeRootMessage (Digest)
open SolverOperationCost (Run)
open PreparedMerklePayloads (StoredDigest store byteEqual)
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

structure Entry where
  label : StoredDigest
  children : Option CostedMerkleNode.Stored

def prepare : List (Input × StoredDigest) → Run (List Entry)
  | [] => ⟨[],1⟩
  | (input,label)::tail =>
    let node := CostedMerkleNode.read input
    let rest := prepare tail
    ⟨⟨label,node.value⟩::rest.value,node.cost+rest.cost+4⟩

theorem prepare_value (log : List (Input × StoredDigest)) :
    (prepare log).value = log.map (fun entry => (⟨entry.2,(CostedMerkleNode.read entry.1).value⟩ : Entry)) := by
  induction log with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨input,label⟩
    simp only [prepare,List.map_cons,ih]

theorem prepare_cost (log : List (Input × StoredDigest)) :
    (prepare log).cost ≤ 915*log.length+1 := by
  induction log with
  | nil => simp [prepare]
  | cons head tail ih =>
    rcases head with ⟨input,label⟩
    have first := CostedMerkleNode.read_cost input
    simp only [prepare,List.length_cons]
    omega

/-- `some none` means a matching response exists but is not a valid node. -/
def lookup : List Entry → StoredDigest → Run (Option (Option CostedMerkleNode.Stored))
  | [],_ => ⟨none,1⟩
  | head::tail,label =>
    let equal := byteEqual head.label.val label.val
    if equal.value then ⟨some head.children,equal.cost+4⟩
    else
      let rest := lookup tail label
      ⟨rest.value,equal.cost+rest.cost+4⟩

theorem lookup_value (log : List Entry) (label : StoredDigest) :
    (lookup log label).value =
      (log.find? (fun entry => decide (entry.label = label))).map Entry.children := by
  induction log with
  | nil => rfl
  | cons head tail ih =>
    simp only [lookup,PreparedMerklePayloads.byteEqual_value,List.find?_cons]
    by_cases same : head.label = label
    · simp [same]
    · have different : head.label.val ≠ label.val := fun equal => same (Subtype.ext equal)
      simp [same,different,ih]

theorem lookup_head_match (head : Entry) (tail : List Entry) (label : StoredDigest)
    (same : head.label = label) :
    lookup (head::tail) label = ⟨some head.children,389⟩ := by
  simp only [lookup,same,PreparedMerklePayloads.byteEqual_value,decide_true,ite_true]
  have compared := PreparedMerklePayloads.byteEqual_self_cost label.val
  rw [label.property] at compared
  simp only [compared]

theorem lookup_cost (log : List Entry) (label : StoredDigest) :
    (lookup log label).cost ≤ 394*log.length+1 := by
  induction log with
  | nil => simp [lookup]
  | cons head tail ih =>
    have compared := PreparedMerklePayloads.byteEqual_cost head.label.val label.val
    rw [head.label.property] at compared
    simp only [lookup,List.length_cons]
    split <;> dsimp only <;> omega

def resolve (dummy : Vector Byte 64) (log : List Entry) (label : StoredDigest) :
    Run (Option CostedMerkleNode.Stored) :=
  let found := lookup log label
  ⟨found.value.map (fun node => node.getD (dummy,dummy)),found.cost+3⟩

theorem resolve_cost (dummy : Vector Byte 64) (log : List Entry) (label : StoredDigest) :
    (resolve dummy log label).cost ≤ 394*log.length+4 := by
  have bound := lookup_cost log label
  simp only [resolve]
  omega

theorem lookup_prepare (log : List (Input × StoredDigest)) (label : StoredDigest) :
    (lookup (prepare log).value label).value =
      (log.find? (fun entry => decide (entry.2 = label))).map (fun entry => (CostedMerkleNode.read entry.1).value) := by
  rw [lookup_value,prepare_value,List.find?_map]
  simp only [Function.comp_def,Option.map_map]

theorem lookup_raw (log : MerkleTreeExtractor.QueryLog Input Digest) (label : Digest) :
    (lookup (prepare (log.map (fun entry => (entry.1,store entry.2)))).value (store label)).value =
      (log.find? (fun entry => decide (entry.2 = label))).map (fun entry => (CostedMerkleNode.read entry.1).value) := by
  rw [lookup_prepare,List.find?_map]
  simp only [Function.comp_def,PreparedMerklePayloads.store_eq,Option.map_map]
theorem resolve_raw (dummy : Vector Byte 64)
    (log : MerkleTreeExtractor.QueryLog Input Digest) (label : Digest) :
    (resolve dummy (prepare (log.map (fun entry => (entry.1,store entry.2)))).value (store label)).value.map
        CostedMerkleNode.view =
      (log.find? (fun entry => decide (entry.2 = label))).map
        (fun entry => (NativeMerkleRoleDecoders.node.decode entry.1).getD (dummy.get,dummy.get)) := by
  simp only [resolve,lookup_raw,Option.map_map,Function.comp_def,
    NativeMerkleRoleDecoders.node,CostedMerkleNode.decode]
  cases found : log.find? (fun entry => decide (entry.2 = label)) with
  | none => rfl
  | some entry =>
    simp only [Option.map_some]
    cases parsed : (CostedMerkleNode.read entry.1).value <;> rfl
end FormalProof4FHE.HasteBoots.PreparedMerkleNodes
