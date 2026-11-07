module
public import FormalProof4FHE.HasteBoots.NativeMerkleRoleDecoders
public import FormalProof4FHE.HasteBoots.SolverOperationCost
@[expose] public section

/-! Shared strict leaf decoding and first-match lookup over stored digest bytes.
The scan charges byte loads/comparisons and list/control operations. Its inputs
are prepared data; decoder preparation, digest materialization and physical
backend costs are separate. No parser or arbitrary callback runs in the scan. -/
namespace FormalProof4FHE.HasteBoots.PreparedMerklePayloads
open InputIndexedOracle (Input Byte)
open NativeRootMessage (Digest)
open NativeLookupRequestWire (Row)
open SolverOperationCost (Run)
open BinaryTree MerkleTreeExtractor
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

abbrev StoredDigest := { bytes : List Byte // bytes.length = 64 }
structure Entry where
  label : StoredDigest
  payload : Option Row

def store (label : Digest) : StoredDigest := ⟨List.ofFn label,by simp⟩

def prepare (log : QueryLog Input Digest) : List Entry :=
  log.map (fun entry => ⟨store entry.2,NativeMerkleRoleDecoders.leaf.decode entry.1⟩)

/-- Full strict payload preparation after labels are stored bytes. Digest
materialization from the public function representation remains separate. -/
def prepareStoredWithCost : List (Input × StoredDigest) → Run (List Entry)
  | [] => ⟨[],1⟩
  | (input,label)::tail =>
    let payload := CostedMerkleLeaf.decode input
    let rest := prepareStoredWithCost tail
    ⟨⟨label,payload.value⟩::rest.value,payload.cost+rest.cost+4⟩

theorem prepareStoredWithCost_value (log : List (Input × StoredDigest)) :
    (prepareStoredWithCost log).value =
      log.map (fun entry => (⟨entry.2,NativeMerkleRoleDecoders.leaf.decode entry.1⟩ : Entry)) := by
  induction log with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨input,label⟩
    simp only [prepareStoredWithCost,List.map_cons,ih]
    rfl

/-- Analysis-only size of supplied inputs, not a charge or runtime callback. -/
def storedInputBytes : List (Input × StoredDigest) → ℕ
  | [] => 0
  | head::tail => head.1.length+storedInputBytes tail

theorem prepareStoredWithCost_cost (log : List (Input × StoredDigest)) :
    (prepareStoredWithCost log).cost ≤ 208*(storedInputBytes log+log.length)+
      (9*NativeFieldWire.columnDomain.length+29)*log.length+1 := by
  induction log with
  | nil => simp [prepareStoredWithCost,storedInputBytes]
  | cons head tail ih =>
    rcases head with ⟨input,label⟩
    have first := CostedMerkleLeaf.decode_cost input
    simp only [prepareStoredWithCost,storedInputBytes,List.length_cons]
    nlinarith

theorem prepareStoredWithCost_raw (log : QueryLog Input Digest) :
    (prepareStoredWithCost (log.map (fun entry => (entry.1,store entry.2)))).value = prepare log := by
  rw [prepareStoredWithCost_value]
  simp only [prepare,List.map_map,Function.comp_def]

def byteEqual : List Byte → List Byte → Run Bool
  | [],[] => ⟨true,1⟩
  | [],_::_ => ⟨false,1⟩
  | _::_,[] => ⟨false,1⟩
  | left::ls,right::rs =>
    if left = right then
      let tail := byteEqual ls rs
      ⟨tail.value,tail.cost+6⟩
    else ⟨false,6⟩

theorem byteEqual_value (left right : List Byte) :
    (byteEqual left right).value = decide (left = right) := by
  induction left generalizing right with
  | nil => cases right <;> simp [byteEqual]
  | cons head tail ih =>
    cases right with
    | nil => simp [byteEqual]
    | cons next rest =>
      by_cases same : head = next
      · subst next; simp [byteEqual,ih]
      · simp [byteEqual,same]

theorem byteEqual_self_cost (bytes : List Byte) :
    (byteEqual bytes bytes).cost = 6*bytes.length+1 := by
  induction bytes with
  | nil => rfl
  | cons head tail ih =>
    simp only [byteEqual,ite_true,List.length_cons]
    omega

theorem byteEqual_cost (left right : List Byte) :
    (byteEqual left right).cost ≤ 6*(left.length+1) := by
  induction left generalizing right with
  | nil => cases right <;> simp [byteEqual]
  | cons head tail ih =>
    cases right with
    | nil => simp only [byteEqual,List.length_cons]; omega
    | cons next rest =>
      have bound := ih rest
      by_cases same : head = next <;> simp only [byteEqual,same,ite_true,ite_false,List.length_cons] <;> omega

/-- Stop at the first matching label with a decoded payload. A malformed
matching entry is skipped; later entries are never scanned after success. -/
def scan : List Entry → StoredDigest → Run (Option Row)
  | [],_ => ⟨none,1⟩
  | head::tail,label =>
    let equal := byteEqual head.label.val label.val
    let candidate := if equal.value then head.payload else none
    match candidate with
    | some row => ⟨some row,equal.cost+4⟩
    | none =>
      let rest := scan tail label
      ⟨rest.value,equal.cost+rest.cost+4⟩

theorem scan_value (log : List Entry) (label : StoredDigest) :
    (scan log label).value =
      (log.filterMap (fun entry => if entry.label = label then entry.payload else none)).head? := by
  induction log with
  | nil => rfl
  | cons head tail ih =>
    simp only [scan,byteEqual_value,List.filterMap_cons]
    by_cases same : head.label = label
    · simp only [decide_true,ite_true,same]
      cases head.payload <;> simp [ih]
    · have bytes : head.label.val ≠ label.val := fun equal => same (Subtype.ext equal)
      simp [bytes,same,ih]

theorem scan_head_success (head : Entry) (tail : List Entry) (label : StoredDigest)
    (same : head.label = label) (row : Row) (found : head.payload = some row) :
    scan (head::tail) label = ⟨some row,389⟩ := by
  simp only [scan,same,byteEqual_value,decide_true,ite_true,found]
  have cost := byteEqual_self_cost label.val
  rw [label.property] at cost
  simp only [cost]

/-- Once a prepared initial resolves a payload, appending any entries preserves
both its result and scan charge. No work from the suffix is included. -/
theorem scan_append_of_some (initial suffix : List Entry) (label : StoredDigest) (row : Row)
    (found : (scan initial label).value = some row) :
    scan (initial++suffix) label = scan initial label := by
  induction initial with
  | nil => simp only [scan] at found; contradiction
  | cons head tail ih =>
    cases candidate : (if (byteEqual head.label.val label.val).value then head.payload else none) with
    | some value => simp only [List.cons_append,scan,candidate]
    | none =>
      have continued : (scan tail label).value = some row := by
        simpa only [scan,candidate] using found
      simp only [List.cons_append,scan,candidate,ih continued]

theorem scan_cost (log : List Entry) (label : StoredDigest) :
    (scan log label).cost ≤ 394*log.length+1 := by
  induction log with
  | nil => simp [scan]
  | cons head tail ih =>
    have compared := byteEqual_cost head.label.val label.val
    rw [head.label.property] at compared
    simp only [scan,List.length_cons]
    split <;> dsimp only <;> omega

theorem store_eq (left right : Digest) : store left = store right ↔ left = right := by
  simp only [store,Subtype.mk.injEq,List.ofFn_inj]

theorem scan_prepare (log : QueryLog Input Digest) (label : Digest) :
    (scan (prepare log) (store label)).value =
      (log.filterMap (fun entry => if entry.2 = label then NativeMerkleRoleDecoders.leaf.decode entry.1 else none)).head? := by
  rw [scan_value]
  simp only [prepare,List.filterMap_map,Function.comp_def,store_eq]
end FormalProof4FHE.HasteBoots.PreparedMerklePayloads
