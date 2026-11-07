module
public import FormalProof4FHE.HasteBoots.StoredGoldPublicSource
public import FormalProof4FHE.HasteBoots.StoredFrozenLedgerBudget
@[expose] public section

/-! Stored ordered hash observations with measured reference digest decoding.
The existing analysis decoder zero-pads missing bytes and ignores bytes after
64; this module preserves that behavior on arbitrary histories. It is not the
strict native hash-output deserializer. Stored logs retain immutable input lists
and byte data, with no functional digest callback in the executed program. -/
namespace FormalProof4FHE.HasteBoots.StoredHashLogCost
open InputIndexedOracle (Input Byte)
open SolverOperationCost (Run)
open PreparedMerklePayloads (StoredDigest)
open StoredGoldPublicSource (Log viewLog)

def pad : ℕ → Input → Run Input
  | 0,_ => ⟨[],1⟩
  | count+1,[] =>
    let rest := pad count []
    ⟨0::rest.value,rest.cost+3⟩
  | count+1,head::tail =>
    let rest := pad count tail
    ⟨head::rest.value,rest.cost+4⟩

theorem pad_length (count : ℕ) (input : Input) : (pad count input).value.length = count := by
  induction count generalizing input with
  | zero => rfl
  | succ count ih => cases input <;> simp only [pad,List.length_cons,ih]

theorem pad_value (count : ℕ) (input : Input) :
    (pad count input).value = List.ofFn (fun i : Fin count => input[i.val]?.getD 0) := by
  induction count generalizing input with
  | zero => rfl
  | succ count ih =>
    cases input with
    | nil => simp only [pad,List.ofFn_succ,List.getElem?_nil,Option.getD_none,ih]
    | cons head tail => simp only [pad,List.ofFn_succ,Fin.val_zero,Fin.val_succ,
        List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,ih]

theorem pad_cost (count : ℕ) (input : Input) : (pad count input).cost ≤ 4*count+1 := by
  induction count generalizing input with
  | zero => simp [pad]
  | succ count ih =>
    cases input with
    | nil => have bound := ih []; simp only [pad]; omega
    | cons head tail => have bound := ih tail; simp only [pad]; omega

def digest (input : Input) : Run StoredDigest :=
  let bytes := pad 64 input
  ⟨⟨bytes.value,by exact pad_length 64 input⟩,bytes.cost+2⟩

theorem digest_value (input : Input) :
    (digest input).value = PreparedMerklePayloads.store (JointHashCache.decode input) := by
  apply Subtype.ext
  exact pad_value 64 input

theorem digest_view (input : Input) : StoredDigestView.view (digest input).value = JointHashCache.decode input := by
  rw [digest_value,StoredDigestView.view_store]

theorem digest_cost (input : Input) : (digest input).cost ≤ 259 := by
  have bytes := pad_cost 64 input
  simp only [digest]
  omega

def append : Log → Log → Run Log
  | [],last => ⟨last,1⟩
  | head::tail,last =>
    let rest := append tail last
    ⟨head::rest.value,rest.cost+3⟩

theorem append_value (first last : Log) : (append first last).value = first++last := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [append,ih,List.cons_append]

theorem append_cost (first last : Log) : (append first last).cost = 3*first.length+1 := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [append,ih,List.length_cons]; omega

def push (log : Log) (input output : Input) : Run Log :=
  let decoded := digest output
  let joined := append log [(input,decoded.value)]
  ⟨joined.value,decoded.cost+joined.cost+4⟩

theorem push_value (log : Log) (input output : Input) :
    viewLog (push log input output).value = viewLog log++[⟨input,JointHashCache.decode output⟩] := by
  simp only [push,append_value,viewLog,List.map_append,List.map_cons,List.map_nil,digest_view]

theorem push_cost (log : Log) (input output : Input) : (push log input output).cost ≤ 3*log.length+264 := by
  have decoded := digest_cost output
  simp only [push,append_cost]
  omega
end FormalProof4FHE.HasteBoots.StoredHashLogCost
