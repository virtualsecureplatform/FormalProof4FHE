module
public import FormalProof4FHE.HasteBoots.SolverOperationCost
public import FormalProof4FHE.HasteBoots.TranscriptFrame
@[expose] public section

/-! Measured byte-prefix extraction and little-endian arithmetic. Charges count
explicit byte/list accesses, stores, arithmetic and control in an abstract model.
A forged requested width stops when the supplied bytes end. Physical execution
and native integer/backend refinement are separate obligations. -/
namespace FormalProof4FHE.HasteBoots.BytePrefixCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)

def takeExact : ℕ → Input → Run (Option (Input × Input))
  | 0,bytes => ⟨some ([],bytes),1⟩
  | _+1,[] => ⟨none,1⟩
  | count+1,head::tail =>
    let rest := takeExact count tail
    ⟨rest.value.map (fun pair => (head::pair.1,pair.2)),rest.cost+5⟩

theorem takeExact_value (count : ℕ) (bytes : Input) :
    (takeExact count bytes).value =
      if count ≤ bytes.length then some (bytes.take count,bytes.drop count) else none := by
  induction count generalizing bytes with
  | zero => simp [takeExact]
  | succ count ih =>
    cases bytes with
    | nil => simp [takeExact]
    | cons head tail =>
      simp only [takeExact,ih,List.length_cons,Nat.succ_le_succ_iff,List.take_succ_cons,List.drop_succ_cons]
      split <;> simp

theorem takeExact_cost (count : ℕ) (bytes : Input) :
    (takeExact count bytes).cost = 5*min count bytes.length+1 := by
  induction count generalizing bytes with
  | zero => simp [takeExact]
  | succ count ih =>
    cases bytes with
    | nil => simp [takeExact]
    | cons head tail =>
      simp only [takeExact,List.length_cons,ih]
      omega

theorem takeExact_append (first rest : Input) :
    (takeExact first.length (first++rest)).value = some (first,rest) := by
  simp [takeExact_value]

def fromLittleEndian : Input → Run ℕ
  | [] => ⟨0,1⟩
  | head::tail =>
    let rest := fromLittleEndian tail
    ⟨head.val+256*rest.value,rest.cost+5⟩

theorem fromLittleEndian_value (bytes : Input) :
    (fromLittleEndian bytes).value = TranscriptFrame.fromLittleEndian bytes := by
  induction bytes with
  | nil => rfl
  | cons head tail ih => simp only [fromLittleEndian,TranscriptFrame.fromLittleEndian,ih]

theorem fromLittleEndian_cost (bytes : Input) :
    (fromLittleEndian bytes).cost = 5*bytes.length+1 := by
  induction bytes with
  | nil => rfl
  | cons head tail ih => simp only [fromLittleEndian,List.length_cons,ih]; omega

def readWide (count : ℕ) (bytes : Input) : Run (Option (ℕ × Input)) :=
  let chunk := takeExact count bytes
  match chunk.value with
  | none => ⟨none,chunk.cost+2⟩
  | some (first,rest) =>
    let value := fromLittleEndian first
    ⟨some (value.value,rest),chunk.cost+value.cost+3⟩

theorem readWide_value (count : ℕ) (bytes : Input) :
    (readWide count bytes).value =
      if count ≤ bytes.length then
        some (TranscriptFrame.fromLittleEndian (bytes.take count),bytes.drop count) else none := by
  by_cases enough : count ≤ bytes.length <;>
    simp [readWide,takeExact_value,enough,fromLittleEndian_value]

theorem readWide_cost (count : ℕ) (bytes : Input) :
    (readWide count bytes).cost ≤ 10*min count bytes.length+5 := by
  by_cases enough : count ≤ bytes.length
  · simp only [readWide,takeExact_value,enough,ite_true,takeExact_cost,
      fromLittleEndian_cost,List.length_take]
    omega
  · simp only [readWide,takeExact_value,enough,ite_false,takeExact_cost]
    omega
end FormalProof4FHE.HasteBoots.BytePrefixCost
