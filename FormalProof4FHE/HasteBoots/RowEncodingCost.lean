module
public import FormalProof4FHE.HasteBoots.IntegerEncodingCost
public import FormalProof4FHE.HasteBoots.NativeLookupRequestWire
@[expose] public section

/-! Measured native row serialization, including length discovery, per-word
encoding and copied list prefixes. No encoding callback is supplied by callers.
Charges are abstract byte/access/arithmetic/control operations. -/
namespace FormalProof4FHE.HasteBoots.RowEncodingCost
open InputIndexedOracle (Input)
open NativeUsizeMessage (Usize)
open NativeLookupRequestWire (Row)
open SolverOperationCost (Run)

def length {A : Type} : List A → Run ℕ
  | [] => ⟨0,1⟩
  | _::tail =>
    let rest := length tail
    ⟨rest.value+1,rest.cost+3⟩

theorem length_value {A : Type} (values : List A) : (length values).value = values.length := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp only [length,List.length_cons,ih]

theorem length_cost {A : Type} (values : List A) : (length values).cost = 3*values.length+1 := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp only [length,List.length_cons,ih]; omega

def append : Input → Input → Run Input
  | [],last => ⟨last,1⟩
  | head::tail,last =>
    let rest := append tail last
    ⟨head::rest.value,rest.cost+3⟩

theorem append_value (first last : Input) : (append first last).value = first++last := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [append,List.cons_append,ih]

theorem append_cost (first last : Input) : (append first last).cost = 3*first.length+1 := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [append,List.length_cons,ih]; omega

def words : List Usize → Run Input
  | [] => ⟨[],1⟩
  | head::tail =>
    let first := IntegerEncodingCost.encode head
    let rest := words tail
    let joined := append first.value rest.value
    ⟨joined.value,first.cost+rest.cost+joined.cost+5⟩

theorem words_value (values : List Usize) :
    (words values).value = values.flatMap NativeUsizeMessage.encode := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp only [words,append_value,IntegerEncodingCost.encode_value,List.flatMap_cons,ih]

theorem words_cost (values : List Usize) : (words values).cost ≤ 92*values.length+1 := by
  induction values with
  | nil => simp [words]
  | cons head tail ih =>
    have encoded := IntegerEncodingCost.encode_cost head
    have size := IntegerEncodingCost.encode_length head
    simp only [words,append_cost,List.length_cons]
    omega

theorem words_length (values : List Usize) : (words values).value.length ≤ 9*values.length := by
  induction values with
  | nil => simp [words]
  | cons head tail ih =>
    have size := IntegerEncodingCost.encode_length head
    simp only [words,append_value,List.length_append,List.length_cons]
    omega

def encode (row : Row) : Run Input :=
  let count := length row.val
  let header := IntegerEncodingCost.encode ⟨count.value,by rw [length_value]; exact row.property⟩
  let body := words row.val
  let joined := append header.value body.value
  ⟨joined.value,count.cost+header.cost+body.cost+joined.cost+4⟩

theorem encode_value (row : Row) :
    (encode row).value = NativeLookupRequestWire.rowCodec.encode row := by
  simp only [encode,append_value,IntegerEncodingCost.encode_value,length_value,words_value,
    NativeLookupRequestWire.rowCodec,NativePrefixCodec.vector,NativePrefixCodec.usize]

theorem encode_cost (row : Row) : (encode row).cost ≤ 95*row.val.length+93 := by
  have header := IntegerEncodingCost.encode_cost
    (⟨(length row.val).value,by rw [length_value]; exact row.property⟩ : Usize)
  have headerSize := IntegerEncodingCost.encode_length
    (⟨(length row.val).value,by rw [length_value]; exact row.property⟩ : Usize)
  have body := words_cost row.val
  simp only [encode,length_cost,append_cost]
  omega

theorem encode_length (row : Row) : (encode row).value.length ≤ 9*(row.val.length+1) := by
  have header := IntegerEncodingCost.encode_length
    (⟨(length row.val).value,by rw [length_value]; exact row.property⟩ : Usize)
  have body := words_length row.val
  simp only [encode,append_value,List.length_append]
  omega
end FormalProof4FHE.HasteBoots.RowEncodingCost
