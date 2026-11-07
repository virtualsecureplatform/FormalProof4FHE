module
public import FormalProof4FHE.HasteBoots.VectorWireReadCost
public import FormalProof4FHE.HasteBoots.RowEncodingCost
@[expose] public section

/-! Charged repeated-vector encoding. Every element's serialization, prefix
copy, length traversal and output construction is included. Public endpoints
instantiate concrete encoders; generic callback runtime is not assumed priced.
This is an abstract operation model, not physical/native refinement. -/
namespace FormalProof4FHE.HasteBoots.VectorWireEncodeCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)
open VectorWireReadCost (weight)
variable {A : Type}

def body (encoder : A → Run Input) : List A → Run Input
  | [] => ⟨[],1⟩
  | head::tail =>
    let first := encoder head
    let rest := body encoder tail
    let joined := RowEncodingCost.append first.value rest.value
    ⟨joined.value,first.cost+rest.cost+joined.cost+5⟩

theorem body_value (encoder : A → Run Input) (codec : NativePrefixCodec.Codec A)
    (correct : ∀ value, (encoder value).value = codec.encode value) (values : List A) :
    (body encoder values).value = values.flatMap codec.encode := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp only [body,RowEncodingCost.append_value,correct,List.flatMap_cons,ih]

theorem body_cost (encoder : A → Run Input) (entry : A → ℕ) (E : ℕ)
    (bounded : ∀ value, (encoder value).cost ≤ E*(entry value+1))
    (sized : ∀ value, (encoder value).value.length ≤ 9*(entry value+1)) (values : List A) :
    (body encoder values).cost ≤ (E+33)*weight entry values+1 := by
  induction values with
  | nil => simp [body,weight]
  | cons head tail ih =>
    have first := bounded head
    have size := sized head
    simp only [body,RowEncodingCost.append_cost,weight]
    nlinarith

theorem body_size (encoder : A → Run Input) (entry : A → ℕ)
    (sized : ∀ value, (encoder value).value.length ≤ 9*(entry value+1)) (values : List A) :
    (body encoder values).value.length ≤ 9*weight entry values := by
  induction values with
  | nil => simp [body,weight]
  | cons head tail ih =>
    have size := sized head
    simp only [body,RowEncodingCost.append_value,List.length_append,weight]
    omega

def encode (encoder : A → Run Input) (values : NativePrefixCodec.Vector A) : Run Input :=
  let count := RowEncodingCost.length values.val
  let header := IntegerEncodingCost.encode ⟨count.value,by rw [RowEncodingCost.length_value]; exact values.property⟩
  let bytes := body encoder values.val
  let joined := RowEncodingCost.append header.value bytes.value
  ⟨joined.value,count.cost+header.cost+bytes.cost+joined.cost+4⟩

theorem encode_value (encoder : A → Run Input) (codec : NativePrefixCodec.Codec A)
    (correct : ∀ value, (encoder value).value = codec.encode value) (values : NativePrefixCodec.Vector A) :
    (encode encoder values).value = (NativePrefixCodec.vector codec).encode values := by
  simp only [encode,RowEncodingCost.append_value,RowEncodingCost.length_value,IntegerEncodingCost.encode_value,
    body_value encoder codec correct,NativePrefixCodec.vector,NativePrefixCodec.usize]

theorem encode_cost (encoder : A → Run Input) (entry : A → ℕ) (E : ℕ)
    (bounded : ∀ value, (encoder value).cost ≤ E*(entry value+1))
    (sized : ∀ value, (encoder value).value.length ≤ 9*(entry value+1)) (values : NativePrefixCodec.Vector A) :
    (encode encoder values).cost ≤ (E+36)*weight entry values.val+93 := by
  have bytes := body_cost encoder entry E bounded sized values.val
  have count := VectorWireReadCost.length_le_weight entry values.val
  have header := IntegerEncodingCost.encode_cost
    (⟨(RowEncodingCost.length values.val).value,by rw [RowEncodingCost.length_value]; exact values.property⟩ : NativeUsizeMessage.Usize)
  have size := IntegerEncodingCost.encode_length
    (⟨(RowEncodingCost.length values.val).value,by rw [RowEncodingCost.length_value]; exact values.property⟩ : NativeUsizeMessage.Usize)
  simp only [encode,RowEncodingCost.length_cost,RowEncodingCost.append_cost]
  nlinarith

theorem encode_size (encoder : A → Run Input) (entry : A → ℕ)
    (sized : ∀ value, (encoder value).value.length ≤ 9*(entry value+1)) (values : NativePrefixCodec.Vector A) :
    (encode encoder values).value.length ≤ 9*(weight entry values.val+1) := by
  have bytes := body_size encoder entry sized values.val
  have header := IntegerEncodingCost.encode_length
    (⟨(RowEncodingCost.length values.val).value,by rw [RowEncodingCost.length_value]; exact values.property⟩ : NativeUsizeMessage.Usize)
  simp only [encode,RowEncodingCost.append_value,List.length_append]
  omega
end FormalProof4FHE.HasteBoots.VectorWireEncodeCost
