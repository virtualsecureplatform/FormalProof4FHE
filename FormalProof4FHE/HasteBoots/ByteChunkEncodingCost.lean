module
public import FormalProof4FHE.HasteBoots.RowEncodingCost
public import FormalProof4FHE.HasteBoots.NativeByteCodec
@[expose] public section

/-! Measured raw-byte vector encoding and concatenation of stored byte chunks.
Byte bodies are existing immutable lists; prefix copies and every concatenation
are charged. No serializer/byte callback executes in these operations. -/
namespace FormalProof4FHE.HasteBoots.ByteChunkEncodingCost
open InputIndexedOracle (Input Byte)
open SolverOperationCost (Run)

def bytes (value : NativePrefixCodec.Vector Byte) : Run Input :=
  let count := RowEncodingCost.length value.val
  let header := IntegerEncodingCost.encode ⟨count.value,by rw [RowEncodingCost.length_value]; exact value.property⟩
  let joined := RowEncodingCost.append header.value value.val
  ⟨joined.value,count.cost+header.cost+joined.cost+3⟩

theorem bytes_value (value : NativePrefixCodec.Vector Byte) : (bytes value).value = NativeByteCodec.bytes.encode value := by
  simp only [bytes,RowEncodingCost.append_value,IntegerEncodingCost.encode_value,
    RowEncodingCost.length_value,NativeByteCodec.bytes_encode]

theorem bytes_cost (value : NativePrefixCodec.Vector Byte) : (bytes value).cost ≤ 3*value.val.length+91 := by
  have encoded := IntegerEncodingCost.encode_cost
    (⟨(RowEncodingCost.length value.val).value,by rw [RowEncodingCost.length_value]; exact value.property⟩ : NativeUsizeMessage.Usize)
  have size := IntegerEncodingCost.encode_length
    (⟨(RowEncodingCost.length value.val).value,by rw [RowEncodingCost.length_value]; exact value.property⟩ : NativeUsizeMessage.Usize)
  simp only [bytes,RowEncodingCost.length_cost,RowEncodingCost.append_cost]
  omega

theorem bytes_size (value : NativePrefixCodec.Vector Byte) : (bytes value).value.length ≤ value.val.length+9 := by
  have size := IntegerEncodingCost.encode_length
    (⟨(RowEncodingCost.length value.val).value,by rw [RowEncodingCost.length_value]; exact value.property⟩ : NativeUsizeMessage.Usize)
  simp only [bytes,RowEncodingCost.append_value,List.length_append]
  omega

def chunkBytes : List Input → ℕ
  | [] => 0
  | head::tail => head.length+chunkBytes tail

def concat : List Input → Run Input
  | [] => ⟨[],1⟩
  | head::tail =>
    let rest := concat tail
    let joined := RowEncodingCost.append head rest.value
    ⟨joined.value,rest.cost+joined.cost+3⟩

theorem concat_value (chunks : List Input) : (concat chunks).value = chunks.flatten := by
  induction chunks with
  | nil => rfl
  | cons head tail ih => simp only [concat,RowEncodingCost.append_value,List.flatten_cons,ih]

theorem concat_size (chunks : List Input) : (concat chunks).value.length = chunkBytes chunks := by
  induction chunks with
  | nil => rfl
  | cons head tail ih => simp only [concat,RowEncodingCost.append_value,List.length_append,chunkBytes,ih]

theorem concat_cost (chunks : List Input) : (concat chunks).cost = 3*chunkBytes chunks+4*chunks.length+1 := by
  induction chunks with
  | nil => rfl
  | cons head tail ih => simp only [concat,RowEncodingCost.append_cost,ih,chunkBytes,List.length_cons]; omega
end FormalProof4FHE.HasteBoots.ByteChunkEncodingCost
