module
public import FormalProof4FHE.HasteBoots.StoredGoldCodeEncodingCost
@[expose] public section

/-! Measured complete Gold parameter-context hash inputs from retained fields.
The outer modulus, every parameter/accessor field, code domain and complete code
object are retained. No row serialization accessor or encoder callback executes.
Structural input injectivity is not collision resistance or physical refinement. -/
namespace FormalProof4FHE.HasteBoots.StoredGoldContextEncodingCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)
abbrev Parameters := NativeBrakedownContext.Parameters NativeGoldBlockCode.Stored

def fixedBytes : ℕ := NativeBrakedownContext.modulus.val.length+NativeGoldBlockCode.domain.val.length

def metadata (parameters : Parameters) : Run Input :=
  let modulus := ByteChunkEncodingCost.bytes NativeBrakedownContext.modulus
  let variableCount := IntegerEncodingCost.encode parameters.numVariables
  let width := IntegerEncodingCost.encode parameters.width
  let left := IntegerEncodingCost.encode parameters.leftVariables
  let queries := IntegerEncodingCost.encode parameters.queries
  let block := IntegerEncodingCost.encode parameters.code.blockWidth
  let count := IntegerEncodingCost.encode parameters.code.blocks
  let domain := ByteChunkEncodingCost.bytes NativeGoldBlockCode.domain
  let code := StoredGoldCodeEncodingCost.encode parameters.code
  let joined := ByteChunkEncodingCost.concat [modulus.value,variableCount.value,width.value,left.value,
    queries.value,block.value,count.value,domain.value,code.value]
  ⟨joined.value,modulus.cost+variableCount.cost+width.cost+left.cost+queries.cost+block.cost+count.cost+
    domain.cost+code.cost+joined.cost+10⟩

theorem metadata_value (parameters : Parameters) :
    (metadata parameters).value = NativeGoldBlockCodeContext.contextCodec.encode (NativeGoldBlockCodeContext.contextFields parameters) := by
  simp only [metadata,ByteChunkEncodingCost.concat_value,List.flatten_cons,List.flatten_nil,List.append_nil,
    ByteChunkEncodingCost.bytes_value,IntegerEncodingCost.encode_value,StoredGoldCodeEncodingCost.encode_value,
    NativeGoldBlockCodeContext.contextCodec,NativeGoldBlockCodeContext.contextFields,NativePrefixCodec.product,
    NativePrefixCodec.usize]

theorem metadata_size (parameters : Parameters) :
    (metadata parameters).value.length ≤ parameters.code.modulus.val.length+fixedBytes+126 := by
  have modulus := ByteChunkEncodingCost.bytes_size NativeBrakedownContext.modulus
  have variableCount := IntegerEncodingCost.encode_length parameters.numVariables
  have width := IntegerEncodingCost.encode_length parameters.width
  have left := IntegerEncodingCost.encode_length parameters.leftVariables
  have queries := IntegerEncodingCost.encode_length parameters.queries
  have block := IntegerEncodingCost.encode_length parameters.code.blockWidth
  have count := IntegerEncodingCost.encode_length parameters.code.blocks
  have domain := ByteChunkEncodingCost.bytes_size NativeGoldBlockCode.domain
  have code := StoredGoldCodeEncodingCost.encode_size parameters.code
  simp only [metadata,ByteChunkEncodingCost.concat_size,ByteChunkEncodingCost.chunkBytes,fixedBytes]
  omega

theorem metadata_cost (parameters : Parameters) :
    (metadata parameters).cost ≤ 9*parameters.code.modulus.val.length+6*fixedBytes+1600 := by
  have modulus := ByteChunkEncodingCost.bytes_cost NativeBrakedownContext.modulus
  have variableCount := IntegerEncodingCost.encode_cost parameters.numVariables
  have width := IntegerEncodingCost.encode_cost parameters.width
  have left := IntegerEncodingCost.encode_cost parameters.leftVariables
  have queries := IntegerEncodingCost.encode_cost parameters.queries
  have block := IntegerEncodingCost.encode_cost parameters.code.blockWidth
  have count := IntegerEncodingCost.encode_cost parameters.code.blocks
  have domain := ByteChunkEncodingCost.bytes_cost NativeGoldBlockCode.domain
  have code := StoredGoldCodeEncodingCost.encode_cost parameters.code
  have modulusSize := ByteChunkEncodingCost.bytes_size NativeBrakedownContext.modulus
  have variablesSize := IntegerEncodingCost.encode_length parameters.numVariables
  have widthSize := IntegerEncodingCost.encode_length parameters.width
  have leftSize := IntegerEncodingCost.encode_length parameters.leftVariables
  have queriesSize := IntegerEncodingCost.encode_length parameters.queries
  have blockSize := IntegerEncodingCost.encode_length parameters.code.blockWidth
  have countSize := IntegerEncodingCost.encode_length parameters.code.blocks
  have domainSize := ByteChunkEncodingCost.bytes_size NativeGoldBlockCode.domain
  have codeSize := StoredGoldCodeEncodingCost.encode_size parameters.code
  simp only [metadata,ByteChunkEncodingCost.concat_cost,ByteChunkEncodingCost.chunkBytes,
    List.length_cons,List.length_nil,fixedBytes]
  omega

def input (parameters : Parameters) : Run Input :=
  let encoded := metadata parameters
  let joined := RowEncodingCost.append NativeBrakedownContext.domain encoded.value
  ⟨joined.value,encoded.cost+joined.cost+3⟩

theorem input_value (parameters : Parameters) :
    some (input parameters).value = NativeBrakedownContext.input NativeGoldBlockCode.description.row parameters := by
  rw [NativeGoldBlockCodeContext.input_computed]
  simp only [input,RowEncodingCost.append_value,metadata_value]

theorem input_size (parameters : Parameters) :
    (input parameters).value.length ≤ parameters.code.modulus.val.length+fixedBytes+
      NativeBrakedownContext.domain.length+126 := by
  have encoded := metadata_size parameters
  simp only [input,RowEncodingCost.append_value,List.length_append]
  omega

theorem input_cost (parameters : Parameters) :
    (input parameters).cost ≤ 9*parameters.code.modulus.val.length+6*fixedBytes+
      3*NativeBrakedownContext.domain.length+1604 := by
  have encoded := metadata_cost parameters
  simp only [input,RowEncodingCost.append_cost]
  omega

theorem input_injective : Function.Injective (fun parameters => (input parameters).value) := by
  intro first last same
  change (input first).value = (input last).value at same
  apply NativeGoldBlockCodeContext.input_injective
  rw [← input_value,← input_value,same]
end FormalProof4FHE.HasteBoots.StoredGoldContextEncodingCost
