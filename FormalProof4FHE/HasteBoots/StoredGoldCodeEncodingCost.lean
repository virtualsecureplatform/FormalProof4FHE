module
public import FormalProof4FHE.HasteBoots.ByteChunkEncodingCost
public import FormalProof4FHE.HasteBoots.NativeGoldBlockCodeContext
@[expose] public section

/-! Complete retained Gold block-code serialization. Every declared field,
including padded message blocks, retained modulus bytes and raw domain root,
is serialized in original order with charged encoding and copying. -/
namespace FormalProof4FHE.HasteBoots.StoredGoldCodeEncodingCost
open InputIndexedOracle (Input)
open SolverOperationCost (Run)
open NativeGoldBlockCode (Stored)

def encode (code : Stored) : Run Input :=
  let message := IntegerEncodingCost.encode code.messageLength
  let block := IntegerEncodingCost.encode code.blockWidth
  let padded := IntegerEncodingCost.encode code.messageBlocks
  let count := IntegerEncodingCost.encode code.blocks
  let modulus := ByteChunkEncodingCost.bytes code.modulus
  let root := IntegerEncodingCost.encode code.domainRoot
  let joined := ByteChunkEncodingCost.concat [message.value,block.value,padded.value,count.value,modulus.value,root.value]
  ⟨joined.value,message.cost+block.cost+padded.cost+count.cost+modulus.cost+root.cost+joined.cost+7⟩

theorem encode_value (code : Stored) : (encode code).value = NativeGoldBlockCode.codec.encode code := by
  simp only [encode,ByteChunkEncodingCost.concat_value,List.flatten_cons,List.flatten_nil,List.append_nil,
    IntegerEncodingCost.encode_value,ByteChunkEncodingCost.bytes_value,NativeGoldBlockCode.serialize_fields,NativeFieldWire.gold]

theorem encode_size (code : Stored) : (encode code).value.length ≤ code.modulus.val.length+54 := by
  have message := IntegerEncodingCost.encode_length code.messageLength
  have block := IntegerEncodingCost.encode_length code.blockWidth
  have padded := IntegerEncodingCost.encode_length code.messageBlocks
  have count := IntegerEncodingCost.encode_length code.blocks
  have modulus := ByteChunkEncodingCost.bytes_size code.modulus
  have root := IntegerEncodingCost.encode_length code.domainRoot
  simp only [encode,ByteChunkEncodingCost.concat_size,ByteChunkEncodingCost.chunkBytes]
  omega

theorem encode_cost (code : Stored) : (encode code).cost ≤ 6*code.modulus.val.length+600 := by
  have message := IntegerEncodingCost.encode_cost code.messageLength
  have block := IntegerEncodingCost.encode_cost code.blockWidth
  have padded := IntegerEncodingCost.encode_cost code.messageBlocks
  have count := IntegerEncodingCost.encode_cost code.blocks
  have modulus := ByteChunkEncodingCost.bytes_cost code.modulus
  have root := IntegerEncodingCost.encode_cost code.domainRoot
  have messageSize := IntegerEncodingCost.encode_length code.messageLength
  have blockSize := IntegerEncodingCost.encode_length code.blockWidth
  have paddedSize := IntegerEncodingCost.encode_length code.messageBlocks
  have countSize := IntegerEncodingCost.encode_length code.blocks
  have modulusSize := ByteChunkEncodingCost.bytes_size code.modulus
  have rootSize := IntegerEncodingCost.encode_length code.domainRoot
  simp only [encode,ByteChunkEncodingCost.concat_cost,ByteChunkEncodingCost.chunkBytes,List.length_cons,List.length_nil]
  omega
end FormalProof4FHE.HasteBoots.StoredGoldCodeEncodingCost
