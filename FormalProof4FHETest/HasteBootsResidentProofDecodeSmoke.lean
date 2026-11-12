module
import all FormalProof4FHE.HasteBoots.HeapProofIdentityWork
import all FormalProof4FHETest.HasteBootsResidentMessageBoundsSmoke
import all FormalProof4FHETest.HasteBootsProofReadSizeSmoke

namespace HasteBootsResidentProofDecodeSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsSharedProofBytesSmoke (proof wire)
open HasteBootsProofReadSizeSmoke (wider wider_with_suffix)
open HasteBootsResidentMessageBoundsSmoke (allocateWrite buffer)
open SharedProofByteCodec (codec)
open InputIndexedOracle (Input)

def bytes : Input := wider ++ [99,100]
theorem allocated : (allocateWrite bytes).isSome = true := by decide +kernel

def proofBuffer := buffer bytes allocated

theorem actual_read : ResidentProofDecode.read proofBuffer.memory proofBuffer.pointer proofBuffer.layout = some (proof,[99,100]) :=
  (ResidentProofDecode.read_iff _ _ _ _ _).mpr ⟨bytes,proofBuffer.loaded,wider_with_suffix⟩

noncomputable def recovered := ResidentProofDecode.recover proofBuffer.memory proofBuffer.pointer proofBuffer.layout proof [99,100] actual_read

theorem original_bytes : recovered.bytes = bytes := recovered.original_bytes bytes proofBuffer.loaded

theorem original_vector : recovered.vector.val = bytes := original_bytes

theorem wider_spelling_and_suffix_retained : recovered.bytes.take 3 = [251,2,0] ∧ recovered.bytes.drop 108 = [99,100] := by
  rw [original_bytes]
  decide +kernel

theorem consumed_bound : (codec.encode proof).length + ([99,100] : Input).length ≤ proofBuffer.layout.size :=
  recovered.consumed_bound

theorem canonical_is_smaller : (codec.encode proof).length < recovered.bytes.length := by
  rw [original_bytes]
  decide +kernel

theorem raw_lazy_word_retained : proof.multiplicities.flat.val.map Fin.val = [0,2^64-1] := by decide +kernel

theorem lost_provenance_rejected :
    ResidentProofDecode.read proofBuffer.memory ⟨proofBuffer.pointer.address,none⟩ proofBuffer.layout = none :=
  ResidentProofDecode.failed_load _ _ _ (NativeByteRange.positive_without_origin _ _ _ (by decide +kernel) rfl)

def invalidBytes : Input := [254] ++ wire.drop 1
theorem invalid_allocated : (allocateWrite invalidBytes).isSome = true := by decide +kernel

def invalidBuffer := buffer invalidBytes invalid_allocated

theorem invalid_tag_rejected : (ResidentProofDecode.read invalidBuffer.memory invalidBuffer.pointer invalidBuffer.layout).isNone = true := by
  rw [ResidentProofDecode.read,invalidBuffer.loaded,Option.bind_some]
  exact HasteBootsProofReadSizeSmoke.invalid_tag_rejected

def truncatedBytes : Input := wire.dropLast
theorem truncated_allocated : (allocateWrite truncatedBytes).isSome = true := by decide +kernel

def truncatedBuffer := buffer truncatedBytes truncated_allocated

theorem truncated_proof_rejected : (ResidentProofDecode.read truncatedBuffer.memory truncatedBuffer.pointer truncatedBuffer.layout).isNone = true := by
  rw [ResidentProofDecode.read,truncatedBuffer.loaded,Option.bind_some]
  decide +kernel

end HasteBootsResidentProofDecodeSmoke
