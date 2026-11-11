module
import all FormalProof4FHE.HasteBoots.FramedIdentityWork

namespace HasteBootsScalarFramingSmoke
open FormalProof4FHE.HasteBoots
open NativeScalarBatchWire NativeScalarBatchPreflight NativePrefixCodec

def usize (value : ℕ) (fits : value < 2^64 := by omega) : NativeUsizeMessage.Usize := ⟨value, fits⟩

theorem varint_boundaries :
    ([usize 250, usize 251, usize 65535, usize 65536, usize 4294967295, usize 4294967296].map
      (fun value => (NativeUsizeMessage.encode value).length)) =
      [1, 3, 3, 5, 5, 9] := by decide +kernel

def message : Message := ⟨⟨[], by decide⟩⟩
def proof : Proof := ⟨[⟨[message, message], by decide⟩,
  ⟨[message, message, message], by decide⟩], by decide⟩
def packet : RoundPacket := ⟨usize 1, ⟨[message, message], by decide⟩⟩

theorem extracted : NativeScalarBatchRoundPacket.packet (usize 1) proof = some packet := by decide +kernel

theorem encoded_lengths : (ScalarProofFraming.proofCodec.encode proof).length = 8 ∧
    (roundCodec.encode packet).length = 4 := by decide +kernel

theorem missing_round : NativeScalarBatchRoundPacket.packet (usize 2) proof = none := by decide +kernel

-- The nonempty hypothesis in packet_length_le cannot be omitted.
def emptyProof : Proof := ⟨[], by decide⟩
def emptyPacket : RoundPacket := ⟨usize 0, ⟨[], by decide⟩⟩
theorem empty_exception : NativeScalarBatchRoundPacket.packet (usize 0) emptyProof = some emptyPacket ∧
    (ScalarProofFraming.proofCodec.encode emptyProof).length <
      (roundCodec.encode emptyPacket).length := by decide +kernel

def proofBytes : Vector InputIndexedOracle.Byte :=
  ⟨ScalarProofFraming.proofCodec.encode proof, by decide +kernel⟩

theorem bounded_source_domain : NativeScalarTranscriptExtension.RoundDomain proof :=
  ScalarProofFraming.roundDomain_of_bytes proof (by decide +kernel) proofBytes
    (NativeExactCodec.read_encode ScalarProofFraming.proofCodec proof)

theorem trailing_byte_rejected :
    NativeExactCodec.read ScalarProofFraming.proofCodec (proofBytes.val ++ [0]) = none := by decide +kernel

end HasteBootsScalarFramingSmoke
