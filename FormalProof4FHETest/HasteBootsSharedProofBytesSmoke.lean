module
import all FormalProof4FHE.HasteBoots.SerializedIdentityWork

namespace HasteBootsSharedProofBytesSmoke
open FormalProof4FHE.HasteBoots
open NativePrefixCodec (Vector)
open InputIndexedOracle (Byte)
open SharedProofByteCodec (codec)

-- Keep the raw lazy u64 spelling, including a word above the field modulus.
def maxWord : NativeFieldRepresentation.GoldWord := ⟨2^64-1,by omega⟩
def zeroRow : NativeLookupRequestWire.Row := ⟨[0],by decide⟩
def extension : NativeFieldWire.GoldExtension := fun _ => 0
def sourceOpening : NativeGoldBatchOpening.Opening := ⟨zeroRow,⟨[zeroRow],by decide⟩,⟨[],by decide⟩⟩
def helperOpening : NativeGoldPcsOpening.Opening := ⟨zeroRow,zeroRow,⟨[],by decide⟩⟩
def message : NativeScalarBatchWire.Message := ⟨⟨[extension],by decide⟩⟩
def proof : SharedProofByteCodec.Proof :=
  ⟨⟨⟨[zeroRow,⟨[maxWord],by decide⟩],by decide⟩,by decide⟩,
    ⟨[fun _ => 7],by decide⟩,⟨[⟨[message],by decide⟩],by decide⟩,
    ⟨[zeroRow],by decide⟩,⟨[extension],by decide⟩,
    ⟨[sourceOpening],by decide⟩,⟨[helperOpening],by decide⟩⟩

def wire : InputIndexedOracle.Input := codec.encode proof

theorem seven_field_wire : wire =
    [2,1,0,1,253] ++ List.replicate 8 255 ++
    [1] ++ List.replicate 64 7 ++ [1,1,1,3,0,0,0] ++
    [1,1,0] ++ [1,3,0,0,0] ++ [1,1,0,1,1,0,0] ++ [1,1,0,1,0,0] := by decide +kernel

theorem encoded_sizes : wire.length = 106 ∧
    (NativeLookupMultiplicityWire.grouped proof.multiplicities).length = 13 ∧
    (NativeLookupMultiplicityWire.flattened proof.multiplicities).length = 11 := by decide +kernel

theorem raw_word_retained :
    (NativeExactCodec.read codec wire).map (fun parsed => parsed.multiplicities.flat.val.map Fin.val) =
      some [0,2^64-1] := by
  rw [wire,SharedProofByteCodec.exact_read]
  decide +kernel

theorem prefix_roundtrip : codec.read (wire ++ [99]) = some (proof,[99]) :=
  SharedProofByteCodec.read_prefix proof [99]

theorem trailing_rejected : (NativeExactCodec.read codec (wire ++ [99])).isNone = true := by decide +kernel

theorem truncated_rejected : (NativeExactCodec.read codec wire.dropLast).isNone = true := by decide +kernel

-- Structural wider prefixes cannot masquerade as the canonical exact byte view.
theorem wider_prefix_rejected :
    (NativeExactCodec.read codec ([251,2,0] ++ wire.drop 1)).isNone = true := by decide +kernel

-- The 2^32 count transition can outgrow the old outer/row headers.
-- No multi-billion-element test value is allocated to check this arithmetic.
theorem flatten_header_growth :
    (NativeUsizeMessage.encode ⟨2^32,by decide⟩).length >
      (NativeUsizeMessage.encode ⟨2,by decide⟩).length +
      (NativeUsizeMessage.encode ⟨2^32-1,by decide⟩).length +
      (NativeUsizeMessage.encode ⟨1,by decide⟩).length := by decide +kernel

def proofBytes : Vector Byte := ⟨wire,by decide +kernel⟩

theorem shared_domain : SharedProofSerializationDomain.Domain proof :=
  SharedProofSerializationDomain.of_bytes proof (by decide +kernel) proofBytes (SharedProofByteCodec.exact_read proof)

theorem opening_response_domains :
    (NativeGoldBatchResponseBinding.payload sourceOpening).length < TranscriptFrame.lengthLimit ∧
    (SingleOpeningColumnLaw.payload helperOpening).length < TranscriptFrame.lengthLimit :=
  ⟨shared_domain.sourceResponses sourceOpening (by simp [proof]),
    shared_domain.helperResponses helperOpening (by simp [proof])⟩

end HasteBootsSharedProofBytesSmoke
