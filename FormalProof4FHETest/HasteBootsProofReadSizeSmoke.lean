module
import all FormalProof4FHE.HasteBoots.DecodedIdentityWork
import all FormalProof4FHETest.HasteBootsSharedProofBytesSmoke

namespace HasteBootsProofReadSizeSmoke
open FormalProof4FHE.HasteBoots
open HasteBootsSharedProofBytesSmoke (proof wire)
open SharedProofByteCodec (codec)
open InputIndexedOracle (Input Byte)
open NativePrefixCodec (Vector)

-- Fingerprint equality identifies the entire original proof, not only its dimensions.
theorem parsed_of_encoding (input : Input) (rest : Input)
    (computed : (codec.read input).map (fun pair => (codec.encode pair.1,pair.2)) = some (wire,rest)) :
    codec.read input = some (proof,rest) := by
  obtain ⟨⟨actual,tail⟩,found,same⟩ := Option.map_eq_some_iff.mp computed
  have pair := Prod.mk.inj same
  have equal : actual = proof := codec.encode_injective pair.1
  have terminal : tail = rest := pair.2
  rw [equal,terminal] at found
  exact found

def wider : Input := [251,2,0] ++ wire.drop 1

theorem wider_read : codec.read wider = some (proof,[]) :=
  parsed_of_encoding wider [] (by decide +kernel)

theorem nested_wider_read : codec.read (wire.take 1 ++ [251,1,0] ++ wire.drop 2) = some (proof,[]) :=
  parsed_of_encoding _ [] (by decide +kernel)

theorem wider_extension_degree : codec.read (wire.take 81 ++ [251,3,0] ++ wire.drop 82) = some (proof,[]) :=
  parsed_of_encoding _ [] (by decide +kernel)

theorem integer_wide_read :
    (NativePrefixCodec.usize.read [252,2,0,0,0]).map (fun pair => (pair.1.val,pair.2)) = some (2,[]) ∧
    (NativePrefixCodec.usize.read [253,2,0,0,0,0,0,0,0]).map (fun pair => (pair.1.val,pair.2)) = some (2,[]) := by decide +kernel

theorem wider_with_suffix : codec.read (wider ++ [99,100]) = some (proof,[99,100]) :=
  parsed_of_encoding _ [99,100] (by decide +kernel)

theorem full_wider_read : SharedProofReadSize.readAll wider = some proof :=
  (SharedProofReadSize.readAll_iff wider proof).mpr wider_read

theorem full_trailing_rejected : (SharedProofReadSize.readAll (wider ++ [99,100])).isNone = true := by decide +kernel

theorem full_truncated_rejected : (SharedProofReadSize.readAll wider.dropLast).isNone = true := by decide +kernel

theorem canonical_shrinks : (codec.encode proof).length = 106 ∧ wider.length = 108 := by decide +kernel

def source : Vector Byte := ⟨wider ++ [99,100],by decide +kernel⟩

theorem original_suffix_paid : (codec.encode proof).length + ([99,100] : Input).length ≤ source.val.length :=
  SharedProofReadSize.proof source.val proof [99,100] wider_with_suffix

theorem canonical_source_exists : ∃ canonical : Vector Byte,
    NativeExactCodec.read codec canonical.val = some proof :=
  SharedProofReadSize.canonical_source source proof [99,100] wider_with_suffix

theorem decoded_domains : SharedProofSerializationDomain.Domain proof :=
  SharedProofSerializationDomain.of_length proof (by decide +kernel)
    (SharedProofReadSize.canonical_fits source proof [99,100] wider_with_suffix)

-- Invalid u64 tags stay failures; the size proof does not canonicalize them into successes.
theorem invalid_tag_rejected : (codec.read ([254] ++ wire.drop 1)).isNone = true := by decide +kernel

end HasteBootsProofReadSizeSmoke
