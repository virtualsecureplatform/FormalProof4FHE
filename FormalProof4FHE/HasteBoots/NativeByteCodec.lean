module

public import FormalProof4FHE.HasteBoots.NativePrefixCodec
public import FormalProof4FHE.HasteBoots.NativeRootMessage

@[expose] public section

/-! Raw serde u8 and fixed-size digest bytes have no integer or vector
headers. This supplies structural prefix readers, not a native strict decoder. -/
namespace FormalProof4FHE.HasteBoots.NativeByteCodec

open InputIndexedOracle (Byte Input)
open NativePrefixCodec (Codec)

def byte : Codec Byte where
  encode := fun value => [value]
  read := fun bytes => match bytes with | [] => none | value :: tail => some (value,tail)
  read_encode := fun _ _ => rfl

def bytes : Codec (NativePrefixCodec.Vector Byte) := NativePrefixCodec.vector byte

theorem bytes_encode (value : NativePrefixCodec.Vector Byte) : bytes.encode value =
    NativeUsizeMessage.encode ⟨value.val.length,value.property⟩ ++ value.val := by
  simp only [bytes,NativePrefixCodec.vector,byte,List.flatMap_singleton',NativePrefixCodec.usize]

/-- Arrays of u8 serialize without a length prefix. -/
def fixed (count : ℕ) : Codec (Fin count → Byte) where
  encode := List.ofFn
  read := fun input =>
    if length : (input.take count).length = count then
      some ((fun index => (input.take count)[index.val]'(by rw [length]; exact index.isLt)),input.drop count)
    else none
  read_encode := by
    intro value suffix
    have take : (List.ofFn value ++ suffix).take count = List.ofFn value := by simp
    have drop : (List.ofFn value ++ suffix).drop count = suffix := by simp
    simp only [take,List.length_ofFn,dite_true,drop,List.getElem_ofFn]

def digest : Codec NativeRootMessage.Digest := fixed 64

theorem digest_encode (value : NativeRootMessage.Digest) : digest.encode value = List.ofFn value := rfl

theorem digest_prefix (value : NativeRootMessage.Digest) (suffix : Input) :
    digest.read (digest.encode value ++ suffix) = some (value,suffix) := digest.read_encode _ _

end FormalProof4FHE.HasteBoots.NativeByteCodec
