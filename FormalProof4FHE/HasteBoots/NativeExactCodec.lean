module

public import FormalProof4FHE.HasteBoots.NativeByteCodec
@[expose] public section

/-! Exact structural input views from existing native prefix codecs. A read
accepts only with no trailing bytes and identical canonical reencoding. This
is an analysis parser, not a refinement of the native proof deserializer. -/
namespace FormalProof4FHE.HasteBoots.NativeExactCodec
open InputIndexedOracle (Input)
open NativePrefixCodec (Codec)

def read {A : Type} (codec : Codec A) (input : Input) : Option A :=
  (codec.read input).bind (fun result =>
    if result.2 = [] ∧ codec.encode result.1 = input then some result.1 else none)

theorem read_encode {A : Type} (codec : Codec A) (value : A) :
    read codec (codec.encode value) = some value := by
  have parsed := codec.read_encode value []
  rw [List.append_nil] at parsed
  simp [read,parsed]

theorem read_sound {A : Type} (codec : Codec A) (input : Input) (value : A)
    (parsed : read codec input = some value) : codec.encode value = input := by
  unfold read at parsed
  cases first : codec.read input with
  | none => simp [first] at parsed
  | some result =>
    simp only [first,Option.bind_some] at parsed
    split at parsed
    · rename_i accepted
      have same := Option.some.inj parsed
      rw [← same]
      exact accepted.2
    · simp at parsed

theorem read_iff {A : Type} (codec : Codec A) (input : Input) (value : A) :
    read codec input = some value ↔ codec.encode value = input := by
  constructor
  · exact read_sound codec input value
  · intro same
    rw [← same]
    exact read_encode codec value

end FormalProof4FHE.HasteBoots.NativeExactCodec
