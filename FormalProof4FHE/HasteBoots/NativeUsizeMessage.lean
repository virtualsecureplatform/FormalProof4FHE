module

public import FormalProof4FHE.HasteBoots.TranscriptFrame

@[expose] public section

/-!
# Standard bincode unsigned messages for the native 64-bit target

`Transcript::append_message` uses bincode 2.0.1 standard (variable integer,
little endian) serialization. Serde serializes usize as u64. This models
that byte format for request ordinals; checked Rust/serde correspondence
remains part of the source refinement gate.
-/

namespace FormalProof4FHE.HasteBoots.NativeUsizeMessage

open InputIndexedOracle (Input Byte)
open TranscriptFrame (littleEndian fromLittleEndian)

abbrev Usize := Fin (2 ^ 64)

def encode (value : Usize) : Input :=
  if small : value.val < 251 then [⟨value.val, by omega⟩]
  else if value.val < 2 ^ 16 then 251 :: littleEndian 2 value.val
  else if value.val < 2 ^ 32 then 252 :: littleEndian 4 value.val
  else 253 :: littleEndian 8 value.val

/-- Structural numeral reader; acceptance of noncanonical wider encodings
is not a strict proof-byte decoder. -/
def read : Input → Option ℕ
  | [] => none
  | tag :: tail =>
    if tag.val < 251 then if tail.isEmpty then some tag.val else none
    else if tag = 251 then if tail.length = 2 then some (fromLittleEndian tail) else none
    else if tag = 252 then if tail.length = 4 then some (fromLittleEndian tail) else none
    else if tag = 253 then if tail.length = 8 then some (fromLittleEndian tail) else none
    else none

theorem read_encode (value : Usize) : read (encode value) = some value.val := by
  unfold encode
  split
  · rename_i small
    simp only [read, small, List.isEmpty_nil, ↓reduceIte]
  · split
    · rename_i fits
      simp only [read, show ¬(251 : Byte).val < 251 by decide, ite_false,
        ite_true, TranscriptFrame.littleEndian_length]
      rw [TranscriptFrame.fromLittleEndian_littleEndian 2 value.val (by norm_num at fits ⊢; exact fits)]
    · split
      · rename_i fits
        simp only [read, show ¬(252 : Byte).val < 251 by decide, ite_false,
          show (252 : Byte) ≠ 251 by decide, ite_true, TranscriptFrame.littleEndian_length]
        rw [TranscriptFrame.fromLittleEndian_littleEndian 4 value.val (by norm_num at fits ⊢; exact fits)]
      · simp only [read, show ¬(253 : Byte).val < 251 by decide, ite_false,
          show (253 : Byte) ≠ 251 by decide, show (253 : Byte) ≠ 252 by decide,
          ite_true, TranscriptFrame.littleEndian_length]
        rw [TranscriptFrame.fromLittleEndian_littleEndian 8 value.val (by
          have fits := value.isLt
          norm_num at fits ⊢
          exact fits)]

theorem encode_injective : Function.Injective encode := by
  intro left right same
  apply Fin.ext
  have equal := congrArg read same
  rw [read_encode, read_encode] at equal
  exact Option.some.inj equal

theorem encode_length (value : Usize) : (encode value).length ≤ 9 := by
  unfold encode
  split
  · simp only [List.length_cons, List.length_nil]
    omega
  · split
    · simp only [List.length_cons, TranscriptFrame.littleEndian_length]
      omega
    · split <;> simp only [List.length_cons, TranscriptFrame.littleEndian_length] <;> omega


end FormalProof4FHE.HasteBoots.NativeUsizeMessage
