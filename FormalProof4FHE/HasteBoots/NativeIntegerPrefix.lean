module

public import FormalProof4FHE.HasteBoots.NativeUsizeMessage

@[expose] public section

/-!
# Self-delimiting unsigned transcript integers

This structural parser is a left inverse for standard bincode u64/usize
encodings, also when followed by more message bytes. It intentionally makes
no strict canonicality or full native proof-decoder claim on arbitrary input.
-/

namespace FormalProof4FHE.HasteBoots.NativeIntegerPrefix

open InputIndexedOracle (Input Byte)
open NativeUsizeMessage (Usize)

def headerSize (tag : Byte) : ℕ :=
  if tag.val < 251 then 1 else if tag = 251 then 3 else if tag = 252 then 5 else if tag = 253 then 9 else 0

private theorem encoded_header (value : Usize) (suffix : Input) :
    headerSize ((NativeUsizeMessage.encode value ++ suffix).headD 0) =
      (NativeUsizeMessage.encode value).length := by
  unfold NativeUsizeMessage.encode
  split
  · rename_i small
    simp [headerSize, small]
  · split
    · simp [headerSize, TranscriptFrame.littleEndian_length]
    · split <;> simp [headerSize, TranscriptFrame.littleEndian_length]

def read (bytes : Input) : Option (ℕ × Input) :=
  (NativeUsizeMessage.read (bytes.take (headerSize (bytes.headD 0)))).map
    (fun value => (value, bytes.drop (headerSize (bytes.headD 0))))

theorem read_encode (value : Usize) (suffix : Input) :
    read (NativeUsizeMessage.encode value ++ suffix) = some (value.val, suffix) := by
  rw [read, encoded_header, List.take_append_of_le_length le_rfl, List.take_of_length_le le_rfl,
    List.drop_append_of_le_length le_rfl, List.drop_of_length_le le_rfl, List.nil_append,
    NativeUsizeMessage.read_encode]
  rfl

def words (values : List Usize) : Input := values.flatMap NativeUsizeMessage.encode

def readCount : ℕ → Input → Option (List ℕ × Input)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes => (read bytes).bind (fun entry =>
      (readCount count entry.2).map (fun rest => (entry.1 :: rest.1, rest.2)))

theorem readCount_words (values : List Usize) (suffix : Input) :
    readCount values.length (words values ++ suffix) = some (values.map Fin.val, suffix) := by
  induction values with
  | nil => simp [words, readCount]
  | cons value tail ih =>
    simp only [words, List.flatMap_cons, List.length_cons, readCount, List.append_assoc]
    change (read (NativeUsizeMessage.encode value ++ (words tail ++ suffix))).bind _ = _
    rw [read_encode, Option.bind_some, ih]
    rfl

def encodeVector (values : List Usize) (fits : values.length < 2 ^ 64) : Input :=
  NativeUsizeMessage.encode ⟨values.length, fits⟩ ++ words values

def readVector (bytes : Input) : Option (List ℕ × Input) :=
  (read bytes).bind (fun entry => readCount entry.1 entry.2)

theorem readVector_encode (values : List Usize) (fits : values.length < 2 ^ 64) (suffix : Input) :
    readVector (encodeVector values fits ++ suffix) = some (values.map Fin.val, suffix) := by
  rw [encodeVector, List.append_assoc, readVector, read_encode, Option.bind_some]
  exact readCount_words values suffix

theorem encodeVector_injective (left right : List Usize) (leftFits : left.length < 2 ^ 64)
    (rightFits : right.length < 2 ^ 64) (same : encodeVector left leftFits = encodeVector right rightFits) : left = right := by
  have parsed := congrArg (fun bytes => readVector (bytes ++ [])) same
  rw [readVector_encode, readVector_encode] at parsed
  have values := congrArg Prod.fst (Option.some.inj parsed)
  exact (List.map_injective_iff.mpr Fin.val_injective) values

end FormalProof4FHE.HasteBoots.NativeIntegerPrefix
