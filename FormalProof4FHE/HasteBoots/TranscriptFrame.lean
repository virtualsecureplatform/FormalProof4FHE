module

public import FormalProof4FHE.HasteBoots.InputIndexedOracle

@[expose] public section

/-!
# Native transcript frame encoding and structural decoding

The layout is exactly `kind || u64le(label.length) || label ||
u64le(message.length) || message`, as in `classical_transcript.rs::frame`.
Kinds 0 through 8 are structurally admissible. Field meanings, protocol
stage admissibility, and checked Rust correspondence are separate obligations.
Length bounds are explicit: the native casts to u64 must not truncate them.
-/

namespace FormalProof4FHE.HasteBoots.TranscriptFrame

open InputIndexedOracle (Byte Input)

/-- Fixed-width little-endian output; high bytes are discarded as by a cast. -/
def littleEndian : ℕ → ℕ → Input
  | 0, _ => []
  | width + 1, value => ⟨value % 256, Nat.mod_lt _ (by decide)⟩ ::
      littleEndian width (value / 256)

def fromLittleEndian : Input → ℕ
  | [] => 0
  | byte :: tail => byte.val + 256 * fromLittleEndian tail

theorem littleEndian_length (width value : ℕ) : (littleEndian width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [littleEndian, ih]

theorem fromLittleEndian_littleEndian (width value : ℕ) (fits : value < 256 ^ width) :
    fromLittleEndian (littleEndian width value) = value := by
  induction width generalizing value with
  | zero =>
    simp only [pow_zero] at fits
    have zero : value = 0 := by omega
    subst value
    rfl
  | succ width ih =>
    have quotient : value / 256 < 256 ^ width := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [pow_succ, Nat.mul_comm] using fits
    simp only [littleEndian, fromLittleEndian, ih _ quotient]
    exact Nat.mod_add_div value 256

/-- Every byte string is a bounded little-endian numeral, including adversarial input. -/
theorem fromLittleEndian_lt (input : Input) :
    fromLittleEndian input < 256 ^ input.length := by
  induction input with
  | nil => decide
  | cons byte tail ih =>
    simp only [fromLittleEndian, List.length_cons, pow_succ]
    have := byte.isLt
    omega

/-- Fixed-width decoding has no alternative byte representation. -/
theorem littleEndian_fromLittleEndian (input : Input) :
    littleEndian input.length (fromLittleEndian input) = input := by
  induction input with
  | nil => rfl
  | cons byte tail ih =>
    have low : (byte.val + 256 * fromLittleEndian tail) % 256 = byte.val := by
      have := byte.isLt
      omega
    have high : (byte.val + 256 * fromLittleEndian tail) / 256 = fromLittleEndian tail := by
      have := byte.isLt
      omega
    simp only [List.length_cons, fromLittleEndian, littleEndian, low, high, ih]

/-- On the declared machine model this is the native u64 length limit. -/
def lengthLimit : ℕ := 256 ^ 8

theorem lengthLimit_eq : lengthLimit = 2 ^ 64 := by decide

def sized (payload : Input) : Input := littleEndian 8 payload.length ++ payload

/-- A checked take refuses a truncated header or body. -/
def takeBytes (count : ℕ) (input : Input) : Option (Input × Input) :=
  if count ≤ input.length then some (input.take count, input.drop count) else none

def readSized (input : Input) : Option (Input × Input) := do
  let (header, tail) ← takeBytes 8 input
  takeBytes (fromLittleEndian header) tail

theorem takeBytes_append (initial suffix : Input) :
    takeBytes initial.length (initial ++ suffix) = some (initial, suffix) := by
  simp [takeBytes]

theorem takeBytes_sound (count : ℕ) (input payload suffix : Input)
    (parsed : takeBytes count input = some (payload, suffix)) :
    input = payload ++ suffix ∧ payload.length = count := by
  unfold takeBytes at parsed
  split at parsed
  next fits =>
    have parts := Option.some.inj parsed
    have first := congrArg Prod.fst parts
    have rest := congrArg Prod.snd parts
    dsimp only at first rest
    constructor
    · rw [← first, ← rest]
      exact (List.take_append_drop count input).symm
    · rw [← first, List.length_take, Nat.min_eq_left fits]
  next => contradiction

/-- Successful parsing certifies the length bound and reconstructs every
consumed byte, even if the caller did not construct the input via `sized`. -/
theorem readSized_sound (input payload suffix : Input)
    (parsed : readSized input = some (payload, suffix)) :
    payload.length < lengthLimit ∧ input = sized payload ++ suffix := by
  unfold readSized at parsed
  cases headerEq : takeBytes 8 input with
  | none => simp [headerEq] at parsed
  | some pair =>
    rcases pair with ⟨header, tail⟩
    simp only [headerEq, Option.bind_eq_bind, Option.bind_some] at parsed
    have outer := takeBytes_sound 8 input header tail headerEq
    have inner := takeBytes_sound (fromLittleEndian header) tail payload suffix parsed
    have headerBytes := littleEndian_fromLittleEndian header
    rw [outer.2, ← inner.2] at headerBytes
    constructor
    · rw [inner.2]
      simpa only [lengthLimit, outer.2] using fromLittleEndian_lt header
    · rw [outer.1, inner.1, ← headerBytes]
      simp only [sized, List.append_assoc]

theorem readSized_sized (payload suffix : Input) (fits : payload.length < lengthLimit) :
    readSized (sized payload ++ suffix) = some (payload, suffix) := by
  unfold readSized sized
  rw [List.append_assoc]
  have header : takeBytes 8 (littleEndian 8 payload.length ++ (payload ++ suffix)) =
      some (littleEndian 8 payload.length, payload ++ suffix) := by
    simpa only [littleEndian_length] using
      takeBytes_append (littleEndian 8 payload.length) (payload ++ suffix)
  rw [header]
  simp only [Option.bind_eq_bind, Option.bind_some]
  change takeBytes (fromLittleEndian (littleEndian 8 payload.length)) (payload ++ suffix) = _
  rw [fromLittleEndian_littleEndian 8 payload.length fits]
  exact takeBytes_append payload suffix

structure Frame where
  kind : Fin 9
  label : Input
  message : Input
  deriving DecidableEq

def Valid (frame : Frame) : Prop :=
  frame.label.length < lengthLimit ∧ frame.message.length < lengthLimit

def encode (frame : Frame) : Input :=
  ⟨frame.kind.val, by omega⟩ :: (sized frame.label ++ sized frame.message)

def decode : Input → Option (Frame × Input)
  | [] => none
  | kind :: tail =>
      if valid : kind.val < 9 then do
        let (label, tail) ← readSized tail
        let (message, tail) ← readSized tail
        pure (⟨⟨kind.val, valid⟩, label, message⟩, tail)
      else none

theorem encode_length (frame : Frame) :
    (encode frame).length = 17 + frame.label.length + frame.message.length := by
  simp [encode, sized, littleEndian_length]
  omega

/-- One frame can be decoded in an arbitrary longer input. The suffix is
returned untouched, so this also rules out ambiguous frame boundaries. -/
theorem decode_encode (frame : Frame) (valid : Valid frame) (suffix : Input) :
    decode (encode frame ++ suffix) = some (frame, suffix) := by
  rcases frame with ⟨kind, label, message⟩
  rcases valid with ⟨labelFits, messageFits⟩
  simp only [encode, List.cons_append, decode, Fin.is_lt, dite_true]
  rw [List.append_assoc, readSized_sized label (sized message ++ suffix) labelFits]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [readSized_sized message suffix messageFits]
  rfl

/-- A successful parse of arbitrary bytes reconstructs the exact consumed
frame and certifies both native u64 lengths. This is the converse of `decode_encode`. -/
theorem decode_sound (input : Input) (frame : Frame) (suffix : Input)
    (parsed : decode input = some (frame, suffix)) :
    Valid frame ∧ input = encode frame ++ suffix := by
  cases input with
  | nil => simp [decode] at parsed
  | cons kind tail =>
    simp only [decode] at parsed
    split at parsed
    next validKind =>
      cases labelEq : readSized tail with
      | none => simp [labelEq] at parsed
      | some pair =>
        rcases pair with ⟨label, afterLabel⟩
        simp only [labelEq, Option.bind_eq_bind, Option.bind_some] at parsed
        cases messageEq : readSized afterLabel with
        | none => simp [messageEq] at parsed
        | some pair =>
          rcases pair with ⟨message, afterMessage⟩
          simp only [messageEq, Option.bind_some] at parsed
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj parsed)
          have labelSound := readSized_sound tail label afterLabel labelEq
          have messageSound := readSized_sound afterLabel message afterMessage messageEq
          constructor
          · exact ⟨labelSound.1, messageSound.1⟩
          · change kind :: tail = kind :: ((sized label ++ sized message) ++ afterMessage)
            rw [labelSound.2, messageSound.2, List.append_assoc]
    next => contradiction

theorem decode_eq_some_iff (input : Input) (frame : Frame) (suffix : Input) :
    decode input = some (frame, suffix) ↔ Valid frame ∧ input = encode frame ++ suffix := by
  constructor
  · exact decode_sound input frame suffix
  · rintro ⟨valid, rfl⟩
    exact decode_encode frame valid suffix

theorem decode_progress (input : Input) (frame : Frame) (suffix : Input)
    (parsed : decode input = some (frame, suffix)) : suffix.length < input.length := by
  have lengths := congrArg List.length (decode_sound input frame suffix parsed).2
  simp only [List.length_append, encode_length] at lengths
  omega

/-- Structural recognition cannot silently discard a malformed header or trailing byte. -/
theorem decode_complete_iff (input : Input) (frame : Frame) :
    decode input = some (frame, []) ↔ Valid frame ∧ input = encode frame := by
  simpa only [List.append_nil] using decode_eq_some_iff input frame []

/-- Equal encoded prefixes force equal frames and equal remaining bytes.
No hash collision or oracle freshness assumption appears in this theorem. -/
theorem boundary_unique (left right : Frame) (leftValid : Valid left) (rightValid : Valid right)
    (leftSuffix rightSuffix : Input)
    (same : encode left ++ leftSuffix = encode right ++ rightSuffix) :
    left = right ∧ leftSuffix = rightSuffix := by
  have decoded := congrArg decode same
  rw [decode_encode left leftValid, decode_encode right rightValid] at decoded
  exact Prod.mk.inj (Option.some.inj decoded)

theorem encode_injective (left right : Frame) (leftValid : Valid left) (rightValid : Valid right)
    (same : encode left = encode right) : left = right := by
  exact (boundary_unique left right leftValid rightValid [] [] (by simpa using same)).1

theorem decode_reject_kind (kind : Byte) (tail : Input) (invalid : 9 ≤ kind.val) :
    decode (kind :: tail) = none := by
  simp [decode, Nat.not_lt.mpr invalid]

def encodeMany : List Frame → Input
  | [] => []
  | frame :: tail => encode frame ++ encodeMany tail

/-- Consume a complete frame stream. Recursion is justified by consumed
bytes, with no guessed bound on the number of frames. -/
def decodeAll (input : Input) : Option (List Frame) :=
  if input = [] then some []
  else match _parsed : decode input with
    | none => none
    | some (frame, suffix) => (frame :: ·) <$> decodeAll suffix
termination_by input.length
decreasing_by exact decode_progress _ _ _ _parsed

/-- Full-stream recognition checks every length and leaves no trailing bytes. -/
theorem decodeAll_sound (input : Input) (frames : List Frame)
    (parsed : decodeAll input = some frames) :
    (∀ frame ∈ frames, Valid frame) ∧ input = encodeMany frames := by
  induction input using (measure (fun xs : Input => xs.length)).wf.induction generalizing frames with
  | h input ih =>
    by_cases empty : input = []
    · subst input
      rw [decodeAll, ite_eq_left rfl] at parsed
      simp only [Option.some.injEq] at parsed
      subst frames
      simp [encodeMany]
    · rw [decodeAll, ite_eq_right empty] at parsed
      split at parsed
      next firstEq => contradiction
      next frame suffix firstEq =>
        cases restEq : decodeAll suffix with
        | none => simp [restEq] at parsed
        | some rest =>
          rw [restEq] at parsed
          change some (frame :: rest) = some frames at parsed
          have equal := Option.some.inj parsed
          subst frames
          have firstSound := decode_sound input frame suffix firstEq
          have restSound := ih suffix (decode_progress input frame suffix firstEq) rest restEq
          constructor
          · intro next member
            rcases List.mem_cons.mp member with rfl | later
            · exact firstSound.1
            · exact restSound.1 next later
          · rw [firstSound.2, restSound.2, encodeMany]

/-- Every valid complete frame stream is recognized, including the empty stream. -/
theorem decodeAll_encodeMany (frames : List Frame)
    (valid : ∀ frame ∈ frames, Valid frame) : decodeAll (encodeMany frames) = some frames := by
  induction frames with
  | nil => rw [encodeMany, decodeAll, ite_eq_left rfl]
  | cons frame tail ih =>
    have nonempty : encodeMany (frame :: tail) ≠ [] := by
      intro empty
      have lengths := congrArg List.length empty
      simp only [encodeMany, List.length_append, encode_length, List.length_nil] at lengths
      omega
    rw [decodeAll, ite_eq_right nonempty]
    have first := decode_encode frame (valid _ (by simp)) (encodeMany tail)
    change decode (encodeMany (frame :: tail)) = some (frame, encodeMany tail) at first
    split
    next rejected => rw [rejected] at first; contradiction
    next parsedFrame suffix accepted =>
      rw [accepted] at first
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj first)
      rw [ih (fun next member => valid next (by simp [member]))]
      rfl

theorem decodeAll_eq_some_iff (input : Input) (frames : List Frame) :
    decodeAll input = some frames ↔ (∀ frame ∈ frames, Valid frame) ∧ input = encodeMany frames := by
  constructor
  · exact decodeAll_sound input frames
  · rintro ⟨valid, rfl⟩
    exact decodeAll_encodeMany frames valid

/-- A complete sequence of well-sized frames has a unique decomposition.
This is structural parsing only; it does not validate protocol stages. -/
theorem encodeMany_injective (left right : List Frame)
    (leftValid : ∀ frame ∈ left, Valid frame) (rightValid : ∀ frame ∈ right, Valid frame)
    (same : encodeMany left = encodeMany right) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons head tail =>
      have lengths := congrArg List.length same
      simp only [encodeMany, List.length_nil, List.length_append, encode_length] at lengths
      omega
  | cons head tail ih =>
    cases right with
    | nil =>
      have lengths := congrArg List.length same
      simp only [encodeMany, List.length_nil, List.length_append, encode_length] at lengths
      omega
    | cons other rest =>
      have heads := boundary_unique head other (leftValid _ (by simp))
        (rightValid _ (by simp)) (encodeMany tail) (encodeMany rest) same
      have tails := ih rest (fun frame member => leftValid frame (by simp [member]))
        (fun frame member => rightValid frame (by simp [member])) heads.2
      exact congrArg₂ List.cons heads.1 tails

end FormalProof4FHE.HasteBoots.TranscriptFrame
