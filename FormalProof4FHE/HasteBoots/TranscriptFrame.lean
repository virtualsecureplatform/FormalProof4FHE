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
