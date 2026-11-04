module

public import FormalProof4FHE.HasteBoots.NativeUsizeMessage

@[expose] public section

/-!
# Native SHA-512 commitment-vector transcript messages

`Digest512` serializes as two fixed 32-byte arrays; a `Commitment` contains
only that digest. A vector therefore has one standard bincode usize header
followed by consecutive 64-byte roots, without per-root length prefixes.
This models the wire format, not hash computation, strict adversarial
proof-byte decoding or checked Rust/serde refinement.
-/

namespace FormalProof4FHE.HasteBoots.NativeRootMessage

open InputIndexedOracle (Input Byte)

abbrev Digest := Fin 64 → Byte

def payload (roots : List Digest) : Input := roots.flatMap List.ofFn

theorem payload_length (roots : List Digest) : (payload roots).length = 64 * roots.length := by
  induction roots with
  | nil => simp [payload]
  | cons root tail ih =>
    simp only [payload, List.flatMap_cons, List.length_append, List.length_ofFn] at *
    rw [ih, List.length_cons, Nat.mul_succ]
    exact Nat.add_comm _ _

private def chunks : ℕ → Input → List Input
  | 0, _ => []
  | count + 1, bytes => bytes.take 64 :: chunks count (bytes.drop 64)

private theorem chunks_payload (roots : List Digest) :
    chunks roots.length (payload roots) = roots.map List.ofFn := by
  induction roots with
  | nil => rfl
  | cons root tail ih =>
    simp only [payload, List.flatMap_cons, List.length_cons, chunks, List.map_cons]
    have first : (List.ofFn root ++ payload tail).take 64 = List.ofFn root := by
      rw [List.take_append_of_le_length (by simp only [List.length_ofFn]; exact le_rfl),
        List.take_of_length_le (by simp only [List.length_ofFn]; exact le_rfl)]
    have rest : (List.ofFn root ++ payload tail).drop 64 = payload tail := by
      rw [List.drop_append_of_le_length (by simp only [List.length_ofFn]; exact le_rfl),
        List.drop_of_length_le (by simp only [List.length_ofFn]; exact le_rfl), List.nil_append]
    change (List.ofFn root ++ payload tail).take 64 ::
      chunks tail.length ((List.ofFn root ++ payload tail).drop 64) = _
    rw [first, rest]
    exact congrArg (fun later => List.ofFn root :: later) ih

theorem payload_injective : Function.Injective payload := by
  intro left right same
  have length : left.length = right.length := by
    have sizes := congrArg List.length same
    rw [payload_length, payload_length] at sizes
    omega
  have equal := congrArg (chunks left.length) same
  rw [chunks_payload, length, chunks_payload] at equal
  exact (List.map_injective_iff.mpr List.ofFn_injective) equal

def encode (roots : List Digest) (fits : roots.length < 2 ^ 64) : Input :=
  NativeUsizeMessage.encode ⟨roots.length, fits⟩ ++ payload roots

theorem encode_length (roots : List Digest) (fits : roots.length < 2 ^ 64) :
    (encode roots fits).length = (NativeUsizeMessage.encode ⟨roots.length, fits⟩).length + 64 * roots.length := by
  rw [encode, List.length_append, payload_length]

/-- The short header cannot conceal a different number of fixed-width
roots. Once the count is fixed, payload grouping is unique. -/
theorem encode_injective (left right : List Digest) (leftFits : left.length < 2 ^ 64)
    (rightFits : right.length < 2 ^ 64) (same : encode left leftFits = encode right rightFits) : left = right := by
  have sizes := congrArg List.length same
  rw [encode_length, encode_length] at sizes
  have firstBound := NativeUsizeMessage.encode_length (⟨left.length, leftFits⟩ : NativeUsizeMessage.Usize)
  have secondBound := NativeUsizeMessage.encode_length (⟨right.length, rightFits⟩ : NativeUsizeMessage.Usize)
  have length : left.length = right.length := by omega
  have count : (⟨left.length, leftFits⟩ : NativeUsizeMessage.Usize) = ⟨right.length, rightFits⟩ := Fin.ext length
  unfold encode at same
  rw [count] at same
  exact payload_injective (List.append_cancel_left same)

end FormalProof4FHE.HasteBoots.NativeRootMessage
