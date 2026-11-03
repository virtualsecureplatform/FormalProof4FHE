module

public import FormalProof4FHE.HasteBoots.RejectionSampling
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Size

@[expose] public section

/-!
# Little-endian byte decoding and the canonical sampler's low-bit mask

The byte vector is in increasing address order. Its little-endian value is
bounded by the whole byte width. Splitting into high and low bits gives an
explicit bijection; projecting its low component proves uniform masking.
This is a fresh ideal byte-chunk law, not a transcript/XOF freshness claim.
-/

open OracleSpec OracleComp
open scoped Classical BigOperators

namespace FormalProof4FHE.HasteBoots.CanonicalByteMask

noncomputable section

abbrev Bytes (bytes : ℕ) := Fin bytes → Fin 256

/-- Increasing byte indices have increasing powers of 256. -/
def word (bytes : ℕ) : Bytes bytes ≃ Fin (2 ^ (8 * bytes)) :=
  finFunctionFinEquiv.trans (finCongr (by rw [pow_mul]; rfl))

def decode {bytes : ℕ} (raw : Bytes bytes) : ℕ := (word bytes raw).val

theorem decode_eq_sum {bytes : ℕ} (raw : Bytes bytes) :
    decode raw = ∑ index : Fin bytes, (raw index).val * 256 ^ index.val := rfl

theorem decode_lt {bytes : ℕ} (raw : Bytes bytes) : decode raw < 2 ^ (8 * bytes) :=
  (word bytes raw).isLt

/-- The mathematical form of the native `value & mask` operation. -/
def masked {bytes : ℕ} (bits : ℕ) (raw : Bytes bytes) : ℕ := decode raw &&& (2 ^ bits - 1)

theorem masked_eq_mod {bytes : ℕ} (bits : ℕ) (raw : Bytes bytes) :
    masked bits raw = decode raw % 2 ^ bits := Nat.and_two_pow_sub_one_eq_mod _ _

def low {bytes : ℕ} (bits : ℕ) (raw : Bytes bytes) : Fin (2 ^ bits) :=
  ⟨decode raw % 2 ^ bits, Nat.mod_lt _ (by positivity)⟩

theorem low_val {bytes : ℕ} (bits : ℕ) (raw : Bytes bytes) :
    (low bits raw).val = masked bits raw := (masked_eq_mod bits raw).symm

/-- All discarded high bits remain in the bijection; no biased reduction or
assumed uniformity of the retained low bits is used. -/
def split (bits bytes : ℕ) (fits : bits ≤ 8 * bytes) :
    Bytes bytes ≃ Fin (2 ^ (8 * bytes - bits)) × Fin (2 ^ bits) :=
  (word bytes).trans ((finCongr (by rw [← pow_add, Nat.sub_add_cancel fits])).trans finProdFinEquiv.symm)

theorem split_snd (bits bytes : ℕ) (fits : bits ≤ 8 * bytes) (raw : Bytes bytes) :
    (split bits bytes fits raw).2 = low bits raw := by
  apply Fin.ext
  rfl

/-- Exact ideal-byte transport law for the actual little-endian mask. -/
theorem uniform_low (bits bytes : ℕ) (fits : bits ≤ 8 * bytes) (event : Fin (2 ^ bits) → Prop) :
    Pr{let raw ← $ᵗ (Bytes bytes)}[event (low bits raw)] =
      Pr{let value ← $ᵗ (Fin (2 ^ bits))}[event value] := by
  have splitLaw := SampleableType.prEvent_uniformSample_equiv (split bits bytes fits) (fun pair => event pair.2)
  have swapLaw := SampleableType.prEvent_uniformSample_equiv
    (Equiv.prodComm (Fin (2 ^ (8 * bytes - bits))) (Fin (2 ^ bits))) (fun pair => event pair.1)
  have project := SampleableType.prEvent_uniformSample_fst (β := Fin (2 ^ (8 * bytes - bits))) event
  calc _ = Pr{let raw ← $ᵗ (Bytes bytes)}[event (split bits bytes fits raw).2] :=
          prEvent_congr _ _ _ (fun raw => by rw [split_snd])
       _ = _ := splitLaw.trans (swapLaw.trans project)

/-- Natural-value version exposes the exact mask used in the retry test. -/
theorem uniform_masked (bits bytes : ℕ) (fits : bits ≤ 8 * bytes) (event : ℕ → Prop) :
    Pr{let raw ← $ᵗ (Bytes bytes)}[event (masked bits raw)] =
      Pr{let value ← $ᵗ (Fin (2 ^ bits))}[event value.val] := by
  simpa only [low_val] using uniform_low bits bytes fits (fun value => event value.val)

/-- The scratch array starts at zero and only the requested prefix is read. -/
def pad {bytes total : ℕ} (_fits : bytes ≤ total) (raw : Bytes bytes) : Bytes total :=
  fun index => if present : index.val < bytes then raw ⟨index.val, present⟩ else 0

/-- Zero initialization of the unread suffix does not alter the little-endian
word. In particular, a short read into the native 16-byte array keeps its law. -/
theorem decode_pad {bytes total : ℕ} (fits : bytes ≤ total) (raw : Bytes bytes) :
    decode (pad fits raw) = decode raw := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le fits
  simp [decode_eq_sum, Fin.sum_univ_add, pad, Fin.is_lt]

/-- Full-width natural decoding fits the native u128 value range. -/
theorem decode_pad_lt_u128 {bytes : ℕ} (fits : bytes ≤ 16) (raw : Bytes bytes) :
    decode (pad fits raw) < 2 ^ 128 := by
  exact decode_lt (pad fits raw)

end

end FormalProof4FHE.HasteBoots.CanonicalByteMask
