module
public import FormalProof4FHE.HasteBoots.PackedCipherSource
public import FormalProof4FHE.HasteBoots.RadixLookupSources
@[expose] public section

/-! Transfer canonical radix constraints between complete packed tables and
their constructed ciphertexts. The negative-mask input fixes the native sign. -/
namespace FormalProof4FHE.HasteBoots.DecodedCipherRadixConstraints
open scoped BigOperators
open NativeBlindRotation (Cipher Poly)
noncomputable section
variable {q d c lanes : ℕ} [Fact q.Prime]

def tables (values : Fin (2*d+2) → Cipher q (2^(c+lanes))) :
    Fin (2*d+2) → MatrixFold.Cube (c+1) → Fin (2^lanes) → ZMod q :=
  fun factor => KeySwitchExtraction.pack (values factor)

/-- Pointwise decoded reconstruction constrains every original packed entry. -/
theorem linear_of_coefficients (radix : ZMod q)
    (values : Fin (2*d+2) → Cipher q (2^(c+lanes)))
    (valid : ∀ half index,
      values DecompositionLinear.input half index =
        ∑ digit : Fin d, radix^digit.val * values (DecompositionLinear.digit digit) half index ∧
      values DecompositionLinear.firstBorrow half index = 0 ∧
      values DecompositionLinear.lastBorrow half index = 0) :
    DecompositionLinear.Relation radix (tables values) := by
  intro cell lane
  obtain ⟨coefficient,half,same⟩ := PackedCipherSource.point_surjective cell
  rw [←same]
  simpa only [tables,PackedCipherSource.pack_point] using
    valid half (PackedAccumulatorTrace.polynomial c lanes (coefficient,lane))

/-- Canonical packed digits are canonical coefficients in both decoded halves. -/
theorem digits_of_constraints (radix : ℕ) (radixLarge : 1 < radix)
    (radixSmall : radix < q) (enough : q-1 < radix^d)
    (values : Fin (2*d+2) → Cipher q (2^(c+lanes)))
    (linear : DecompositionLinear.Relation (radix : ZMod q) (tables values))
    (lookup : ∀ cell lane, RadixCanonicity.LookupAt q radix (tables values) cell lane)
    (half : Bool) (index : Fin (2^(c+lanes))) (digit : Fin d) :
    (values (DecompositionLinear.digit digit) half index).val =
      (values DecompositionLinear.input half index).val / radix^digit.val % radix := by
  let position := (PackedAccumulatorTrace.polynomial c lanes).symm index
  have canonical := RadixCanonicity.digits_of_constraints radixLarge radixSmall enough
    (tables values) linear (PackedCipherSource.point position.1 half) position.2
    (lookup _ _) digit
  simpa only [tables,PackedCipherSource.pack_point,position,Prod.mk.eta,Equiv.apply_symm_apply] using canonical

/-- Reconstruction plus comparison identifies the literal native digits of
the negative mask, including the canonical quotient/remainder values. -/
theorem native_digits_of_constraints (bits : ℕ) (radixLarge : 1 < 2^bits)
    (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d)
    (values : Fin (2*d+2) → Cipher q (2^(c+lanes)))
    (linear : DecompositionLinear.Relation (2^bits : ZMod q) (tables values))
    (lookup : ∀ cell lane, RadixCanonicity.LookupAt q (2^bits) (tables values) cell lane)
    (mask : Poly q (2^(c+lanes)))
    (known : ∀ half, values DecompositionLinear.input half = -mask)
    (digit : Fin d) (half : Bool) :
    values (DecompositionLinear.digit digit) half = NativeBlindRotation.digit bits digit (-mask) := by
  funext index
  have canonical := digits_of_constraints (2^bits) radixLarge radixSmall enough values
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using linear) lookup half index digit
  calc
    values (DecompositionLinear.digit digit) half index =
        ((values (DecompositionLinear.digit digit) half index).val : ZMod q) := (ZMod.natCast_zmod_val _).symm
    _ = ((values DecompositionLinear.input half index).val / (2^bits)^digit.val % (2^bits) : ℕ) :=
      congrArg (fun value : ℕ => (value : ZMod q)) canonical
    _ = NativeBlindRotation.digit bits digit (-mask) index := by rw [known half]; rfl

variable {Cfg Input Digest Index : Type} {heights : Cfg → ℕ} [DecidableEq Digest]
/-- The common family tables are exactly these packings, so no fresh private
interpretation is introduced when using the coefficient constraints above. -/
theorem family_tables
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (factors : Fin (2*d+2) → Index) :
    tables (fun factor => PackedCipherSource.familyCipher (c := c) world enc dummy (factors factor)) =
      (fun factor => RecordedPaddedSourceFamily.logical world enc dummy (c+1) (factors factor)) := by
  funext factor
  exact PackedCipherSource.pack_familyCipher world enc dummy (factors factor)

end
end FormalProof4FHE.HasteBoots.DecodedCipherRadixConstraints
