module

public import FormalProof4FHE.HasteBoots.NativeFields
public import FormalProof4FHE.HasteBoots.NativeUsizeMessage

@[expose] public section

/-!
# Native raw base-field representatives

Goldilocks serialization retains its full raw u64, including lazy values.
BabyBear deserialization admits only raw Montgomery representatives below
its prime. The natural-number Montgomery model below spells unsigned
wrapping, low-word masking and right shift as moduli and division; checked
Rust/instruction refinement and the other arithmetic operations remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeFieldRepresentation

open NativeFields

abbrev GoldWord := Fin (2 ^ 64)
abbrev BabyWord := Fin babyBearModulus

def goldValue (word : GoldWord) : Goldilocks := (word.val : Goldilocks)

def goldCanonical (word : GoldWord) : ℕ :=
  if goldilocksModulus ≤ word.val then word.val - goldilocksModulus else word.val

theorem goldCanonical_lt (word : GoldWord) : goldCanonical word < goldilocksModulus := by
  have fits := word.isLt
  unfold goldCanonical
  unfold goldilocksModulus at *
  norm_num at fits ⊢
  split <;> omega

theorem goldCanonical_cast (word : GoldWord) :
    (goldCanonical word : Goldilocks) = goldValue word := by
  unfold goldCanonical goldValue
  split
  next large => simp only [Nat.cast_sub large, ZMod.natCast_self, sub_zero]
  next => rfl

theorem goldValue_val (word : GoldWord) : (goldValue word).val = goldCanonical word := by
  rw [← goldCanonical_cast, ZMod.val_natCast_of_lt (goldCanonical_lt word)]

/-- This is the semantic equality tested by native lazy Goldilocks
comparison; serialization still retains each original raw word. -/
theorem goldValue_eq_iff (left right : GoldWord) :
    goldValue left = goldValue right ↔ goldCanonical left = goldCanonical right := by
  constructor
  · intro same
    have values := congrArg (fun value : Goldilocks => value.val) same
    simpa only [goldValue_val] using values
  · intro same
    rw [← goldCanonical_cast left, ← goldCanonical_cast right, same]

/-- Native Montgomery radix, inverse-mod-radix constant, and u64 modulus. -/
def radix : ℕ := 4294967296
def montyMu : ℕ := 2281701377
def wordModulus : ℕ := 18446744073709551616

def montyT (word : BabyWord) : ℕ := (word.val * montyMu) % radix
def montyU (word : BabyWord) : ℕ := montyT word * babyBearModulus

/-- Natural semantics of the native wrapping u64 subtraction, high-word
extraction, and wrapping u32 correction in `from_monty`. -/
def fromMonty (word : BabyWord) : ℕ :=
  (((word.val + wordModulus - montyU word) % wordModulus) / radix +
    (if word.val < montyU word then babyBearModulus else 0)) % radix

private theorem radix_positive : 0 < radix := by decide
private theorem mu_inverse : (montyMu * babyBearModulus) % radix = 1 := by decide

theorem monty_remainder (word : BabyWord) : montyU word % radix = word.val := by
  have small : word.val < radix := by
    have bound := word.isLt
    unfold babyBearModulus radix at *
    omega
  unfold montyU montyT
  rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod word.val (montyMu * babyBearModulus) radix,
    mu_inverse, Nat.mod_eq_of_lt small, mul_one, Nat.mod_eq_of_lt small]

theorem monty_quotient_lt (word : BabyWord) : montyU word / radix < babyBearModulus := by
  apply (Nat.div_lt_iff_lt_mul radix_positive).mpr
  have bound := Nat.mod_lt (word.val * montyMu) radix_positive
  unfold montyU montyT
  unfold babyBearModulus radix at *
  omega

theorem monty_decompose (word : BabyWord) :
    word.val + radix * (montyU word / radix) = montyU word := by
  have decomposition := Nat.mod_add_div (montyU word) radix
  rwa [monty_remainder] at decomposition

theorem monty_quotient_positive (word : BabyWord) (nonzero : word.val ≠ 0) :
    0 < montyU word / radix := by
  have decomposition := monty_decompose word
  have bound := word.isLt
  unfold montyU at *
  unfold babyBearModulus radix at *
  omega

/-- The explicit wrapped-word computation returns the unique canonical
Montgomery reduction of every deserializable BabyBear raw word. -/
theorem fromMonty_formula (word : BabyWord) :
    fromMonty word = if word.val = 0 then 0 else babyBearModulus - montyU word / radix := by
  by_cases zero : word.val = 0
  · simp [fromMonty, montyU, montyT, zero]
  · have decomposition := monty_decompose word
    have quotient := monty_quotient_lt word
    have positive := monty_quotient_positive word zero
    have over : word.val < montyU word := by
      norm_num only [radix] at decomposition positive ⊢
      omega
    have subtract : word.val + wordModulus - montyU word =
        wordModulus - radix * (montyU word / radix) := by omega
    have below : wordModulus - radix * (montyU word / radix) < wordModulus := by
      unfold radix wordModulus babyBearModulus at *
      omega
    have high : (wordModulus - radix * (montyU word / radix)) / radix =
        radix - montyU word / radix := by
      unfold radix wordModulus babyBearModulus at *
      omega
    simp only [fromMonty, zero, ite_false, over, ite_true, subtract, Nat.mod_eq_of_lt below, high]
    unfold radix babyBearModulus at *
    omega

theorem fromMonty_lt (word : BabyWord) : fromMonty word < babyBearModulus := by
  rw [fromMonty_formula]
  split
  · exact Nat.zero_lt_of_lt word.isLt
  · have positive := monty_quotient_positive word ‹word.val ≠ 0›
    omega

def babyValue (word : BabyWord) : BabyBear :=
  (word.val : BabyBear) * (radix : BabyBear)⁻¹

theorem radix_nonzero : (radix : BabyBear) ≠ 0 := by decide +kernel

theorem fromMonty_mul (word : BabyWord) :
    (fromMonty word : BabyBear) * (radix : BabyBear) = (word.val : BabyBear) := by
  by_cases zero : word.val = 0
  · simp [fromMonty_formula, zero]
  · have quotient := monty_quotient_lt word
    have decomposition := congrArg (fun value : ℕ => (value : BabyBear)) (monty_decompose word)
    have uZero : (montyU word : BabyBear) = 0 := by
      change ((montyT word * babyBearModulus : ℕ) : BabyBear) = 0
      rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
    rw [uZero, Nat.cast_add, Nat.cast_mul] at decomposition
    rw [fromMonty_formula, ite_eq_right zero, Nat.cast_sub (Nat.le_of_lt quotient)]
    simp only [ZMod.natCast_self, zero_sub]
    linear_combination -decomposition

theorem fromMonty_cast (word : BabyWord) : (fromMonty word : BabyBear) = babyValue word := by
  calc
    (fromMonty word : BabyBear) = ((fromMonty word : BabyBear) * (radix : BabyBear)) * (radix : BabyBear)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ radix_nonzero, mul_one]
    _ = babyValue word := by rw [fromMonty_mul]; rfl

theorem babyValue_val (word : BabyWord) : (babyValue word).val = fromMonty word := by
  rw [← fromMonty_cast, ZMod.val_natCast_of_lt (fromMonty_lt word)]

/-- Mathematical form of `BabyBear::new`: multiplication by the radix
followed by the unique representative below the prime. -/
def babyOfValue (value : BabyBear) : BabyWord :=
  ⟨(value * (radix : BabyBear)).val, ZMod.val_lt _⟩

theorem babyValue_ofValue (value : BabyBear) : babyValue (babyOfValue value) = value := by
  simp only [babyValue, babyOfValue, ZMod.natCast_zmod_val, mul_assoc,
    mul_inv_cancel₀ radix_nonzero, mul_one]

theorem babyOfValue_value (word : BabyWord) : babyOfValue (babyValue word) = word := by
  apply Fin.ext
  simp only [babyOfValue, babyValue, mul_assoc, inv_mul_cancel₀ radix_nonzero, mul_one]
  exact ZMod.val_natCast_of_lt word.isLt

theorem babyValue_injective : Function.Injective babyValue := by
  intro left right same
  have equal := congrArg babyOfValue same
  simpa only [babyOfValue_value] using equal

theorem babyOfValue_raw (value : BabyBear) :
    (babyOfValue value).val = (value.val * radix) % babyBearModulus := by
  change (value * (radix : BabyBear)).val = _
  rw [← ZMod.val_natCast babyBearModulus (value.val * radix), Nat.cast_mul, ZMod.natCast_zmod_val]

theorem baby_new_product_fits (value : BabyBear) : value.val * radix < wordModulus := by
  have bound := ZMod.val_lt value
  unfold babyBearModulus radix wordModulus at *
  omega

theorem baby_mu_product_fits (word : BabyWord) : word.val * montyMu < wordModulus := by
  have bound := word.isLt
  unfold babyBearModulus montyMu wordModulus at *
  omega

end FormalProof4FHE.HasteBoots.NativeFieldRepresentation
