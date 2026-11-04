module

public import FormalProof4FHE.HasteBoots.NativeGoldCubic
public import FormalProof4FHE.HasteBoots.NativeGoldInverse

@[expose] public section

/-!
# Raw cubic inverse and its nonzero domain

The determinant and adjugate keep the native operation order. Failure of
base inversion is represented by `none`; Rust's unchecked inverse panics on
that path. Nonzero extension inputs are proved to avoid it. Checked Rust
instruction refinement remains open.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldCubicInverse

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)

/-- Scalar denominator of native `cubic_inv`. -/
def determinant (a : Word) : GoldWord :=
  let a0square := NativeGoldArithmetic.mul (a 0) (a 0)
  let a1square := NativeGoldArithmetic.mul (a 1) (a 1)
  let a2w := NativeGoldArithmetic.mul 7 (a 2)
  let a0a1 := NativeGoldArithmetic.mul (a 0) (a 1)
  let three := NativeGoldArithmetic.add (NativeGoldArithmetic.add 1 1) 1
  NativeGoldArithmetic.sub
    (NativeGoldArithmetic.add
      (NativeGoldArithmetic.add (NativeGoldArithmetic.mul a0square (a 0))
        (NativeGoldArithmetic.mul (NativeGoldArithmetic.mul 7 (a 1)) a1square))
      (NativeGoldArithmetic.mul (NativeGoldArithmetic.mul a2w a2w) (a 2)))
    (NativeGoldArithmetic.mul (NativeGoldArithmetic.mul three a2w) a0a1)

def adjugate (a : Word) : Word :=
  let a0square := NativeGoldArithmetic.mul (a 0) (a 0)
  let a1square := NativeGoldArithmetic.mul (a 1) (a 1)
  let a2w := NativeGoldArithmetic.mul 7 (a 2)
  let a0a1 := NativeGoldArithmetic.mul (a 0) (a 1)
  ![NativeGoldArithmetic.sub a0square (NativeGoldArithmetic.mul (a 1) a2w),
    NativeGoldArithmetic.sub (NativeGoldArithmetic.mul a2w (a 2)) a0a1,
    NativeGoldArithmetic.sub a1square (NativeGoldArithmetic.mul (a 0) (a 2))]

/-- The source multiplies the inverse scalar on the left of each coordinate. -/
def finish (a : Word) (scalar : GoldWord) : Word :=
  fun i => NativeGoldArithmetic.mul scalar (adjugate a i)

def inverseResult (a : Word) : Option Word :=
  (NativeGoldInverse.tryInverse (determinant a)).map (finish a)

/-- Native division first inverts the divisor, then multiplies on the right. -/
def divResult (left right : Word) : Option Word :=
  (inverseResult right).map (NativeGoldCubic.mul left)

noncomputable section

theorem determinant_value (a : Word) :
    goldValue (determinant a) = goldValue (a 0) ^ 3 + 7 * goldValue (a 1) ^ 3 +
      49 * goldValue (a 2) ^ 3 - 21 * goldValue (a 0) * goldValue (a 1) * goldValue (a 2) := by
  have seven : goldValue (7 : GoldWord) = (7 : Goldilocks) := rfl
  have one : goldValue (1 : GoldWord) = (1 : Goldilocks) := rfl
  simp only [determinant, NativeGoldArithmetic.add_value, NativeGoldArithmetic.sub_value,
    NativeGoldArithmetic.mul_value, seven, one]
  ring

theorem adjugate_coordinates (a : Word) (i : Fin 3) :
    goldValue (adjugate a i) =
      ![goldValue (a 0) ^ 2 - 7 * goldValue (a 1) * goldValue (a 2),
        7 * goldValue (a 2) ^ 2 - goldValue (a 0) * goldValue (a 1),
        goldValue (a 1) ^ 2 - goldValue (a 0) * goldValue (a 2)] i := by
  have seven : goldValue (7 : GoldWord) = (7 : Goldilocks) := rfl
  fin_cases i <;>
    simp [adjugate, NativeGoldArithmetic.sub_value, NativeGoldArithmetic.mul_value, seven] <;> ring

theorem product_coordinates (a : Word) (i : Fin 3) :
    goldValue (NativeGoldCubic.mul a (adjugate a) i) =
      ![goldValue (determinant a), 0, 0] i := by
  rw [NativeGoldCubic.mul_coordinates]
  fin_cases i <;>
    simp [adjugate_coordinates, determinant_value] <;> ring

theorem product_adjugate (a : Word) :
    goldExtensionValue a * goldExtensionValue (adjugate a) =
      algebraMap Goldilocks Goldilocks3 (goldValue (determinant a)) := by
  rw [← NativeGoldCubic.mul_value, NativeGoldCubic.value_expansion]
  simp only [product_coordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, map_zero, zero_mul, add_zero]

/-- Irreducibility of X^3-7 rules out a zero adjugate of a nonzero input. -/
theorem adjugate_nonzero (a : Word) (nonzero : goldExtensionValue a ≠ 0) :
    goldExtensionValue (adjugate a) ≠ 0 := by
  intro zero
  have coordinate (i : Fin 3) : goldValue (adjugate a i) = 0 := by
    have values := congrArg (fun v => goldilocksBasis.equivFun v i) zero
    simpa only [goldExtension_coordinate, map_zero, Pi.zero_apply] using values
  have h0 := coordinate 0
  have h1 := coordinate 1
  have h2 := coordinate 2
  simp only [adjugate_coordinates, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2
  by_cases lastZero : goldValue (a 2) = 0
  · have middleZero : goldValue (a 1) = 0 := by
      apply (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
      simpa only [lastZero, mul_zero, sub_zero] using h2
    have firstZero : goldValue (a 0) = 0 := by
      apply (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
      simpa only [middleZero, mul_zero, zero_mul, sub_zero] using h0
    apply nonzero
    apply goldilocksBasis.equivFun.injective
    ext i
    simp only [goldExtension_coordinate, map_zero, Pi.zero_apply]
    fin_cases i <;> assumption
  · apply goldilocks_seven_not_cube (goldValue (a 1) / goldValue (a 2))
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 3 lastZero)).mpr
    linear_combination goldValue (a 1) * h2 - goldValue (a 2) * h1

theorem determinant_nonzero (a : Word) (nonzero : goldExtensionValue a ≠ 0) :
    goldValue (determinant a) ≠ 0 := by
  intro zero
  have relation := product_adjugate a
  rw [zero, map_zero] at relation
  exact (mul_ne_zero nonzero (adjugate_nonzero a nonzero)) relation

theorem finish_value (a : Word) (scalar : GoldWord) :
    goldExtensionValue (finish a scalar) = goldValue scalar • goldExtensionValue (adjugate a) := by
  apply goldilocksBasis.equivFun.injective
  ext i
  simp only [goldExtension_coordinate, finish, NativeGoldArithmetic.mul_value,
    map_smul, Pi.smul_apply, smul_eq_mul]

/-- Every nonzero native denominator has a successful, mathematically correct
raw inverse result; its serialization retains the actual operation tree. -/
theorem inverseResult_value (a : Word) (nonzero : goldExtensionValue a ≠ 0) :
    (inverseResult a).map goldExtensionValue = some (goldExtensionValue a)⁻¹ := by
  have normNonzero := determinant_nonzero a nonzero
  have canonicalNonzero := mt (NativeGoldInverse.canonical_zero_iff (determinant a)).mp normNonzero
  simp only [inverseResult, NativeGoldInverse.tryInverse, canonicalNonzero, ite_false,
    Option.map_some, finish_value, NativeGoldInverse.chain_inverse _ normNonzero]
  congr 1
  apply eq_inv_of_mul_eq_one_left
  rw [Algebra.smul_def]
  calc
    algebraMap Goldilocks Goldilocks3 (goldValue (determinant a))⁻¹ *
        goldExtensionValue (adjugate a) * goldExtensionValue a =
      algebraMap Goldilocks Goldilocks3 (goldValue (determinant a))⁻¹ *
        (goldExtensionValue a * goldExtensionValue (adjugate a)) := by ring
    _ = 1 := by
      rw [product_adjugate, ← map_mul, inv_mul_cancel₀ normNonzero, map_one]

theorem divResult_value (left right : Word) (nonzero : goldExtensionValue right ≠ 0) :
    (divResult left right).map goldExtensionValue =
      some (goldExtensionValue left / goldExtensionValue right) := by
  have inverse := congrArg (Option.map (fun value => goldExtensionValue left * value))
    (inverseResult_value right nonzero)
  simpa only [divResult, Option.map_map, Function.comp_def, NativeGoldCubic.mul_value,
    Option.map_some, div_eq_mul_inv] using inverse

end

end FormalProof4FHE.HasteBoots.NativeGoldCubicInverse
