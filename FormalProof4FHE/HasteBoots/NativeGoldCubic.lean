module

public import FormalProof4FHE.HasteBoots.NativeGoldExtensionArithmetic

@[expose] public section

/-!
# Native cubic Karatsuba multiplication

The raw product retains the source order of every addition, subtraction and
multiplication in `cubic_mul`, with binomial constant seven. The algebraic
proof interprets those words in the checked X^3-7 extension.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldCubic

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)

/-- Literal native degree-three Karatsuba operation tree. -/
def mul (a b : Word) : Word :=
  let a0b0 := NativeGoldArithmetic.mul (a 0) (b 0)
  let a1b1 := NativeGoldArithmetic.mul (a 1) (b 1)
  let a2b2 := NativeGoldArithmetic.mul (a 2) (b 2)
  let cross12 := NativeGoldArithmetic.sub (NativeGoldArithmetic.sub
    (NativeGoldArithmetic.mul (NativeGoldArithmetic.add (a 1) (a 2))
      (NativeGoldArithmetic.add (b 1) (b 2))) a1b1) a2b2
  let c0 := NativeGoldArithmetic.add a0b0 (NativeGoldArithmetic.mul cross12 7)
  let c1 := NativeGoldArithmetic.add (NativeGoldArithmetic.sub (NativeGoldArithmetic.sub
    (NativeGoldArithmetic.mul (NativeGoldArithmetic.add (a 0) (a 1))
      (NativeGoldArithmetic.add (b 0) (b 1))) a0b0) a1b1)
      (NativeGoldArithmetic.mul a2b2 7)
  let c2 := NativeGoldArithmetic.add (NativeGoldArithmetic.sub (NativeGoldArithmetic.sub
    (NativeGoldArithmetic.mul (NativeGoldArithmetic.add (a 0) (a 2))
      (NativeGoldArithmetic.add (b 0) (b 2))) a0b0) a2b2) a1b1
  ![c0, c1, c2]

noncomputable section

def generator : Goldilocks3 := AdjoinRoot.root goldilocksPolynomial

theorem generator_cube : generator ^ 3 = 7 := by
  unfold generator Goldilocks3
  have relation := AdjoinRoot.eval₂_root goldilocksPolynomial
  change (Polynomial.X ^ 3 - Polynomial.C (7 : Goldilocks)).eval₂
    (AdjoinRoot.of goldilocksPolynomial) (AdjoinRoot.root goldilocksPolynomial) = 0 at relation
  apply sub_eq_zero.mp
  simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat, map_ofNat] using relation

/-- The basis equivalence has the literal polynomial-coordinate meaning. -/
theorem value_expansion (word : Word) :
    goldExtensionValue word =
      algebraMap Goldilocks Goldilocks3 (goldValue (word 0)) +
      algebraMap Goldilocks Goldilocks3 (goldValue (word 1)) * generator +
      algebraMap Goldilocks Goldilocks3 (goldValue (word 2)) * generator ^ 2 := by
  rw [goldExtensionValue, Module.Basis.equivFun_symm_apply]
  simp [Fin.sum_univ_succ, goldilocks_basis_power, Algebra.smul_def, generator, add_assoc]

theorem mul_coordinates (a b : Word) (i : Fin 3) :
    goldValue (mul a b i) =
      ![goldValue (a 0) * goldValue (b 0) +
          7 * (goldValue (a 1) * goldValue (b 2) + goldValue (a 2) * goldValue (b 1)),
        goldValue (a 0) * goldValue (b 1) + goldValue (a 1) * goldValue (b 0) +
          7 * goldValue (a 2) * goldValue (b 2),
        goldValue (a 0) * goldValue (b 2) + goldValue (a 1) * goldValue (b 1) +
          goldValue (a 2) * goldValue (b 0)] i := by
  have seven : goldValue (7 : GoldWord) = (7 : Goldilocks) := rfl
  fin_cases i <;>
    simp [mul, NativeGoldArithmetic.add_value, NativeGoldArithmetic.sub_value,
      NativeGoldArithmetic.mul_value, seven] <;> ring

theorem mul_value (a b : Word) :
    goldExtensionValue (mul a b) = goldExtensionValue a * goldExtensionValue b := by
  rw [value_expansion, value_expansion a, value_expansion b]
  simp only [mul_coordinates, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    map_add, map_mul, map_ofNat]
  linear_combination
    -(algebraMap Goldilocks Goldilocks3 (goldValue (a 1)) *
      algebraMap Goldilocks Goldilocks3 (goldValue (b 2)) +
      algebraMap Goldilocks Goldilocks3 (goldValue (a 2)) *
      algebraMap Goldilocks Goldilocks3 (goldValue (b 1))) * generator_cube -
    (algebraMap Goldilocks Goldilocks3 (goldValue (a 2)) *
      algebraMap Goldilocks Goldilocks3 (goldValue (b 2))) * generator * generator_cube

end

end FormalProof4FHE.HasteBoots.NativeGoldCubic
