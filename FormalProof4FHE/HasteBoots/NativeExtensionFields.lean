module

public import FormalProof4FHE.HasteBoots.NativeFields
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-!
# Checked defining polynomials for the native challenge extensions

The native challenge fields use X^3-7 over Goldilocks and X^6-31 over
BabyBear. These are separate from the degree-4/8 PCS extensions. Kernel
checked non-power witnesses prove irreducibility; no primitive-generator
capability or composed security bound is inferred from field size.
Native lazy/Montgomery representation correspondence remains separate.
-/

namespace FormalProof4FHE.HasteBoots.NativeExtensionFields

open Polynomial NativeFields

noncomputable section

theorem no_power_of_witness {p degree : ℕ} [Fact p.Prime] (a : ZMod p)
    (nonzero : a ≠ 0) (positive : 0 < degree) (divides : degree ∣ p - 1)
    (witness : a ^ ((p - 1) / degree) ≠ 1) : ∀ b : ZMod p, b ^ degree ≠ a := by
  intro b equal
  have bne : b ≠ 0 := by
    intro zero
    apply nonzero
    rw [← equal, zero, zero_pow (Nat.ne_of_gt positive)]
  apply witness
  rw [← equal, ← pow_mul, Nat.mul_div_cancel' divides]
  exact ZMod.pow_card_sub_one_eq_one bne

theorem goldilocks_seven_not_cube : ∀ b : Goldilocks, b ^ 3 ≠ 7 := by
  apply no_power_of_witness (7 : Goldilocks)
  · unfold Goldilocks goldilocksModulus
    reduce_mod_char
    decide
  · decide
  · decide
  · unfold Goldilocks goldilocksModulus
    reduce_mod_char
    decide

theorem babyBear_thirtyOne_not_cube : ∀ b : BabyBear, b ^ 3 ≠ 31 := by
  apply no_power_of_witness (31 : BabyBear)
  · unfold BabyBear babyBearModulus
    reduce_mod_char
    decide
  · decide
  · decide
  · unfold BabyBear babyBearModulus
    reduce_mod_char
    decide

theorem babyBear_thirtyOne_not_square : ∀ b : BabyBear, b ^ 2 ≠ 31 := by
  apply no_power_of_witness (31 : BabyBear)
  · unfold BabyBear babyBearModulus
    reduce_mod_char
    decide
  · decide
  · decide
  · unfold BabyBear babyBearModulus
    reduce_mod_char
    decide

abbrev goldilocksPolynomial : Polynomial Goldilocks := X ^ 3 - C 7
abbrev babyBearCubic : Polynomial BabyBear := X ^ 3 - C 31
abbrev babyBearPolynomial : Polynomial BabyBear := X ^ 6 - C 31

theorem goldilocks_irreducible : Irreducible goldilocksPolynomial :=
  X_pow_sub_C_irreducible_of_prime (by decide : Nat.Prime 3) goldilocks_seven_not_cube

theorem babyBear_cubic_irreducible : Irreducible babyBearCubic :=
  X_pow_sub_C_irreducible_of_prime (by decide : Nat.Prime 3) babyBear_thirtyOne_not_cube

theorem babyBear_irreducible : Irreducible babyBearPolynomial := by
  let : Fact (Irreducible babyBearCubic) := ⟨babyBear_cubic_irreducible⟩
  have quadratic : Irreducible (X ^ 2 - C (AdjoinRoot.root babyBearCubic)) := by
    apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro b equal
    apply babyBear_thirtyOne_not_square (Algebra.norm BabyBear b)
    rw [← map_pow, equal]
    change Algebra.norm BabyBear (AdjoinRoot.root ((X : Polynomial BabyBear) ^ 3 - C 31)) = 31
    rw [norm_root_X_pow_sub_C (by decide : (3 : ℕ) ≠ 0)]
    norm_num
  change Irreducible (X ^ (2 * 3) - C (31 : BabyBear))
  exact X_pow_mul_sub_C_irreducible babyBear_cubic_irreducible quadratic

instance : Fact (Irreducible goldilocksPolynomial) := ⟨goldilocks_irreducible⟩
instance : Fact (Irreducible babyBearPolynomial) := ⟨babyBear_irreducible⟩

abbrev Goldilocks3 := AdjoinRoot goldilocksPolynomial
abbrev BabyBear6 := AdjoinRoot babyBearPolynomial

def goldilocksBasis : Module.Basis (Fin 3) Goldilocks Goldilocks3 :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C (7 : Goldilocks) (by decide : (3 : ℕ) ≠ 0))).basis.reindex
    (finCongr (by simp))

def babyBearBasis : Module.Basis (Fin 6) BabyBear BabyBear6 :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C (31 : BabyBear) (by decide : (6 : ℕ) ≠ 0))).basis.reindex
    (finCongr (by simp))

theorem goldilocks_basis_power (i : Fin 3) :
    goldilocksBasis i = AdjoinRoot.root goldilocksPolynomial ^ i.val := by
  simp only [goldilocksBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

theorem babyBear_basis_power (i : Fin 6) :
    babyBearBasis i = AdjoinRoot.root babyBearPolynomial ^ i.val := by
  simp only [babyBearBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

instance : Fintype Goldilocks3 := Fintype.ofEquiv (Fin 3 → Goldilocks) goldilocksBasis.equivFun.symm.toEquiv
instance : Fintype BabyBear6 := Fintype.ofEquiv (Fin 6 → BabyBear) babyBearBasis.equivFun.symm.toEquiv

theorem goldilocks_card : Fintype.card Goldilocks3 = goldilocksModulus ^ 3 := by
  rw [Fintype.card_congr goldilocksBasis.equivFun.toEquiv, Fintype.card_fun, NativeFields.goldilocks_card,
    Fintype.card_fin]

theorem babyBear_card : Fintype.card BabyBear6 = babyBearModulus ^ 6 := by
  rw [Fintype.card_congr babyBearBasis.equivFun.toEquiv, Fintype.card_fun, NativeFields.babyBear_card,
    Fintype.card_fin]

end

end FormalProof4FHE.HasteBoots.NativeExtensionFields
