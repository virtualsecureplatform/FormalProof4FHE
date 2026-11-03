module

public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# Checked Goldilocks and BabyBear field parameters

These moduli match algebra/src/modulus/{goldilocks,baby_bear}/mod.rs.
Lucas certificates prove primality using complete factorizations of p-1 and
kernel-checked fast modular exponentiation. No primality or native-evaluation
axiom is used. Relating native lazy/Montgomery integers to ZMod remains open.
-/

namespace FormalProof4FHE.HasteBoots.NativeFields

def goldilocksModulus : ℕ := 18446744069414584321
def babyBearModulus : ℕ := 2013265921

theorem goldilocks_prime : goldilocksModulus.Prime := by
  change Nat.Prime 18446744069414584321
  apply lucas_primality _ (7 : ZMod 18446744069414584321)
  · reduce_mod_char
  · intro q prime divides
    have factored : q ∣ 2 ^ 32 * 3 * 5 * 17 * 257 * 65537 := by norm_num at divides ⊢; exact divides
    have two : q ∣ 2 ^ 32 ↔ q = 2 := by
      constructor
      · intro factor
        exact (Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp (prime.dvd_of_dvd_pow factor)
      · rintro rfl
        exact dvd_pow_self 2 (by decide)
    have small (p : ℕ) (hp : p.Prime) : q ∣ p ↔ q = p := Nat.prime_dvd_prime_iff_eq prime hp
    have alternatives : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 17 ∨ q = 257 ∨ q = 65537 := by
      simpa only [prime.dvd_mul, two, small 3 (by norm_num), small 5 (by norm_num), small 17 (by norm_num),
        small 257 (by norm_num), small 65537 (by norm_num), or_assoc] using factored
    rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide

theorem babyBear_prime : babyBearModulus.Prime := by
  change Nat.Prime 2013265921
  apply lucas_primality _ (31 : ZMod 2013265921)
  · reduce_mod_char
  · intro q prime divides
    have factored : q ∣ 2 ^ 27 * 3 * 5 := by norm_num at divides ⊢; exact divides
    have two : q ∣ 2 ^ 27 ↔ q = 2 := by
      constructor
      · intro factor
        exact (Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp (prime.dvd_of_dvd_pow factor)
      · rintro rfl
        exact dvd_pow_self 2 (by decide)
    have alternatives : q = 2 ∨ q = 3 ∨ q = 5 := by
      simpa only [prime.dvd_mul, two, Nat.prime_dvd_prime_iff_eq prime (by norm_num : Nat.Prime 3),
        Nat.prime_dvd_prime_iff_eq prime (by norm_num : Nat.Prime 5), or_assoc] using factored
    rcases alternatives with rfl | rfl | rfl <;> reduce_mod_char <;> decide

theorem goldilocks_top_arithmetic : (1753635133440165772 : ZMod 18446744069414584321) ^ 2147483648 = -1 := by
  reduce_mod_char

theorem babyBear_top_arithmetic : (1538287591 : ZMod 2013265921) ^ 67108864 = -1 := by
  reduce_mod_char

theorem goldilocks_main_arithmetic : (455906449640507599 : ZMod 18446744069414584321) = 1753635133440165772 ^ 2097152 := by
  reduce_mod_char

theorem babyBear_main_arithmetic : (812423803 : ZMod 2013265921) = 1538287591 ^ 65536 := by
  reduce_mod_char

instance : Fact goldilocksModulus.Prime := ⟨goldilocks_prime⟩
instance : Fact babyBearModulus.Prime := ⟨babyBear_prime⟩

abbrev Goldilocks := ZMod goldilocksModulus
abbrev BabyBear := ZMod babyBearModulus

theorem goldilocks_card : Fintype.card Goldilocks = goldilocksModulus := ZMod.card _
theorem babyBear_card : Fintype.card BabyBear = babyBearModulus := ZMod.card _

theorem goldilocks_odd : (-1 : Goldilocks) ≠ 1 := by unfold Goldilocks goldilocksModulus; reduce_mod_char; decide
theorem babyBear_odd : (-1 : BabyBear) ≠ 1 := by unfold BabyBear babyBearModulus; reduce_mod_char; decide

end FormalProof4FHE.HasteBoots.NativeFields
