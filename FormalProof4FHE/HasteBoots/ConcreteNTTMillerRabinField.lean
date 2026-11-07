module
public import FormalProof4FHE.HasteBoots.ConcreteNTTRootConstruction
public import Mathlib.FieldTheory.Finite.Basic
@[expose] public section

/-! Field semantics of the native Miller-Rabin initial test and subsequent
squares. Prime-field completeness is proved; deterministic soundness of the
particular twelve-base composite test is a separate statement. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinField
variable {F : Type} [Field F] [DecidableEq F]

def squares : ℕ → F → Bool
  | 0,_ => false
  | remaining+1,x =>
    let next := x*x
    if next = -1 then true else squares remaining next

def check (s : ℕ) (x : F) : Bool :=
  if x = 1 ∨ x = -1 then true else squares (s-1) x

theorem check_of_power (s : ℕ) (x : F) (power : x^(2^s) = 1) : check s x = true := by
  induction s generalizing x with
  | zero =>
    have one : x = 1 := by simpa only [pow_zero,pow_one] using power
    simp only [check,one,true_or,ite_true]
  | succ s ih =>
    by_cases initial : x = 1 ∨ x = -1
    · simp only [check,initial,ite_true]
    · have notOne : x*x ≠ 1 := by
        intro square
        exact initial (mul_self_eq_one_iff.mp square)
      have nextPower : (x*x)^(2^s) = 1 := by
        rw [← pow_two,← pow_mul]
        have exponents : 2*2^s = 2^(s+1) := by rw [Nat.pow_succ]; omega
        rw [exponents]
        exact power
      have next := ih (x*x) nextPower
      simp only [check,initial,ite_false,Nat.add_sub_cancel]
      by_cases positive : 0 < s
      · rw [show s = (s-1)+1 by omega,squares]
        split
        · rfl
        · rename_i notNegative
          simpa only [check,notOne,notNegative,false_or,ite_false] using next
      · have zero : s = 0 := by omega
        rw [zero,pow_zero,pow_one] at nextPower
        exact (notOne nextPower).elim

theorem prime_round (modulus q s : ℕ) [Fact (Nat.Prime modulus)] (base : ZMod modulus)
    (nonzero : base ≠ 0) (decomposition : modulus-1 = q*2^s) : check s (base^q) = true := by
  apply check_of_power
  rw [← pow_mul,← decomposition]
  exact ZMod.pow_card_sub_one_eq_one nonzero

end FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinField
