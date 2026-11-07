module
public import FormalProof4FHE.HasteBoots.ConcreteNTTDiv64
@[expose] public section

/-! Natural-word semantics of concrete-ntt prime::exp_mod64 at locked revision
cdeba793e46208320b30d78be19f7be78d49016a. The original odd multiply, square,
halve, final multiply and exponent-zero exit use the proved reciprocal reducer.
No modular multiplication callback is supplied. u256 limbs/instructions,
u64 comparisons/shifts, Rust refinement and physical cost remain open. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTModularPower
open ConcreteNTTDiv64 (wordLimit mulMod)

def loop (divisor exponent x y : ℕ) : ℕ :=
  if exponent ≤ 1 then mulMod divisor x y else
    let nextY := if exponent%2 = 1 then mulMod divisor x y else y
    loop divisor (exponent/2) (mulMod divisor x x) nextY
termination_by exponent
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

def power (divisor base exponent : ℕ) : ℕ :=
  if exponent = 0 then 1 else loop divisor exponent base 1

theorem loop_cast (divisor exponent x y : ℕ) (valid : 1 < divisor) (divisorFits : divisor < wordLimit)
    (positive : 0 < exponent) (xFits : x < wordLimit) (yFits : y < wordLimit) :
    (loop divisor exponent x y : ZMod divisor) = (x : ZMod divisor)^exponent*(y : ZMod divisor) := by
  induction exponent using Nat.strong_induction_on generalizing x y with
  | h exponent ih =>
    rw [loop]
    split
    · rename_i small
      have one : exponent = 1 := by omega
      simpa only [one,pow_one] using ConcreteNTTDiv64.mulMod_cast divisor x y valid divisorFits xFits yFits
    · rename_i large
      have halfPositive : 0 < exponent/2 := by omega
      have halfSmaller : exponent/2 < exponent := Nat.div_lt_self positive (by decide)
      have nextX := (ConcreteNTTDiv64.mulMod_lt divisor x x valid divisorFits xFits xFits).trans divisorFits
      have castX := ConcreteNTTDiv64.mulMod_cast divisor x x valid divisorFits xFits xFits
      by_cases odd : exponent%2 = 1
      · simp only [odd,ite_true]
        have nextY := (ConcreteNTTDiv64.mulMod_lt divisor x y valid divisorFits xFits yFits).trans divisorFits
        rw [ih (exponent/2) halfSmaller _ _ halfPositive nextX nextY,castX,
          ConcreteNTTDiv64.mulMod_cast divisor x y valid divisorFits xFits yFits]
        have count : 2*(exponent/2)+1 = exponent := by omega
        calc
          ((x : ZMod divisor)*x)^(exponent/2)*(x*y) = (x : ZMod divisor)^(2*(exponent/2)+1)*y := by
            rw [pow_succ,pow_mul,pow_two]
            ring
          _ = (x : ZMod divisor)^exponent*y := by rw [count]
      · simp only [odd,ite_false]
        rw [ih (exponent/2) halfSmaller _ _ halfPositive nextX yFits,castX]
        have count : 2*(exponent/2) = exponent := by omega
        rw [← pow_two,← pow_mul,count]

theorem loop_lt (divisor exponent x y : ℕ) (valid : 1 < divisor) (divisorFits : divisor < wordLimit)
    (xFits : x < wordLimit) (yFits : y < wordLimit) : loop divisor exponent x y < divisor := by
  induction exponent using Nat.strong_induction_on generalizing x y with
  | h exponent ih =>
    rw [loop]
    split
    · exact ConcreteNTTDiv64.mulMod_lt divisor x y valid divisorFits xFits yFits
    · rename_i large
      have smaller : exponent/2 < exponent := Nat.div_lt_self (by omega) (by decide)
      have nextX := (ConcreteNTTDiv64.mulMod_lt divisor x x valid divisorFits xFits xFits).trans divisorFits
      dsimp only
      apply ih (exponent/2) smaller _ _ nextX
      split
      · exact (ConcreteNTTDiv64.mulMod_lt divisor x y valid divisorFits xFits yFits).trans divisorFits
      · exact yFits

theorem power_cast (divisor base exponent : ℕ) (valid : 1 < divisor) (divisorFits : divisor < wordLimit)
    (baseFits : base < wordLimit) : (power divisor base exponent : ZMod divisor) = (base : ZMod divisor)^exponent := by
  simp only [power]
  split
  · rename_i zero
    simp only [zero,pow_zero,Nat.cast_one]
  · rename_i positive
    rw [loop_cast divisor exponent base 1 valid divisorFits (by omega) baseFits (by decide),Nat.cast_one,mul_one]

theorem power_lt (divisor base exponent : ℕ) (valid : 1 < divisor) (divisorFits : divisor < wordLimit)
    (baseFits : base < wordLimit) : power divisor base exponent < divisor := by
  simp only [power]
  split
  · exact valid
  · exact loop_lt divisor exponent base 1 valid divisorFits baseFits (by decide)

theorem power_eq (divisor base exponent : ℕ) (valid : 1 < divisor) (divisorFits : divisor < wordLimit)
    (baseFits : base < wordLimit) : power divisor base exponent = base^exponent%divisor := by
  let : NeZero divisor := ⟨by omega⟩
  have value := power_cast divisor base exponent valid divisorFits baseFits
  rw [← Nat.cast_pow] at value
  have same := congrArg ZMod.val value
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (power_lt divisor base exponent valid divisorFits baseFits)] using same

end FormalProof4FHE.HasteBoots.ConcreteNTTModularPower
