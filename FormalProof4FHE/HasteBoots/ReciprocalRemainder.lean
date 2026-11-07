module
public import Mathlib.Tactic
@[expose] public section

/-! Integer correctness of wrapped reciprocal remainder reduction. This isolates
the mathematical formula used by concrete-ntt Div64 from limb/instruction
refinement. It does not assume the formula already computes a remainder. -/
namespace FormalProof4FHE.HasteBoots.ReciprocalRemainder

def reciprocal (radix divisor : ℕ) : ℕ := (radix-1)/divisor+1

theorem reciprocal_bounds (radix divisor : ℕ) (positive : 0 < radix) (nonzero : 0 < divisor) :
    radix ≤ reciprocal radix divisor*divisor ∧ reciprocal radix divisor*divisor < radix+divisor := by
  have divided := Nat.mod_add_div (radix-1) divisor
  have remainder := Nat.mod_lt (radix-1) nonzero
  rw [Nat.mul_comm divisor ((radix-1)/divisor)] at divided
  simp only [reciprocal,Nat.add_mul,Nat.one_mul]
  omega

theorem reciprocal_lt (radix divisor : ℕ) (radixBound : 1 < radix) (divisorBound : 1 < divisor) :
    reciprocal radix divisor < radix := by
  have divided : (radix-1)/divisor < radix-1 := Nat.div_lt_self (by omega) divisorBound
  simp only [reciprocal]
  omega

/-- The reciprocal product's quotient equals the original division quotient. -/
theorem quotient (radix divisor input : ℕ) (radixPositive : 0 < radix) (divisorPositive : 0 < divisor)
    (errorBound : (reciprocal radix divisor*divisor-radix)*input < radix) :
    reciprocal radix divisor*input/radix = input/divisor := by
  let error := reciprocal radix divisor*divisor-radix
  let product := reciprocal radix divisor*input
  have lowerReciprocal := (reciprocal_bounds radix divisor radixPositive divisorPositive).1
  have reciprocalEq : reciprocal radix divisor*divisor = radix+error := by dsimp only [error]; omega
  have productEq : product*divisor = radix*input+error*input := by
    dsimp only [product]
    calc
      reciprocal radix divisor*input*divisor = (reciprocal radix divisor*divisor)*input := by ring
      _ = radix*input+error*input := by rw [reciprocalEq]; ring
  have original := Nat.mod_add_div input divisor
  have remainder := Nat.mod_lt input divisorPositive
  have tailBound : radix*(input%divisor)+error*input < radix*divisor := by
    change error*input < radix at errorBound
    nlinarith
  have expanded : product*divisor = (radix*(input/divisor))*divisor + (radix*(input%divisor)+error*input) := by
    rw [productEq]
    nlinarith [congrArg (fun n => radix*n) original]
  have lowerMult : (input/divisor*radix)*divisor ≤ product*divisor := by
    calc
      (input/divisor*radix)*divisor = (radix*(input/divisor))*divisor := by ring
      _ ≤ (radix*(input/divisor))*divisor + (radix*(input%divisor)+error*input) := Nat.le_add_right _ _
      _ = product*divisor := expanded.symm
  have lower : input/divisor*radix ≤ product := Nat.le_of_mul_le_mul_right lowerMult divisorPositive
  have upperMult : product*divisor < ((input/divisor+1)*radix)*divisor := by
    rw [expanded]
    calc
      _ < (radix*(input/divisor))*divisor + radix*divisor := Nat.add_lt_add_left tailBound _
      _ = ((input/divisor+1)*radix)*divisor := by ring
  have upper : product < (input/divisor+1)*radix := (Nat.mul_lt_mul_right divisorPositive).mp upperMult
  change product/radix = input/divisor
  apply Nat.le_antisymm
  · have bounded := (Nat.div_lt_iff_lt_mul radixPositive).mpr upper
    omega
  · exact (Nat.le_div_iff_mul_le radixPositive).mpr lower

def remainder (radix divisor input : ℕ) : ℕ :=
  ((reciprocal radix divisor*input)%radix*divisor)/radix

theorem remainder_eq (radix divisor input : ℕ) (radixPositive : 0 < radix) (divisorPositive : 0 < divisor)
    (errorBound : (reciprocal radix divisor*divisor-radix)*input < radix) :
    remainder radix divisor input = input%divisor := by
  let error := reciprocal radix divisor*divisor-radix
  let product := reciprocal radix divisor*input
  have lower := (reciprocal_bounds radix divisor radixPositive divisorPositive).1
  have reciprocalEq : reciprocal radix divisor*divisor = radix+error := by dsimp only [error]; omega
  have productEq : product*divisor = radix*input+error*input := by
    dsimp only [product]
    calc
      reciprocal radix divisor*input*divisor = (reciprocal radix divisor*divisor)*input := by ring
      _ = radix*input+error*input := by rw [reciprocalEq]; ring
  have sameQuotient := quotient radix divisor input radixPositive divisorPositive errorBound
  change product/radix = input/divisor at sameQuotient
  have original := congrArg (fun n => radix*n) (Nat.mod_add_div input divisor)
  have wrapped := congrArg (fun n => n*divisor) (Nat.mod_add_div product radix)
  rw [sameQuotient] at wrapped
  have low : product%radix*divisor = radix*(input%divisor)+error*input := by nlinarith
  change (product%radix*divisor)/radix = input%divisor
  rw [low,Nat.mul_add_div radixPositive,Nat.div_eq_of_lt errorBound,Nat.add_zero]

/-- A sufficient public word-range condition for the strict error bound. -/
theorem error_bound (radix divisor input : ℕ) (radixPositive : 0 < radix) (divisorPositive : 0 < divisor)
    (range : input*divisor ≤ radix) : (reciprocal radix divisor*divisor-radix)*input < radix := by
  have bounds := reciprocal_bounds radix divisor radixPositive divisorPositive
  have error : reciprocal radix divisor*divisor-radix < divisor := by omega
  by_cases zero : input = 0
  · simp only [zero,Nat.mul_zero]; exact radixPositive
  · have strict := Nat.mul_lt_mul_of_pos_right error (Nat.pos_of_ne_zero zero)
    nlinarith
end FormalProof4FHE.HasteBoots.ReciprocalRemainder
