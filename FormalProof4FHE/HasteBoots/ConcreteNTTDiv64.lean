module
public import FormalProof4FHE.HasteBoots.ReciprocalRemainder
public import Mathlib.Data.ZMod.Basic
@[expose] public section

/-! Natural-word formula for concrete-ntt Div64::new, rem_u128 and mul_mod64
at cdeba793e46208320b30d78be19f7be78d49016a. Reciprocal wrapping and the high
product extraction are explicit. u256 limb routines, u128 machine operations,
compiler/Rust equivalence and physical cost remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTDiv64

def wordLimit : ℕ := 2^64
def wideLimit : ℕ := 2^128
def reciprocalLimit : ℕ := 2^256

def reciprocal (divisor : ℕ) : ℕ :=
  (ReciprocalRemainder.reciprocal reciprocalLimit divisor)%reciprocalLimit

def rem (divisor input : ℕ) : ℕ :=
  ((reciprocal divisor*input)%reciprocalLimit*divisor)/reciprocalLimit

theorem reciprocal_unwrapped (divisor : ℕ) (valid : 1 < divisor) :
    reciprocal divisor = ReciprocalRemainder.reciprocal reciprocalLimit divisor := by
  apply Nat.mod_eq_of_lt
  exact ReciprocalRemainder.reciprocal_lt reciprocalLimit divisor (by decide) valid

theorem input_error_bound (divisor input : ℕ) (valid : 1 < divisor)
    (divisorFits : divisor < wordLimit) (inputFits : input < wideLimit) :
    (ReciprocalRemainder.reciprocal reciprocalLimit divisor*divisor-reciprocalLimit)*input < reciprocalLimit := by
  apply ReciprocalRemainder.error_bound reciprocalLimit divisor input (by decide) (by omega)
  calc
    input*divisor ≤ wideLimit*wordLimit := Nat.mul_le_mul inputFits.le divisorFits.le
    _ ≤ reciprocalLimit := by decide

theorem rem_eq (divisor input : ℕ) (valid : 1 < divisor)
    (divisorFits : divisor < wordLimit) (inputFits : input < wideLimit) : rem divisor input = input%divisor := by
  rw [rem,reciprocal_unwrapped divisor valid]
  exact ReciprocalRemainder.remainder_eq reciprocalLimit divisor input (by decide) (by omega)
    (input_error_bound divisor input valid divisorFits inputFits)

theorem rem_lt (divisor input : ℕ) (valid : 1 < divisor)
    (divisorFits : divisor < wordLimit) (inputFits : input < wideLimit) : rem divisor input < divisor := by
  rw [rem_eq divisor input valid divisorFits inputFits]
  exact Nat.mod_lt input (by omega)

def mulMod (divisor left right : ℕ) : ℕ := rem divisor (left*right)

theorem product_fits (left right : ℕ) (leftFits : left < wordLimit) (rightFits : right < wordLimit) :
    left*right < wideLimit := by
  calc
    left*right ≤ (wordLimit-1)*(wordLimit-1) := Nat.mul_le_mul (by omega) (by omega)
    _ < wideLimit := by decide

theorem mulMod_eq (divisor left right : ℕ) (valid : 1 < divisor) (divisorFits : divisor < wordLimit)
    (leftFits : left < wordLimit) (rightFits : right < wordLimit) : mulMod divisor left right = left*right%divisor :=
  rem_eq divisor (left*right) valid divisorFits (product_fits left right leftFits rightFits)

theorem mulMod_lt (divisor left right : ℕ) (valid : 1 < divisor) (divisorFits : divisor < wordLimit)
    (leftFits : left < wordLimit) (rightFits : right < wordLimit) : mulMod divisor left right < divisor := by
  rw [mulMod_eq divisor left right valid divisorFits leftFits rightFits]
  exact Nat.mod_lt _ (by omega)

theorem mulMod_cast (divisor left right : ℕ) (valid : 1 < divisor) (divisorFits : divisor < wordLimit)
    (leftFits : left < wordLimit) (rightFits : right < wordLimit) :
    (mulMod divisor left right : ZMod divisor) = (left : ZMod divisor)*(right : ZMod divisor) := by
  rw [mulMod_eq divisor left right valid divisorFits leftFits rightFits,ZMod.natCast_mod,Nat.cast_mul]

end FormalProof4FHE.HasteBoots.ConcreteNTTDiv64
