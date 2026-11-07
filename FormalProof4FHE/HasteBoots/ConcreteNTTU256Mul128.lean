module
public import FormalProof4FHE.HasteBoots.ConcreteNTTU256Add
@[expose] public section

/-! Literal wrapping_mul_u256_u128: two u256-by-u64 products, a one-limb
shift dropping the old high limb, and wrapping addition. This closes the low
product and final high-carry formulas used by rem_u128. Reciprocal initialization,
actual Rust instructions/compiler and physical refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul128
open ConcreteNTTLimbArithmetic (radix Limb radix_pos)
open ConcreteNTTU256Mul64 (Word value limit value_lt multiply)
abbrev Wide := Fin (radix^2)

def low (right : Wide) : Limb := ⟨right.val%radix,Nat.mod_lt _ radix_pos⟩
def high (right : Wide) : Limb := ⟨right.val/radix,(Nat.div_lt_iff_lt_mul radix_pos).mpr (by simpa only [pow_two] using right.isLt)⟩

theorem parts_value (right : Wide) : (low right).val+radix*(high right).val = right.val := Nat.mod_add_div _ _

def shift64 (word : Word) : Word := ⟨0,word.x0,word.x1,word.x2⟩

theorem shift_value (word : Word) : value (shift64 word)+limit*word.x3.val = value word*radix := by
  simp only [shift64,value,limit,Fin.val_zero]
  ring

theorem shift_low (word : Word) : value (shift64 word) = value word*radix%limit := by
  rw [← shift_value word,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (value_lt (shift64 word))]

def wrappingMultiply (left : Word) (right : Wide) : Word :=
  let x := multiply left (low right)
  let y := multiply left (high right)
  (ConcreteNTTU256Add.add x.1 (shift64 y.1)).1

theorem wrappingMultiply_value (left : Word) (right : Wide) :
    value (wrappingMultiply left right) = value left*right.val%limit := by
  simp only [wrappingMultiply,ConcreteNTTU256Add.add_low,shift_low,ConcreteNTTU256Mul64.multiply_low]
  have exactProduct : value left*(low right).val+value left*(high right).val*radix = value left*right.val := by
    calc
      _ = value left*((low right).val+radix*(high right).val) := by ring
      _ = value left*right.val := by rw [parts_value]
  calc
    _ = (value left*(low right).val+value left*(high right).val*radix)%limit := by
      simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_mod]
    _ = value left*right.val%limit := by rw [exactProduct]

def remainder (reciprocal : Word) (divisor : Limb) (input : Wide) : Limb :=
  (multiply (wrappingMultiply reciprocal input) divisor).2

theorem remainder_formula (reciprocal : Word) (divisor : Limb) (input : Wide) :
    (remainder reciprocal divisor input).val =
      ((value reciprocal*input.val)%ConcreteNTTDiv64.reciprocalLimit*divisor.val)/ConcreteNTTDiv64.reciprocalLimit := by
  simp only [remainder,ConcreteNTTU256Mul64.multiply_high,wrappingMultiply_value,ConcreteNTTU256Mul64.limit_eq]

/-- The remaining initialization relation is explicit, rather than a supplied
remainder or multiplication correctness callback. -/
theorem remainder_eq (reciprocal : Word) (divisor : Limb) (input : Wide) (valid : 1 < divisor.val)
    (initialized : value reciprocal = ConcreteNTTDiv64.reciprocal divisor.val) :
    (remainder reciprocal divisor input).val = input.val%divisor.val := by
  rw [remainder_formula,initialized]
  exact ConcreteNTTDiv64.rem_eq divisor.val input.val valid divisor.isLt input.isLt

end FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul128
