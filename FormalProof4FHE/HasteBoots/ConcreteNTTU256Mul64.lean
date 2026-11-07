module
public import FormalProof4FHE.HasteBoots.ConcreteNTTLimbArithmetic
@[expose] public section

/-! Four literal chained mul_with_carry calls implementing concrete-ntt
u256::mul_u256_u64. Low and high results are proved against the complete
320-bit mathematical product. Native Rust layout, instructions, compiler and
physical cost remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul64
open ConcreteNTTLimbArithmetic (radix Limb mulCarry)

structure Word where
  x0 : Limb
  x1 : Limb
  x2 : Limb
  x3 : Limb
  deriving DecidableEq, Repr

def value (word : Word) : ℕ := word.x0.val+radix*(word.x1.val+radix*(word.x2.val+radix*word.x3.val))
def limit : ℕ := radix^4

theorem value_lt (word : Word) : value word < limit := by
  have h0 := word.x0.isLt
  have h1 := word.x1.isLt
  have h2 := word.x2.isLt
  have h3 := word.x3.isLt
  norm_num [value,limit,radix] at h0 h1 h2 h3 ⊢
  omega

def multiply (word : Word) (right : Limb) : Word × Limb :=
  let a := mulCarry word.x0 right 0
  let b := mulCarry word.x1 right a.2
  let c := mulCarry word.x2 right b.2
  let d := mulCarry word.x3 right c.2
  (⟨a.1,b.1,c.1,d.1⟩,d.2)

theorem multiply_value (word : Word) (right : Limb) :
    value (multiply word right).1+limit*(multiply word right).2.val = value word*right.val := by
  let a := mulCarry word.x0 right 0
  let b := mulCarry word.x1 right a.2
  let c := mulCarry word.x2 right b.2
  let d := mulCarry word.x3 right c.2
  have h0 := ConcreteNTTLimbArithmetic.mulCarry_value word.x0 right 0
  have h1 := congrArg (fun n => radix*n) (ConcreteNTTLimbArithmetic.mulCarry_value word.x1 right a.2)
  have h2 := congrArg (fun n => radix^2*n) (ConcreteNTTLimbArithmetic.mulCarry_value word.x2 right b.2)
  have h3 := congrArg (fun n => radix^3*n) (ConcreteNTTLimbArithmetic.mulCarry_value word.x3 right c.2)
  change value (⟨a.1,b.1,c.1,d.1⟩ : Word)+limit*d.2.val = value word*right.val
  dsimp only [value,limit]
  change a.1.val+radix*a.2.val = word.x0.val*right.val+0 at h0
  change radix*(b.1.val+radix*b.2.val) = radix*(word.x1.val*right.val+a.2.val) at h1
  change radix^2*(c.1.val+radix*c.2.val) = radix^2*(word.x2.val*right.val+b.2.val) at h2
  change radix^3*(d.1.val+radix*d.2.val) = radix^3*(word.x3.val*right.val+c.2.val) at h3
  nlinarith only [h0,h1,h2,h3]

theorem multiply_low (word : Word) (right : Limb) :
    value (multiply word right).1 = value word*right.val%limit := by
  have exactProduct := multiply_value word right
  rw [← exactProduct,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (value_lt (multiply word right).1)]

theorem multiply_high (word : Word) (right : Limb) :
    (multiply word right).2.val = value word*right.val/limit := by
  have exactProduct := multiply_value word right
  rw [← exactProduct,Nat.add_mul_div_left _ _ (by decide : 0 < limit),
    Nat.div_eq_of_lt (value_lt (multiply word right).1),Nat.zero_add]

theorem multiply_high_lt (word : Word) (right : Limb) (positive : 0 < right.val) :
    (multiply word right).2.val < right.val := by
  rw [multiply_high]
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < limit)).mpr
  have bound := Nat.mul_lt_mul_of_pos_right (value_lt word) positive
  simpa only [Nat.mul_comm limit right.val] using bound

/-- The later u256-by-u128 routine may increment this high limb once. -/
theorem multiply_high_increment_fits (word : Word) (right : Limb) :
    (multiply word right).2.val+1 < radix := by
  by_cases zero : right.val = 0
  · rw [multiply_high,zero,Nat.mul_zero,Nat.zero_div]
    decide
  · have high := multiply_high_lt word right (Nat.pos_of_ne_zero zero)
    have bound := right.isLt
    omega

theorem limit_eq : limit = ConcreteNTTDiv64.reciprocalLimit := by decide

/-- The actual high carry is the high-product extraction used by fastdiv. -/
theorem fastdiv_high (word : Word) (right : Limb) :
    (multiply word right).2.val = value word*right.val/ConcreteNTTDiv64.reciprocalLimit := by
  rw [multiply_high,limit_eq]

end FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul64
