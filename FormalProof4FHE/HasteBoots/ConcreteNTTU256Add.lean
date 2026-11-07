module
public import FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul64
public import FormalProof4FHE.HasteBoots.ConcreteNTTLimbAdd
@[expose] public section

/-! Original ordered four-limb adc chain for u256::overflowing_add and
wrapping_add. Native layout/instruction/compiler and physical refinement remain
separate from the exact bounded-word arithmetic identity. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTU256Add
open ConcreteNTTLimbArithmetic (radix)
open ConcreteNTTLimbAdd (adc)
open ConcreteNTTU256Mul64 (Word value limit value_lt)

def add (left right : Word) : Word × Bool :=
  let a := adc left.x0 right.x0 false
  let b := adc left.x1 right.x1 a.2
  let c := adc left.x2 right.x2 b.2
  let d := adc left.x3 right.x3 c.2
  (⟨a.1,b.1,c.1,d.1⟩,d.2)

theorem add_value (left right : Word) :
    value (add left right).1+limit*(if (add left right).2 then 1 else 0) = value left+value right := by
  let a := adc left.x0 right.x0 false
  let b := adc left.x1 right.x1 a.2
  let c := adc left.x2 right.x2 b.2
  let d := adc left.x3 right.x3 c.2
  have h0 := ConcreteNTTLimbAdd.adc_value left.x0 right.x0 false
  have h1 := congrArg (fun n => radix*n) (ConcreteNTTLimbAdd.adc_value left.x1 right.x1 a.2)
  have h2 := congrArg (fun n => radix^2*n) (ConcreteNTTLimbAdd.adc_value left.x2 right.x2 b.2)
  have h3 := congrArg (fun n => radix^3*n) (ConcreteNTTLimbAdd.adc_value left.x3 right.x3 c.2)
  change value (⟨a.1,b.1,c.1,d.1⟩ : Word)+limit*(if d.2 then 1 else 0) = value left+value right
  dsimp only [value,limit]
  change a.1.val+radix*(if a.2 then 1 else 0) = left.x0.val+right.x0.val+0 at h0
  change radix*(b.1.val+radix*(if b.2 then 1 else 0)) = radix*(left.x1.val+right.x1.val+(if a.2 then 1 else 0)) at h1
  change radix^2*(c.1.val+radix*(if c.2 then 1 else 0)) = radix^2*(left.x2.val+right.x2.val+(if b.2 then 1 else 0)) at h2
  change radix^3*(d.1.val+radix*(if d.2 then 1 else 0)) = radix^3*(left.x3.val+right.x3.val+(if c.2 then 1 else 0)) at h3
  nlinarith only [h0,h1,h2,h3]

theorem add_low (left right : Word) : value (add left right).1 = (value left+value right)%limit := by
  rw [← add_value left right,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (value_lt (add left right).1)]

theorem add_overflow (left right : Word) : (add left right).2 = true ↔ limit ≤ value left+value right := by
  have exactSum := add_value left right
  have bound := value_lt (add left right).1
  cases overflow : (add left right).2 <;> simp [overflow] at exactSum ⊢ <;> omega

end FormalProof4FHE.HasteBoots.ConcreteNTTU256Add
