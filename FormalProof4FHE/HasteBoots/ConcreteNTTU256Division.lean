module
public import FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul64
@[expose] public section

/-! Natural-word semantics of concrete-ntt u256::div_rem_u256_u64 at locked
cdeba793e46208320b30d78be19f7be78d49016a. All four high-to-low division steps
are retained. u128 intermediate and u64 quotient/remainder casts are bounded;
actual machine division, bit assembly, compiler and physical refinement remain
separate obligations. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTU256Division
open ConcreteNTTLimbArithmetic (radix Limb radix_pos)
open ConcreteNTTU256Mul64 (Word value)

theorem digit_lt (divisor : Limb) (prior : Fin divisor.val) (digit : Limb) :
    digit.val+radix*prior.val < radix*divisor.val := by
  have d := digit.isLt
  have r := prior.isLt
  nlinarith

theorem digit_fits (divisor : Limb) (prior : Fin divisor.val) (digit : Limb) :
    digit.val+radix*prior.val < radix^2 := by
  have bound := digit_lt divisor prior digit
  have divisorBound := Nat.mul_lt_mul_of_pos_left divisor.isLt radix_pos
  simpa only [pow_two] using bound.trans divisorBound

def step (divisor : Limb) (prior : Fin divisor.val) (digit : Limb) : Limb × Fin divisor.val :=
  let double := digit.val+radix*prior.val
  let positive : 0 < divisor.val := by have bound := prior.isLt; omega
  (⟨double/divisor.val,(Nat.div_lt_iff_lt_mul positive).mpr (digit_lt divisor prior digit)⟩,
   ⟨double%divisor.val,Nat.mod_lt _ positive⟩)

theorem step_value (divisor : Limb) (prior : Fin divisor.val) (digit : Limb) :
    (step divisor prior digit).1.val*divisor.val+(step divisor prior digit).2.val = digit.val+radix*prior.val := by
  change (digit.val+radix*prior.val)/divisor.val*divisor.val+(digit.val+radix*prior.val)%divisor.val = _
  calc
    _ = (digit.val+radix*prior.val)%divisor.val+divisor.val*((digit.val+radix*prior.val)/divisor.val) := by ring
    _ = _ := Nat.mod_add_div _ _

def divide (word : Word) (divisor : Limb) (positive : 0 < divisor.val) : Word × Fin divisor.val :=
  let a := step divisor ⟨0,positive⟩ word.x3
  let b := step divisor a.2 word.x2
  let c := step divisor b.2 word.x1
  let d := step divisor c.2 word.x0
  (⟨d.1,c.1,b.1,a.1⟩,d.2)

theorem divide_value (word : Word) (divisor : Limb) (positive : 0 < divisor.val) :
    value (divide word divisor positive).1*divisor.val+(divide word divisor positive).2.val = value word := by
  let a := step divisor ⟨0,positive⟩ word.x3
  let b := step divisor a.2 word.x2
  let c := step divisor b.2 word.x1
  let d := step divisor c.2 word.x0
  have h3 := congrArg (fun n => radix^3*n) (step_value divisor ⟨0,positive⟩ word.x3)
  have h2 := congrArg (fun n => radix^2*n) (step_value divisor a.2 word.x2)
  have h1 := congrArg (fun n => radix*n) (step_value divisor b.2 word.x1)
  have h0 := step_value divisor c.2 word.x0
  change value (⟨d.1,c.1,b.1,a.1⟩ : Word)*divisor.val+d.2.val = value word
  dsimp only [value]
  change radix^3*(a.1.val*divisor.val+a.2.val) = radix^3*(word.x3.val+radix*0) at h3
  change radix^2*(b.1.val*divisor.val+b.2.val) = radix^2*(word.x2.val+radix*a.2.val) at h2
  change radix*(c.1.val*divisor.val+c.2.val) = radix*(word.x1.val+radix*b.2.val) at h1
  change d.1.val*divisor.val+d.2.val = word.x0.val+radix*c.2.val at h0
  nlinarith only [h0,h1,h2,h3]

theorem divide_quotient (word : Word) (divisor : Limb) (positive : 0 < divisor.val) :
    value (divide word divisor positive).1 = value word/divisor.val := by
  rw [← divide_value word divisor positive,Nat.mul_comm (value (divide word divisor positive).1) divisor.val,Nat.mul_add_div positive,
    Nat.div_eq_of_lt (divide word divisor positive).2.isLt,Nat.add_zero]

theorem divide_remainder (word : Word) (divisor : Limb) (positive : 0 < divisor.val) :
    (divide word divisor positive).2.val = value word%divisor.val := by
  have equation : value word = (divide word divisor positive).2.val+divisor.val*value (divide word divisor positive).1 := by
    have exactValue := divide_value word divisor positive
    nlinarith only [exactValue]
  rw [equation,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (divide word divisor positive).2.isLt]

end FormalProof4FHE.HasteBoots.ConcreteNTTU256Division
