module
import all FormalProof4FHE.HasteBoots.ReciprocalRemainder
import all FormalProof4FHE.HasteBoots.ConcreteNTTLimbArithmetic
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul64
import all FormalProof4FHE.HasteBoots.ConcreteNTTLimbAdd
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Add
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul128
import all FormalProof4FHE.HasteBoots.ConcreteNTTDiv64
namespace FormalProof4FHETest.HasteBootsConcreteNTTLimbSmoke
open FormalProof4FHE.HasteBoots
open ConcreteNTTLimbArithmetic (radix Limb mulCarry)
open ConcreteNTTU256Mul64 (Word value multiply)
private def limb (n : Nat) : Limb := Fin.ofNat radix n
private def word (a b c d : Nat) : Word := ⟨limb a,limb b,limb c,limb d⟩
private def max : Nat := radix-1
private def inputs : List Word :=
  [word 0 0 0 0,word max max max max,word 1 0 0 0,word 0 0 0 1,
   word max 0 max 0,word 0 max 0 max,word (max-1) max 1 max]
private def rights : List Limb := [limb 0,limb 1,limb 2,limb (2^32+1),limb max]
private def limbs : List Limb := [limb 0,limb 1,limb (radix/2),limb (radix-2),limb max]

-- 125 limb multiply/carry cases, compared to independent full-width arithmetic.
/-- info: true -/
#guard_msgs in
#eval limbs.all (fun left => limbs.all (fun right => limbs.all (fun carry =>
  let result := mulCarry left right carry
  let full := left.val*right.val+carry.val
  decide (full < 2^128 ∧ result.1.val = full%radix ∧ result.2.val = full/radix))))

-- Largest u64-by-u64 plus carry is still a fitting u128 intermediate.
/-- info: true -/
#guard_msgs in
#eval let result := mulCarry (limb max) (limb max) (limb max)
  decide (result.1.val = 0 ∧ result.2.val = max)

-- Same 35 u256 products checked against fresh native output by Python integers.
/-- info: true -/
#guard_msgs in
#eval inputs.all (fun input => rights.all (fun right =>
  let result := multiply input right
  let full := value input*right.val
  decide (value result.1 = full%2^256 ∧ result.2.val = full/2^256)))

-- Exact recomposition of all 320 bits and the later high-carry increment bound.
/-- info: true -/
#guard_msgs in
#eval inputs.all (fun input => rights.all (fun right =>
  let result := multiply input right
  decide (value result.1+2^256*result.2.val = value input*right.val ∧ result.2.val+1 < radix)))

-- All-ones multiplication propagates carries through every original limb.
/-- info: true -/
#guard_msgs in
#eval let result := multiply (word max max max max) (limb max)
  decide (result.1 = word 1 max max max ∧ result.2.val = radix-2)

-- Zero and one keep all four limb positions and the final carry exact.
/-- info: true -/
#guard_msgs in
#eval inputs.all (fun input =>
  decide ((multiply input (limb 1)).1 = input ∧ (multiply input (limb 1)).2.val = 0 ∧
    value (multiply input (limb 0)).1 = 0 ∧ (multiply input (limb 0)).2.val = 0))
-- Both overflow flags and Boolean carry agree with full-width addition.
/-- info: true -/
#guard_msgs in
#eval limbs.all (fun left => limbs.all (fun right => [false,true].all (fun carry =>
  let result := ConcreteNTTLimbAdd.adc left right carry
  let full := left.val+right.val+(if carry then 1 else 0)
  decide (result.1.val = full%radix ∧ result.2 = decide (radix ≤ full)))))

-- All 49 native addition cases include chains across every limb boundary.
/-- info: true -/
#guard_msgs in
#eval inputs.all (fun left => inputs.all (fun right =>
  let result := ConcreteNTTU256Add.add left right
  decide (value result.1 = (value left+value right)%2^256 ∧
    result.2 = decide (2^256 ≤ value left+value right))))

-- The one-limb shift drops the original high limb exactly.
/-- info: true -/
#guard_msgs in
#eval inputs.all (fun input =>
  decide (value (ConcreteNTTU256Mul128.shift64 input) = value input*radix%2^256))

-- Same 42 native wrapped u256-by-u128 cases, compared to full Nat products.
/-- info: true -/
#guard_msgs in
#eval inputs.all (fun left => [0,1,radix-1,radix,radix+1,2^128-1].all (fun right =>
  let wide : ConcreteNTTU256Mul128.Wide := Fin.ofNat (radix^2) right
  decide (value (ConcreteNTTU256Mul128.wrappingMultiply left wide) = value left*right%2^256)))

-- Full limb remainder composition, using the mathematical initialized reciprocal.
-- The native reciprocal-initialization limb proof is still a separate obligation.
private def fromNat (n : Nat) : Word := word n (n/radix) (n/radix^2) (n/radix^3)
/-- info: true -/
#guard_msgs in
#eval [2,3,17,97,65536,18446744069414584321,radix-1].all (fun divisor =>
  [0,1,radix-1,radix,2^128-1].all (fun input =>
    let reciprocal := fromNat (ConcreteNTTDiv64.reciprocal divisor)
    let wide : ConcreteNTTU256Mul128.Wide := Fin.ofNat (radix^2) input
    decide ((ConcreteNTTU256Mul128.remainder reciprocal (limb divisor) wide).val = input%divisor)))

end FormalProof4FHETest.HasteBootsConcreteNTTLimbSmoke
