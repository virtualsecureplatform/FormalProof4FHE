module
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Division
import all FormalProof4FHE.HasteBoots.ConcreteNTTDiv64Initialization
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedPower
import all FormalProof4FHE.HasteBoots.ConcreteNTTModularPower
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul128
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Add
import all FormalProof4FHE.HasteBoots.ConcreteNTTLimbAdd
import all FormalProof4FHE.HasteBoots.ConcreteNTTU256Mul64
import all FormalProof4FHE.HasteBoots.ConcreteNTTLimbArithmetic
import all FormalProof4FHE.HasteBoots.ConcreteNTTDiv64
import all FormalProof4FHE.HasteBoots.ReciprocalRemainder
import all Mathlib.Data.ZMod.Basic
import all Mathlib.Data.ZMod.Defs
import all Mathlib.Algebra.Group.Fin.Basic
namespace FormalProof4FHETest.HasteBootsConcreteNTTInitializationSmoke
open FormalProof4FHE.HasteBoots
open ConcreteNTTLimbArithmetic (radix Limb)
open ConcreteNTTU256Mul64 (Word value)
private def limb (n : Nat) : Limb := Fin.ofNat radix n
private def word (a b c d : Nat) : Word := ⟨limb a,limb b,limb c,limb d⟩
private def max : Nat := radix-1
private def inputs : List Word :=
  [word 0 0 0 0,word max max max max,word 1 0 0 0,word 0 0 0 1,
   word max 0 max 0,word 0 max 0 max,word (max-1) max 1 max]
private def divisors : List Limb := [2,3,17,97,65536,limb 18446744069414584321,limb max]
private def words : List Limb := [0,1,2,limb 18446744069414584320,limb max]
private def exponents : List Limb := [0,1,2,63,64,limb max]

-- Complete prior remainder range for 31 small divisors and five boundary digits.
/-- info: true -/
#guard_msgs in
#eval (List.range 31).all (fun offset =>
  let divisor := limb (offset+2)
  (List.finRange divisor.val).all (fun prior => [limb 0,limb 1,limb (radix/2),limb (radix-2),limb max].all (fun digit =>
    let result := ConcreteNTTU256Division.step divisor prior digit
    let double := digit.val+radix*prior.val
    decide (double < 2^128 ∧ result.1.val = double/divisor.val ∧ result.2.val = double%divisor.val))))

-- Same 49 full u256 division cases independently checked against fresh native output.
/-- info: true -/
#guard_msgs in
#eval inputs.all (fun input => divisors.all (fun divisor =>
  if positive : 0 < divisor.val then
    let result := ConcreteNTTU256Division.divide input divisor positive
    decide (value result.1 = value input/divisor.val ∧ result.2.val = value input%divisor.val)
  else false))

-- Full recomposition verifies original high-to-low order and every retained limb.
/-- info: true -/
#guard_msgs in
#eval inputs.all (fun input => divisors.all (fun divisor =>
  if positive : 0 < divisor.val then
    let result := ConcreteNTTU256Division.divide input divisor positive
    decide (value result.1*divisor.val+result.2.val = value input ∧ result.2.val < divisor.val)
  else false))

-- Constructor produces both retained reciprocals and the original divisor.
/-- info: true -/
#guard_msgs in
#eval divisors.all (fun divisor => match ConcreteNTTDiv64Initialization.new divisor with
  | .assertionFailure => false
  | .initialized state => decide (state.divisor = divisor ∧
      value state.doubleReciprocal = ConcreteNTTDiv64.reciprocal divisor.val ∧
      state.singleReciprocal.val = (2^128-1)/divisor.val+1))

-- Actual native assert condition excludes zero and one before division.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTDiv64Initialization.new 0 = .assertionFailure) &&
  decide (ConcreteNTTDiv64Initialization.new 1 = .assertionFailure)

-- Complete initialized limb remainder needs no supplied reciprocal certificate.
/-- info: true -/
#guard_msgs in
#eval divisors.all (fun divisor => match ConcreteNTTDiv64Initialization.new divisor with
  | .assertionFailure => false
  | .initialized state => [0,1,radix-1,radix,2^128-1].all (fun input =>
      let wide : ConcreteNTTU256Mul128.Wide := Fin.ofNat (radix^2) input
      decide ((ConcreteNTTDiv64Initialization.remainder state wide).val = input%divisor.val)))

-- All 175 native modular-product cases use the retained initialized state.
/-- info: true -/
#guard_msgs in
#eval divisors.all (fun divisor => match ConcreteNTTDiv64Initialization.new divisor with
  | .assertionFailure => false
  | .initialized state => words.all (fun left => words.all (fun right =>
      decide ((ConcreteNTTDiv64Initialization.mulMod state left right).val = left.val*right.val%divisor.val))))

-- Same 210 native power cases, including full-u64 exponents and unreduced bases.
/-- info: true -/
#guard_msgs in
#eval divisors.all (fun divisor => match ConcreteNTTDiv64Initialization.new divisor with
  | .assertionFailure => false
  | .initialized state => words.all (fun base => exponents.all (fun exponent =>
      decide ((ConcreteNTTInitializedPower.power state base exponent).val = ((base.val : ZMod divisor.val)^exponent.val).val))))

-- MAX / (2^64-1) has four one limbs, preserving every quotient position.
/-- info: true -/
#guard_msgs in
#eval if positive : 0 < (limb max).val then
  let result := ConcreteNTTU256Division.divide (word max max max max) (limb max) positive
  decide (result.1 = word 1 1 1 1 ∧ result.2.val = 0)
else false

-- Addition of one propagates through three full limbs for divisor two.
/-- info: true -/
#guard_msgs in
#eval (match ConcreteNTTDiv64Initialization.new 2 with
  | .assertionFailure => false
  | .initialized state => decide (state.doubleReciprocal = word 0 0 0 (radix/2) ∧ state.singleReciprocal.val = 2^127)) &&
  (match ConcreteNTTDiv64Initialization.new (limb max) with
  | .assertionFailure => false
  | .initialized state => decide (state.doubleReciprocal = word 2 1 1 1 ∧ state.singleReciprocal.val = radix+2))
end FormalProof4FHETest.HasteBootsConcreteNTTInitializationSmoke
