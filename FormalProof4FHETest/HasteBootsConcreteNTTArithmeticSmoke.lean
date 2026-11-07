module
import all FormalProof4FHE.HasteBoots.ReciprocalRemainder
import all FormalProof4FHE.HasteBoots.ConcreteNTTDiv64
import all FormalProof4FHE.HasteBoots.ConcreteNTTModularPower
import all Mathlib.Data.ZMod.Basic
import all Mathlib.Data.ZMod.Defs
import all Mathlib.Algebra.Group.Fin.Basic
namespace FormalProof4FHETest.HasteBootsConcreteNTTArithmeticSmoke
open FormalProof4FHE.HasteBoots
private def divisors : List Nat := [2,3,17,97,65536,18446744069414584321,2^64-1]
private def wideInputs : List Nat := [0,1,2^64-1,2^64,2^128-1]
private def words : List Nat := [0,1,2,18446744069414584320,2^64-1]
private def exponents : List Nat := [0,1,2,63,64,2^64-1]

-- The reciprocal is rounded up exactly once, with no overflow for valid divisors.
/-- info: true -/
#guard_msgs in
#eval divisors.all (fun d =>
  let reciprocal := ConcreteNTTDiv64.reciprocal d
  decide (reciprocal < 2^256 ∧ 2^256 ≤ reciprocal*d ∧ reciprocal*d < 2^256+d))

-- All small inputs, including the zero-error power-of-two divisors.
/-- info: true -/
#guard_msgs in
#eval (List.range 31).all (fun offset =>
  let divisor := offset+2
  (List.range 128).all (fun input => decide (ConcreteNTTDiv64.rem divisor input = input%divisor)))

-- Same 35 wide-word cases probed directly against the locked native reducer.
/-- info: true -/
#guard_msgs in
#eval divisors.all (fun divisor => wideInputs.all (fun input =>
  decide (ConcreteNTTDiv64.rem divisor input = input%divisor)))

-- Full u64 products must retain the high half before reciprocal reduction.
/-- info: true -/
#guard_msgs in
#eval divisors.all (fun divisor => words.all (fun left => words.all (fun right =>
  decide (ConcreteNTTDiv64.mulMod divisor left right = left*right%divisor))))

-- Zero, one, odd/even and full-u64 exponents, including noncanonical bases.
-- ZMod exponentiation is an independent reduced-arithmetic reference.
/-- info: true -/
#guard_msgs in
#eval divisors.all (fun divisor => words.all (fun base => exponents.all (fun exponent =>
  decide (ConcreteNTTModularPower.power divisor base exponent = ((base : ZMod divisor)^exponent).val))))

-- Canonical output is retained across every outer-loop transition.
/-- info: true -/
#guard_msgs in
#eval divisors.all (fun divisor => words.all (fun base => exponents.all (fun exponent =>
  decide (ConcreteNTTModularPower.power divisor base exponent < divisor))))
end FormalProof4FHETest.HasteBootsConcreteNTTArithmeticSmoke
