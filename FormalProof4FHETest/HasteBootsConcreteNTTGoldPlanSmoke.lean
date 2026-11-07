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
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSearch
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedSquareRoot
import all FormalProof4FHE.HasteBoots.ConcreteNTTInitializedRootConstruction
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordSearch
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordSquareRoot
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordRootConstruction
import all FormalProof4FHE.HasteBoots.ConcreteNTTRootConstruction
import all FormalProof4FHE.HasteBoots.NativeFields

import all FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinField
import all FormalProof4FHE.HasteBoots.ConcreteNTTMillerRabinRound
import all FormalProof4FHE.HasteBoots.ConcreteNTTPrimeGate

import all FormalProof4FHE.HasteBoots.ConcreteNTTRootPowerArray
import all FormalProof4FHE.HasteBoots.ConcreteNTTPlanRootPowers

import all FormalProof4FHE.HasteBoots.ConcreteNTTBitReverse
import all FormalProof4FHE.HasteBoots.ConcreteNTTTwiddleIndices
import all FormalProof4FHE.HasteBoots.ConcreteNTTTwiddleArray
import all FormalProof4FHE.HasteBoots.ConcreteNTTConstructedTwiddles

import all FormalProof4FHE.HasteBoots.ConcreteNTTPlanConstants
import all FormalProof4FHE.HasteBoots.ConcreteNTTGoldPlan
import all FormalProof4FHE.HasteBoots.ConcreteNTTGoldTable

namespace FormalProof4FHETest.HasteBootsConcreteNTTGoldPlanSmoke
open FormalProof4FHE.HasteBoots
open ConcreteNTTLimbArithmetic (radix Limb)
private def limb (n : Nat) : Limb := Fin.ofNat radix n

-- Every canonical small-field input has the literal inverse and quotient value.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTDiv64Initialization.new 17 with
  | .assertionFailure => false
  | .initialized state => (List.range 16).all fun extra =>
      let size := extra+1
      let constants := ConcreteNTTPlanConstants.build state size 64
      decide ((size*constants.nInverse.val)%17 = 1) &&
      decide (constants.nInverse.val < 17) &&
      decide (constants.nInverseShoup.val = constants.nInverse.val*radix/17)

-- Both original casts are inert on canonical inputs at the full word boundary.
/-- info: true -/
#guard_msgs in
#eval [2,17,18446744069414584321,18446744073709551615].all fun p =>
  match ConcreteNTTDiv64Initialization.new (limb p) with
  | .assertionFailure => false
  | .initialized state => [0,1,p-1].all fun value =>
      decide ((ConcreteNTTPlanConstants.wide (value*radix)).val = value*radix) &&
      decide ((ConcreteNTTPlanConstants.shoup state (limb value) 64).val = value*radix/p)

-- Known Goldilocks constants include the exact u128 shifted-division results.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTDiv64Initialization.new ConcreteNTTPlanRootPowers.goldilocksDivisor with
  | .assertionFailure => false
  | .initialized state => [(16,17293822565076172801,17293822569102704640),
      (32,17870283317245378561,17870283321406128128),
      (1024,18428729670909296641,18428729675200069632)].all fun (n,inv,shoup) =>
      let constants := ConcreteNTTPlanConstants.build state n 64
      decide (constants.nInverse.val = inv ∧ constants.nInverseShoup.val = shoup ∧
        constants.bigQ.val = 64 ∧ constants.pBarrett.val = 9223372039002259455) &&
      decide ((ConcreteNTTPlanConstants.bigL state 64).val = 127)

-- Original minimum-size and unsupported-order returns remain ordinary rejection.
/-- info: true -/
#guard_msgs in
#eval ((List.range 4) ++ [32]).all fun bits =>
  decide (ConcreteNTTGoldPlan.goldilocks bits = ConcreteNTTGoldPlan.Outcome.rejected)

-- Complete stored metadata and inverse constants at the native degree.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTGoldPlan.goldilocks 10 with
  | .constructed plan =>
    decide (plan.root.val = 455906449640507599 ∧ plan.modulus.val = NativeFields.goldilocksModulus ∧
      plan.nInverse.val = 18428729670909296641 ∧ plan.nInverseShoup.val = 18428729675200069632 ∧
      plan.bigQ.val = 64 ∧ plan.pBarrett.val = 9223372039002259455 ∧
      plan.rootPowers.size = 2048 ∧ plan.twiddle.size = 1024 ∧ plan.inverseTwiddle.size = 1024 ∧
      plan.rootPowersShoup = #[] ∧ plan.twiddleShoup = #[] ∧ plan.inverseTwiddleShoup = #[])
  | _ => false

-- Every original array and the original first initialized state are retained.
/-- info: true -/
#guard_msgs in
#eval [5,10].all fun bits =>
  match ConcreteNTTGoldPlan.goldilocks bits, ConcreteNTTConstructedTwiddles.goldilocks bits with
  | .constructed plan, .prepared stage =>
      decide (plan.root = stage.rootPowers.root ∧ plan.rootPowers = stage.rootPowers.powers ∧
        plan.twiddle = stage.forward ∧ plan.inverseTwiddle = stage.inverse ∧ plan.divisor = stage.rootPowers.state) &&
      decide (ConcreteNTTDiv64Initialization.new plan.modulus = ConcreteNTTDiv64Initialization.Outcome.initialized plan.divisor)
  | _,_ => false

-- Every retained reverse index has its exact value, bounds and involution.
/-- info: true -/
#guard_msgs in
#eval [5,10].all fun bits =>
  match ConcreteNTTGoldPlan.goldilocks bits with
  | .constructed plan => decide (plan.reverseLsbs.size = 2^bits) &&
      (List.range (2^bits)).all (fun i =>
        decide (plan.reverseLsbs[i]! = ConcreteNTTBitReverse.narrow bits i) &&
        decide (plan.reverseLsbs[i]! < 2^bits) && decide (plan.reverseLsbs[plan.reverseLsbs[i]!]! = i))
  | _ => false

-- Complete root-power and twiddle contents still match independent power evaluation.
/-- info: true -/
#guard_msgs in
#eval [5,10].all fun bits =>
  match ConcreteNTTGoldPlan.goldilocks bits with
  | .constructed plan =>
      let p := NativeFields.goldilocksModulus
      let n := 2^bits
      let power := ConcreteNTTModularPower.power p plan.root.val
      (List.range (2*n)).all (fun i => decide (plan.rootPowers[i]!.val = power i)) &&
      (List.range n).all (fun i =>
        let exponent := ConcreteNTTBitReverse.narrow bits i
        let opposite := (n-exponent)%n
        decide (plan.twiddle[i]!.val = power exponent) &&
        decide (plan.inverseTwiddle[i]!.val = if opposite = 0 then 1 else p-power opposite))
  | _ => false

-- The complete plan's inverse normalizes its native polynomial size to one.
/-- info: true -/
#guard_msgs in
#eval [4,5,10].all fun bits =>
  match ConcreteNTTGoldPlan.goldilocks bits with
  | .constructed plan =>
      decide (((2^bits)*plan.nInverse.val)%NativeFields.goldilocksModulus = 1) &&
      decide (plan.nInverseShoup.val = plan.nInverse.val*radix/NativeFields.goldilocksModulus)
  | _ => false

-- ConcreteTable maps ordinary Plan rejection to the original table error.
/-- info: true -/
#guard_msgs in
#eval ((List.range 4) ++ [32]).all fun bits =>
  decide (ConcreteNTTGoldTable.newTable bits = ConcreteNTTGoldTable.Outcome.tableError)

-- Goldilocks::new copies the exact canonical Plan root and retains the whole Plan.
/-- info: true -/
#guard_msgs in
#eval [5,10].all fun bits =>
  match ConcreteNTTGoldTable.newTable bits, ConcreteNTTGoldPlan.goldilocks bits with
  | .created table, .constructed plan =>
      decide (table.plan = plan ∧ table.root = plan.root ∧ table.root.val < NativeFields.goldilocksModulus)
  | _,_ => false

end FormalProof4FHETest.HasteBootsConcreteNTTGoldPlanSmoke
