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

namespace FormalProof4FHETest.HasteBootsConcreteNTTTwiddleSmoke
open FormalProof4FHE.HasteBoots
open ConcreteNTTLimbArithmetic (radix Limb)
private def limb (n : Nat) : Limb := Fin.ofNat radix n
private def contents (data : Array Limb) : List Nat := data.toList.map Fin.val
private def expected (p root bits : Nat) (arrays : Array Limb × Array Limb) : Bool :=
  let n := 2^bits
  decide (arrays.1.size = n ∧ arrays.2.size = n) && (List.range n).all fun i =>
    let exponent := ConcreteNTTBitReverse.narrow bits i
    let opposite := (n-exponent)%n
    decide (arrays.1[i]!.val = ConcreteNTTModularPower.power p root exponent) &&
    decide (arrays.2[i]!.val = if opposite = 0 then 1 else p-ConcreteNTTModularPower.power p root opposite)

-- Literal source-word indices, including the most significant selected bit.
/-- info: true -/
#guard_msgs in
#eval decide ((List.range 8).map (ConcreteNTTBitReverse.word 3) = [0,4,2,6,1,5,3,7]) &&
  decide (ConcreteNTTBitReverse.word 10 1 = 512) &&
  decide (ConcreteNTTBitReverse.word 10 1023 = 1023)

-- Exhaustive bounds and involution on every native-sized index up to 10 bits.
/-- info: true -/
#guard_msgs in
#eval (List.range 10).all fun extra =>
  let bits := extra+1
  (List.range (2^bits)).all fun i =>
    decide (ConcreteNTTBitReverse.word bits i < 2^bits) &&
    decide (ConcreteNTTBitReverse.word bits (ConcreteNTTBitReverse.word bits i) = i)

-- Boundary words use the same low-bit reversal, without relying on narrow casts.
/-- info: true -/
#guard_msgs in
#eval [1,4,10,32,63,64].all fun bits =>
  [0,1,2^bits-1,2^bits,18446744073709551615].all fun i =>
    decide (ConcreteNTTBitReverse.word bits i = ConcreteNTTBitReverse.narrow bits i)

-- The original inverse-index map handles zero separately and is a permutation.
/-- info: true -/
#guard_msgs in
#eval [16,32,1024].all fun n => (List.range n).all fun i =>
  decide (ConcreteNTTTwiddleIndices.opposite n (ConcreteNTTTwiddleIndices.opposite n i) = i)

-- Complete small-field forward/inverse arrays retain the original zero branch.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTDiv64Initialization.new 17 with
  | .assertionFailure => false
  | .initialized state =>
    match ConcreteNTTTwiddleArray.build state 3 3 with
    | none => false
    | some arrays =>
      decide (contents arrays.1 = [1,13,9,15,3,5,10,11]) &&
      decide (contents arrays.2 = [1,4,2,8,6,7,12,14]) && expected 17 3 3 arrays

-- Bounds failures and an empty loop are distinct; neither silently drops a write.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTDiv64Initialization.new 17 with
  | .assertionFailure => false
  | .initialized state =>
      decide (ConcreteNTTTwiddleArray.fill state 3 3 1 0 1 #[] (Array.replicate 8 0) = none) &&
      decide (ConcreteNTTTwiddleArray.fill state 3 3 1 0 1 (Array.replicate 8 0) #[] = none) &&
      decide (ConcreteNTTTwiddleArray.fill state 3 3 0 99 1 #[] #[] = some (#[],#[]))

-- Raw subtraction at an invalid zero root is retained; no canonicalization gate.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTDiv64Initialization.new 17 with
  | .assertionFailure => false
  | .initialized state =>
    match ConcreteNTTTwiddleArray.build state 0 1 with
    | none => false
    | some arrays => decide (contents arrays.1 = [1,0] ∧ contents arrays.2 = [1,17])

-- Twiddle initializer unwrap failure remains assertion failure, not rejection.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTConstructedTwiddles.build 0 3 = ConcreteNTTConstructedTwiddles.Outcome.assertionFailure) &&
  decide (ConcreteNTTConstructedTwiddles.build 1 3 = ConcreteNTTConstructedTwiddles.Outcome.assertionFailure) &&
  decide (ConcreteNTTConstructedTwiddles.build 17 5 = ConcreteNTTConstructedTwiddles.Outcome.assertionFailure)

-- The separately constructed root/state match the actual earlier prefix.
/-- info: true -/
#guard_msgs in
#eval [5,10].all fun bits =>
  match ConcreteNTTPlanRootPowers.goldilocks bits,
      ConcreteNTTConstructedTwiddles.build ConcreteNTTPlanRootPowers.goldilocksDivisor bits with
  | .prepared prior, .initializedTables tables =>
      decide (tables.root = prior.root ∧ tables.state = prior.state) &&
      expected NativeFields.goldilocksModulus prior.root.val bits (tables.forward,tables.inverse)
  | _,_ => false

-- The composed constructor stage preserves every root-power and twiddle entry.
/-- info: true -/
#guard_msgs in
#eval [5,10].all fun bits =>
  match ConcreteNTTConstructedTwiddles.goldilocks bits with
  | .prepared stage =>
      expected NativeFields.goldilocksModulus stage.rootPowers.root.val bits (stage.forward,stage.inverse) &&
      (List.range (2*2^bits)).all (fun i => decide (stage.rootPowers.powers[i]!.val =
        ConcreteNTTModularPower.power NativeFields.goldilocksModulus stage.rootPowers.root.val i))
  | _ => false

end FormalProof4FHETest.HasteBootsConcreteNTTTwiddleSmoke
