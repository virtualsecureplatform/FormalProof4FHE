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

namespace FormalProof4FHETest.HasteBootsConcreteNTTPlanRootPowersSmoke
open FormalProof4FHE.HasteBoots
open ConcreteNTTLimbArithmetic (radix Limb)
private def limb (n : Nat) : Limb := Fin.ofNat radix n
private def contents (data : Array Limb) : List Nat := data.toList.map Fin.val
private def matchesPowers (p n : Nat) (root : Limb) (data : Array Limb) : Bool :=
  decide (contents data = (List.range (2*n)).map (ConcreteNTTModularPower.power p root.val))

-- Size failures are distinguished from a successful empty fill (no write).
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTDiv64Initialization.new 17 with
  | .assertionFailure => false
  | .initialized state =>
      decide (ConcreteNTTRootPowerArray.build state 0 3 = none) &&
      decide (ConcreteNTTRootPowerArray.build state 1 3 = none) &&
      decide (ConcreteNTTRootPowerArray.fill state 3 1 3 1 #[7,8] = none) &&
      decide (ConcreteNTTRootPowerArray.fill state 3 0 99 1 #[7,8] = some #[7,8])

-- Exhaustive small canonical roots exercise every tail length and zero products.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTDiv64Initialization.new 17 with
  | .assertionFailure => false
  | .initialized state => (List.range 17).all fun root => (List.range 9).all fun extra =>
      match ConcreteNTTRootPowerArray.build state (2*(extra+1)) (limb root) with
      | none => false
      | some data => matchesPowers 17 (extra+1) (limb root) data

-- The original direct initial root write is preserved, with no extra validation.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTDiv64Initialization.new 17 with
  | .assertionFailure => false
  | .initialized state =>
      match ConcreteNTTRootPowerArray.build state 4 20 with
      | none => false
      | some data => decide (contents data = [1,20,9,10])

-- Tail writes preserve earlier entries and store the newly multiplied value.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTDiv64Initialization.new 17 with
  | .assertionFailure => false
  | .initialized state =>
      match ConcreteNTTRootPowerArray.fill state 3 2 2 3 #[1,3,0,0] with
      | none => false
      | some data => decide (contents data = [1,3,9,10])

-- All five established native plans have the same complete root-power arrays.
/-- info: true -/
#guard_msgs in
#eval [(97,16,51), (193,16,151), (193,32,94),
       (18446744069414584321,32,549755813888),
       (18446744069414584321,1024,455906449640507599)].all fun (p,n,root) =>
  match ConcreteNTTDiv64Initialization.new (limb p) with
  | .assertionFailure => false
  | .initialized state =>
    match ConcreteNTTRootPowerArray.build state (2*n) (limb root) with
    | none => false
    | some data => matchesPowers p n (limb root) data

-- The original minimum-size gate rejects before root construction.
/-- info: true -/
#guard_msgs in
#eval (List.range 4).all fun logSize =>
  decide (ConcreteNTTPlanRootPowers.goldilocks logSize = ConcreteNTTPlanRootPowers.Outcome.rejected)

-- Complete constructor prefixes retain the actual original initialized state.
/-- info: true -/
#guard_msgs in
#eval [(5,549755813888), (10,455906449640507599)].all fun (logSize,root) =>
  match ConcreteNTTPlanRootPowers.goldilocks logSize with
  | .prepared table =>
      decide (table.root.val = root) &&
      decide (ConcreteNTTDiv64Initialization.new ConcreteNTTPlanRootPowers.goldilocksDivisor =
        ConcreteNTTDiv64Initialization.Outcome.initialized table.state) &&
      matchesPowers NativeFields.goldilocksModulus (2^logSize) table.root table.powers
  | _ => false

-- The 1024-degree array retains its final entry and negacyclic half-period.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTPlanRootPowers.goldilocks 10 with
  | .prepared table =>
      decide (table.powers.size = 2048) &&
      (List.range 1024).all (fun i =>
        decide (table.powers[i+1024]!.val = NativeFields.goldilocksModulus-table.powers[i]!.val))
  | _ => false

end FormalProof4FHETest.HasteBootsConcreteNTTPlanRootPowersSmoke
