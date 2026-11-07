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

namespace FormalProof4FHETest.HasteBootsConcreteNTTInitializedRootSmoke
open FormalProof4FHE.HasteBoots
open ConcreteNTTLimbArithmetic (radix Limb)
private def limb (value : Nat) : Limb := Fin.ofNat radix value

-- Search reuses the constructed state and preserves every original index/value.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTDiv64Initialization.new 17 with
  | .assertionFailure => false
  | .initialized state => (List.range 6).all (fun limit => (List.range 17).all (fun t =>
      decide (ConcreteNTTInitializedSearch.search state limit t = ConcreteNTTWordSearch.search 17 limit t)))

-- Every small-field square-root outcome agrees, including ordinary no-root returns.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTDiv64Initialization.new 17 with
  | .assertionFailure => false
  | .initialized state => (List.range 17).all (fun n =>
      decide (ConcreteNTTInitializedSquareRoot.sqrt state 1 4 3 n = ConcreteNTTWordSquareRoot.sqrt 17 1 4 3 n))

-- Assertion failure remains distinct, and zero/one exits precede the inner search.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTDiv64Initialization.new 17 with
  | .assertionFailure => false
  | .initialized state =>
      decide (ConcreteNTTInitializedSquareRoot.loop state 0 3 2 1 = ConcreteNTTWordSquareRoot.Outcome.assertionFailure) &&
      decide (ConcreteNTTInitializedSquareRoot.loop state 1 3 16 1 = ConcreteNTTWordSquareRoot.Outcome.noRoot) &&
      decide (ConcreteNTTInitializedSquareRoot.loop state 0 3 0 7 = ConcreteNTTWordSquareRoot.Outcome.root 0) &&
      decide (ConcreteNTTInitializedSquareRoot.loop state 0 3 1 7 = ConcreteNTTWordSquareRoot.Outcome.root 7)

-- Closed construction rejects zero/one at Div64::new and unsupported root orders.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTInitializedRootConstruction.newRoot 0 3 = ConcreteNTTWordSquareRoot.Outcome.assertionFailure) &&
  decide (ConcreteNTTInitializedRootConstruction.newRoot 1 3 = ConcreteNTTWordSquareRoot.Outcome.assertionFailure) &&
  decide (ConcreteNTTInitializedRootConstruction.newRoot 17 4 = ConcreteNTTWordSquareRoot.Outcome.noRoot)

-- All supported small-field orders match the original complete root constructor.
/-- info: true -/
#guard_msgs in
#eval (List.range 4).all (fun log =>
  let result := ConcreteNTTInitializedRootConstruction.newRoot 17 log
  decide (result = ConcreteNTTWordRootConstruction.construct 17 log) &&
  match result with
  | .root answer => decide (answer < 17 ∧ answer^(2^log)%17 = 16)
  | _ => false)

-- Root literals independently recorded by the pinned native Plan fixture.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTInitializedRootConstruction.newRoot 97 4 = ConcreteNTTWordSquareRoot.Outcome.root 51) &&
  decide (ConcreteNTTInitializedRootConstruction.newRoot 193 4 = ConcreteNTTWordSquareRoot.Outcome.root 151) &&
  decide (ConcreteNTTInitializedRootConstruction.newRoot 193 5 = ConcreteNTTWordSquareRoot.Outcome.root 94)

-- Goldilocks N=32 and N=1024 retain the exact original native roots.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTInitializedRootConstruction.goldilocks 5 = ConcreteNTTWordSquareRoot.Outcome.root 549755813888) &&
  decide (ConcreteNTTInitializedRootConstruction.goldilocks 10 = ConcreteNTTWordSquareRoot.Outcome.root 455906449640507599)

-- Unreduced u64 input words are reduced by the same retained reciprocal state.
/-- info: true -/
#guard_msgs in
#eval match ConcreteNTTDiv64Initialization.new 17 with
  | .assertionFailure => false
  | .initialized state =>
      decide (ConcreteNTTInitializedSquareRoot.sqrt state 1 4 3 (radix-1) = ConcreteNTTWordSquareRoot.Outcome.root 0) &&
      decide ((ConcreteNTTInitializedSquareRoot.sqrt state 1 4 3 21).erase.map (fun n => n*n%17) = some 4)
end FormalProof4FHETest.HasteBootsConcreteNTTInitializedRootSmoke
