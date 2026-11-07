module
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordSearch
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordSquareRoot
import all FormalProof4FHE.HasteBoots.ConcreteNTTWordRootConstruction
import all FormalProof4FHE.HasteBoots.ConcreteNTTSquareRoot
import all FormalProof4FHE.HasteBoots.ConcreteNTTRootConstruction
import all FormalProof4FHE.HasteBoots.ConcreteNTTModularPower
import all FormalProof4FHE.HasteBoots.ConcreteNTTDiv64
import all FormalProof4FHE.HasteBoots.ReciprocalRemainder
import all FormalProof4FHE.HasteBoots.NativeFields
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
import all Mathlib.Data.ZMod.Defs
import all Mathlib.Algebra.Group.Fin.Basic
namespace FormalProof4FHETest.HasteBootsConcreteNTTWordRootSmoke
open FormalProof4FHE.HasteBoots
open ConcreteNTTWordSquareRoot (Outcome)
private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

-- Exact inner indices and final values agree over the complete small field.
/-- info: true -/
#guard_msgs in
#eval (List.range 6).all (fun limit => (List.range 17).all (fun t =>
  let word := ConcreteNTTWordSearch.search 17 limit t
  let field := ConcreteNTTSquareRoot.search limit (t : ZMod 17)
  decide (word.1 = field.1 ∧ word.2 = field.2.val ∧ word.1 ≤ limit ∧ word.2 < 17)))

-- Distinct zero/one early returns and ordinary no-root rejection.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTWordSquareRoot.sqrt 17 1 4 3 0 = .root 0) &&
  decide (ConcreteNTTWordSquareRoot.sqrt 17 1 4 3 1 = .root 1) &&
  decide (ConcreteNTTWordSquareRoot.sqrt 17 1 4 3 3 = .noRoot)

-- Native failed assertion is retained, distinct from an exhausted root search.
-- Early exits precede that assertion even with m=0.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTWordSquareRoot.loop 17 0 3 2 1 = .assertionFailure) &&
  decide (ConcreteNTTWordSquareRoot.loop 17 1 3 16 1 = .noRoot) &&
  decide (ConcreteNTTWordSquareRoot.loop 17 0 3 0 7 = .root 0) &&
  decide (ConcreteNTTWordSquareRoot.loop 17 0 3 1 7 = .root 7)

-- Both accepted values and rejections match the field loop, with canonical roots.
/-- info: true -/
#guard_msgs in
#eval (List.range 17).all (fun n =>
  let result := ConcreteNTTWordSquareRoot.sqrt 17 1 4 3 n
  decide (result.erase = (ConcreteNTTSquareRoot.sqrt 1 4 (3 : ZMod 17) (n : ZMod 17)).map ZMod.val) &&
  match result with
  | .root answer => decide (answer < 17 ∧ answer*answer%17 = n)
  | .noRoot => true
  | .assertionFailure => false)

-- Original factorization provides fitting initialization and shift parameters.
/-- info: true -/
#guard_msgs in
#eval [3,17,97,193,2013265921,18446744069414584321,2^64-1].all (fun modulus =>
  let parts := ConcreteNTTRootConstruction.factorTwos (modulus-1)
  decide (parts.1+1 < 2^64 ∧ parts.2 < 64))

-- Each supported order returns the original root; unsupported order fails closed.
/-- info: true -/
#guard_msgs in
#eval (List.range 4).all (fun log =>
  let result := ConcreteNTTWordRootConstruction.construct 17 log
  decide (result.erase = (ConcreteNTTRootConstruction.construct 17 log : Option (ZMod 17)).map ZMod.val)) &&
  decide (ConcreteNTTWordRootConstruction.construct 17 4 = .noRoot)

-- Exact roots also checked directly by the locked native Plan fixture.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTWordRootConstruction.construct 97 4 = .root 51) &&
  decide (ConcreteNTTWordRootConstruction.construct 193 4 = .root 151) &&
  decide (ConcreteNTTWordRootConstruction.construct 193 5 = .root 94) &&
  decide (ConcreteNTTWordRootConstruction.goldilocks 5 = .root 549755813888) &&
  decide (ConcreteNTTWordRootConstruction.goldilocks 10 = .root 455906449640507599)

-- Unreduced u64 inputs are canonicalized by literal modular operations.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTWordSquareRoot.sqrt 17 1 4 3 (2^64-1) = .root 0) &&
  decide ((ConcreteNTTWordSquareRoot.sqrt 17 1 4 3 21).erase.map (fun n => n*n%17) = some 4)
end FormalProof4FHETest.HasteBootsConcreteNTTWordRootSmoke
