module
import all FormalProof4FHE.HasteBoots.ConcreteNTTSquareRoot
import all FormalProof4FHE.HasteBoots.ConcreteNTTRootConstruction
import all FormalProof4FHE.HasteBoots.NativeFields
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
import all Mathlib.Data.ZMod.Defs
import all Mathlib.Algebra.Group.Fin.Basic
namespace FormalProof4FHETest.HasteBootsConcreteNTTRootSmoke
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩
private instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
private instance : Fact (Nat.Prime 193) := ⟨by norm_num⟩

-- Native factorization loop, including the public Goldilocks and BabyBear moduli.
/-- info: true -/
#guard_msgs in
#eval [1,2,3,4,12,96,192,NativeFields.goldilocksModulus-1,NativeFields.babyBearModulus-1].all (fun n =>
  let parts := ConcreteNTTRootConstruction.factorTwos n
  decide (parts.1%2 = 1 ∧ n = parts.1*2^parts.2))

-- The inner loop squares before checking, with indices starting at one.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTSquareRoot.search 0 (3 : ZMod 17) = (0,3)) &&
  decide (ConcreteNTTSquareRoot.search 4 (1 : ZMod 17) = (1,1)) &&
  decide (ConcreteNTTSquareRoot.search 4 (16 : ZMod 17) = (1,1)) &&
  decide (ConcreteNTTSquareRoot.search 4 (4 : ZMod 17) = (2,1))

-- Both early returns and nonresidue rejection retain the source behavior.
/-- info: true -/
#guard_msgs in
#eval decide (ConcreteNTTSquareRoot.sqrt 1 4 (3 : ZMod 17) 0 = some 0) &&
  decide (ConcreteNTTSquareRoot.sqrt 1 4 (3 : ZMod 17) 1 = some 1) &&
  (ConcreteNTTSquareRoot.sqrt 1 4 (3 : ZMod 17) 3).isNone

-- Every square input in this complete small field returns a square root.
/-- info: true -/
#guard_msgs in
#eval (List.range 17).all (fun n =>
  let square : ZMod 17 := (n : ZMod 17)*(n : ZMod 17)
  match ConcreteNTTSquareRoot.sqrt 1 4 (3 : ZMod 17) square with
  | none => false
  | some answer => decide (answer*answer = square))

-- Unsupported order rejects rather than borrowing an earlier lower-order root.
/-- info: true -/
#guard_msgs in
#eval (List.range 4).all (fun log =>
  match (ConcreteNTTRootConstruction.construct 17 log : Option (ZMod 17)) with
  | none => false
  | some root => decide (root^(2^log) = -1)) &&
  (ConcreteNTTRootConstruction.construct 17 4 : Option (ZMod 17)).isNone

-- Exact roots independently probed from the locked native Plan::try_new.
/-- info: [some 51] -/
#guard_msgs in
#eval [(ConcreteNTTRootConstruction.construct 97 4 : Option (ZMod 97)).map ZMod.val]
/-- info: [some 151, some 94] -/
#guard_msgs in
#eval [(ConcreteNTTRootConstruction.construct 193 4 : Option (ZMod 193)).map ZMod.val,
       (ConcreteNTTRootConstruction.construct 193 5 : Option (ZMod 193)).map ZMod.val]
/-- info: [some 549755813888, some 455906449640507599] -/
#guard_msgs in
#eval [ConcreteNTTRootConstruction.goldilocks 5 |>.map ZMod.val,
       ConcreteNTTRootConstruction.goldilocks 10 |>.map ZMod.val]
end FormalProof4FHETest.HasteBootsConcreteNTTRootSmoke
