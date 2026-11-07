module
import all FormalProof4FHE.HasteBoots.NTTDomainCost
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 17) := ⟨by decide⟩
private def values (n : Nat) (psi : ZMod 17) : List Nat :=
  (NTTDomainCost.nodes n psi).value.toList.map ZMod.val

/-- info: [3] -/
#guard_msgs in
#eval values 0 3

/-- info: [3, 10] -/
#guard_msgs in
#eval values 1 3

/-- info: [3, 5, 10, 11] -/
#guard_msgs in
#eval values 2 3

/-- info: [3, 14, 5, 12, 10, 7, 11, 6] -/
#guard_msgs in
#eval values 3 3

/-- info: [0, 0, 0, 0] -/
#guard_msgs in
#eval values 2 0

/-- info: [1, 1, 1, 1] -/
#guard_msgs in
#eval values 2 1

/-- info: 4 -/
#guard_msgs in
#eval (NTTDomainCost.nodes 0 (3 : ZMod 17)).cost

/-- info: 17 -/
#guard_msgs in
#eval (NTTDomainCost.nodes 1 (3 : ZMod 17)).cost

/-- info: 47 -/
#guard_msgs in
#eval (NTTDomainCost.nodes 2 (3 : ZMod 17)).cost

/-- info: 115 -/
#guard_msgs in
#eval (NTTDomainCost.nodes 3 (3 : ZMod 17)).cost
