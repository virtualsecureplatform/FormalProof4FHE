module

import all FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks
import all FormalProof4FHE.HasteBoots.NativeGoldPcsDraws
import all FormalProof4FHE.HasteBoots.NativeIndexRequest
import all Mathlib.Data.List.Sort

/-! Original ordered atomic blocks from full successful native schedule-5
PCS verifications. For quota 33 over 32 positions, only 18 distinct columns
are transmitted; the original analysis vector must still contain 33 draws. -/
open FormalProof4FHE.HasteBoots
namespace NativeGoldPcsDrawsSmoke
private noncomputable def bytes (values : List ℕ) : InputIndexedOracle.Input :=
  values.map (fun n => ⟨n%256,Nat.mod_lt _ (by decide)⟩)
private noncomputable def raw8 := bytes [255, 35, 98, 236, 156, 95, 183, 234, 86, 215, 207, 220, 241, 194, 191, 166, 179, 66, 120, 32, 65, 162, 234, 196, 117, 158, 29, 76, 250, 15, 114, 122, 64, 180, 75, 243, 136, 52, 128, 33, 120, 36, 233, 121, 89, 53, 93, 223, 156, 244, 48, 42, 105, 181, 254, 131, 143, 172, 61, 243, 212, 41, 79, 115]
private def ordered8 : List ℕ := [31, 22, 19, 21, 0, 24, 28, 15]
private def indices8 : List ℕ := [0, 15, 19, 21, 22, 24, 28, 31]
example : NativeIndexRequest.ordered 32 8 raw8 = ordered8 := by decide +kernel
example : NativeIndexRequest.distinct ordered8 = indices8 := by decide +kernel
example : (NativeGoldPcsDraws.typed 5 8 (NativeIndexRequest.ordered 32 8 raw8)).map
  (fun draw => (List.ofFn draw).map Fin.val) = some ordered8 := by decide +kernel
private noncomputable def raw33 := bytes [154, 196, 70, 74, 16, 189, 245, 73, 17, 128, 79, 38, 112, 0, 170, 77, 239, 130, 244, 180, 180, 248, 155, 25, 47, 209, 115, 239, 214, 207, 37, 139, 136, 38, 115, 131, 240, 198, 255, 26, 97, 4, 52, 222, 27, 133, 182, 212, 57, 117, 177, 125, 153, 144, 204, 202, 158, 70, 166, 16, 220, 39, 174, 66, 53, 225, 255, 76, 14, 120, 141, 181, 200, 106, 208, 3, 96, 56, 192, 133, 99, 3, 191, 60, 116, 20, 120, 26, 126, 247, 153, 130, 94, 218, 93, 131, 102, 43, 140, 167, 175, 206, 131, 152, 89, 62, 125, 47, 245, 202, 252, 109, 228, 78, 175, 13, 128, 193, 117, 76, 143, 162, 77, 211, 207, 109, 199, 42, 101, 185, 235, 6, 22, 174, 60, 146, 152, 205, 185, 17, 240, 8, 183, 22, 10, 58, 40, 44, 13, 165, 46, 5, 118, 98, 58, 120, 231, 239, 140, 97, 150, 33, 82, 60, 218, 45, 126, 37, 249, 251, 3, 103, 249, 70, 46, 106, 131, 229, 89, 246, 225, 108, 69, 242, 225, 124, 116, 229, 25, 66, 217, 114, 150, 212, 171, 208, 215, 115, 149, 185, 97, 222, 228, 38, 185, 225, 94, 139, 77, 24, 244, 151, 187, 71, 60, 175, 249, 197, 24, 185, 114, 38, 154, 12, 59, 41, 199, 195, 180, 147, 219, 172, 51, 70, 41, 102, 161, 98, 107, 236, 205, 117, 7, 141, 134, 113, 103, 53, 33, 151, 160, 141, 191, 244, 212, 71, 202, 109, 31, 234, 161, 197, 140, 74]
private def ordered33 : List ℕ := [26, 17, 15, 15, 8, 1, 25, 30, 21, 8, 3, 30, 6, 25, 4, 15, 5, 24, 10, 22, 22, 25, 3, 1, 22, 1, 13, 25, 27, 19, 13, 1, 10]
private def indices33 : List ℕ := [1, 3, 4, 5, 6, 8, 10, 13, 15, 17, 19, 21, 22, 24, 25, 26, 27, 30]
example : NativeIndexRequest.ordered 32 33 raw33 = ordered33 := by decide +kernel
example : NativeIndexRequest.distinct ordered33 = indices33 := by decide +kernel
example : (NativeGoldPcsDraws.typed 5 33 (NativeIndexRequest.ordered 32 33 raw33)).map
  (fun draw => (List.ofFn draw).map Fin.val) = some ordered33 := by decide +kernel
example : (ordered33.length,indices33.length) = (33,18) := by decide +kernel
example : (NativeGoldPcsDraws.typed 5 18 ordered33).isNone = true := by decide +kernel
example : (NativeGoldPcsDraws.typed 5 3 [27,3,27]).map (fun draw => (List.ofFn draw).map Fin.val) = some [27,3,27] := by decide +kernel
example : (NativeGoldPcsDraws.typed 5 1 [32]).isNone = true := by decide +kernel
example : (NativeGoldPcsDraws.typed 5 2 [1]).isNone = true := by decide +kernel
example : (NativeGoldPcsDraws.typed 5 0 []).map (fun draw => (List.ofFn draw).map Fin.val) = some [] := by decide +kernel
end NativeGoldPcsDrawsSmoke

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsDraws.typed_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsDraws.typed_values

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsDraws.typed_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsDraws.typed_complete

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsDraws.prepared_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsDraws.prepared_sample

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsDraws.prepared_typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsDraws.prepared_typed

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsAgrees.pool_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsAgrees.pool_position

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsAgrees.agrees_of_equations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsAgrees.agrees_of_equations

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsAgrees.pool_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsAgrees.pool_agrees

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks.prepared_parameters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks.prepared_parameters

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks.original_draws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks.original_draws

/-- info: 'FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks.prepared_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks.prepared_agrees
