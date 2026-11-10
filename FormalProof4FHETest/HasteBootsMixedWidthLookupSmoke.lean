module
import FormalProof4FHE.HasteBoots.MixedWidthLookupOpeningFamily
import Mathlib.Algebra.Field.ZMod
open FormalProof4FHE.HasteBoots
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
namespace HasteBootsMixedWidthLookupSmoke
noncomputable section
local instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩
abbrev F := ZMod 17
def basis : Module.Basis (Fin 1) F F := Module.Basis.singleton _ _

-- A two-lane source and an original one-lane helper. The helper's nonzero
-- claimed sum cannot be hidden by the source's extra physical lane.
example : MixedWidthLookupOpeningFamily.WrongOpenings basis
    (padding := 1) (helperPadding := 0) (c := 1) (row := 0) (columns := 1) rfl
    (fun _ _ _ => 0) (fun _ _ => 0)
    ⟨ScalarSumcheckQuery.query 1 (fun _ => 0),fun _ => 1⟩
    ⟨ScalarSumcheckQuery.query 1 (fun _ => 0),fun _ => 0⟩ (fun _ _ => 0) 0 := by
  left
  have zeroFold : (ExtensionQuery.coefficientsQuery (padding := 0) basis
      (ScalarSumcheckQuery.point (ScalarSumcheckQuery.query 1 (fun _ : Fin 1 => (0 : F))))).query.fold
      (fun _ _ => 0) = 0 := by
    simp [ExtensionQuery.coefficientsQuery,ExtensionQuery.coefficients,Query.fold,
      MatrixFold.foldFirst]
    change Matrix.mulVec _ (0 : Fin 1 → F) + Matrix.mulVec _ 0 = 0
    rw [Matrix.mulVec_zero,Matrix.mulVec_zero,add_zero]
  rw [zeroFold]
  intro equal
  have impossible := congrArg (PaddedExtension.decode basis) equal
  simp only [PaddedExtension.decode_encode,map_zero] at impossible
  exact one_ne_zero impossible
end
end HasteBootsMixedWidthLookupSmoke
