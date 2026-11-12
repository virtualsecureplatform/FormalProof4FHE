module
import all FormalProof4FHE.HasteBoots.LookupInitialPairedWork

namespace HasteBootsLookupInitialArithmeticSmoke
open FormalProof4FHE.HasteBoots
open NativeExtensionFields (Goldilocks3)
open scoped BigOperators
noncomputable section

/-- Two active cells, with a truthful helper total of two, still violate the
reciprocal identity at both cells. The midpoint EQ draw cancels the errors. -/
def helpers (cell : MatrixFold.Cube 1) : Goldilocks3 := if cell.1 then 2 else 0

def errors (cell : MatrixFold.Cube 1) : Goldilocks3 :=
  ReciprocalMask.residual 1 0 (helpers cell) true

theorem truthful_total : (∑ cell, helpers cell) = 2 := by
  change (∑ cell : Bool × Unit, if cell.1 then (2 : Goldilocks3) else 0) = 2
  rw [Fintype.sum_prod_type]
  simp

theorem nonzero_residual : ∃ cell, errors cell ≠ 0 := by
  refine ⟨(true,()),?_⟩
  norm_num [errors,helpers,ReciprocalMask.residual]

theorem midpoint_misses :
    (∑ cell, PackedEqualityCube.weight (fun _ : Fin 1 => (1/2 : Goldilocks3)) cell * errors cell) = 0 := by
  rw [← ExtensionQuery.evaluate_eq_sum]
  have base : (2 : NativeFields.Goldilocks) ≠ 0 := by decide +kernel
  have twoNonzero : (2 : Goldilocks3) ≠ 0 := by
    intro equal
    apply base
    apply (algebraMap NativeFields.Goldilocks Goldilocks3).injective
    simpa only [map_ofNat,map_zero] using equal
  norm_num [ExtensionQuery.evaluate,errors,helpers,ReciprocalMask.residual]
  field_simp [twoNonzero]
  ring

theorem endpoint_detects :
    (∑ cell, PackedEqualityCube.weight (fun _ : Fin 1 => (1 : Goldilocks3)) cell * errors cell) ≠ 0 := by
  rw [← ExtensionQuery.evaluate_eq_sum]
  norm_num [ExtensionQuery.evaluate,errors,helpers,ReciprocalMask.residual]

/-- A zero-dimensional nonzero residual has no equality exception. -/
theorem zero_dimension_detects (values : MatrixFold.Cube 0 → Goldilocks3)
    (bad : ∃ cell, values cell ≠ 0) (point : Fin 0 → Goldilocks3) :
    (∑ cell, PackedEqualityCube.weight point cell * values cell) ≠ 0 := by
  obtain ⟨cell,bad⟩ := bad
  rw [← ExtensionQuery.evaluate_eq_sum]
  cases cell
  exact bad

end
end HasteBootsLookupInitialArithmeticSmoke
