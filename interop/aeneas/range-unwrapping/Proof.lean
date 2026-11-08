namespace HasteBootsRangeUnwrappingProof
open Aeneas Aeneas.Std Result
open hasteboots_range_unwrapping

theorem capacity_exact (value : Capacity) : capacity value = ok value.val := rfl

theorem small_exact (value : Small) : small value = ok value.val := rfl

theorem direct_exact (value : Capacity) : direct value = ok value.val := rfl

theorem capacity_value (value : Capacity) :
    (do let output ← capacity value; pure output.val) = ok value.val.val := rfl

theorem capacity_bounded (value : Capacity) :
    ∃ output, capacity value = ok output ∧ output.val ≤ 9223372036854775807 :=
  ⟨value.val, rfl, value.property.2⟩

theorem small_bounded (value : Small) :
    ∃ output, small value = ok output ∧ 7 ≤ output.val ∧ output.val ≤ 19 :=
  ⟨value.val, rfl, value.property⟩

end HasteBootsRangeUnwrappingProof
