namespace HasteBootsUsizeRangeProof
open Aeneas Aeneas.Std Result
open hasteboots_usize_ranges

theorem preserve_exact (value : Stored) : preserve value = ok value := rfl

theorem select_exact (value : Stored) : select value = ok value.window := rfl

theorem identity_exact
    (value : { x : Usize // 0 ≤ x.val ∧ x.val ≤ 9223372036854775807 }) :
    identity value = ok value := rfl

theorem capacity_bounds (value : Stored) :
    0 ≤ value.capacity.val.val ∧ value.capacity.val.val ≤ 9223372036854775807 :=
  value.capacity.property

theorem window_bounds (value : Stored) :
    7 ≤ value.window.val.val ∧ value.window.val.val ≤ 19 := value.window.property

theorem select_sound (value : Stored) :
    ∃ output, select value = ok output ∧ 7 ≤ output.val.val ∧ output.val.val ≤ 19 :=
  ⟨value.window, rfl, value.window.property⟩

end HasteBootsUsizeRangeProof
