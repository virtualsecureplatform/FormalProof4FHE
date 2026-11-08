namespace HasteBootsU32RangeProof
open Aeneas Aeneas.Std Result
open hasteboots_u32_ranges

theorem preserve_exact (value : Stored) : preserve value = ok value := rfl

theorem select_exact (value : Stored) : select value = ok value.window := rfl

theorem identity_exact (value : { x : U32 // 0 ≤ x.val ∧ x.val ≤ 999999999 }) :
    identity value = ok value := rfl

theorem nanos_bounds (value : Stored) :
    0 ≤ value.nanos.val.val ∧ value.nanos.val.val ≤ 999999999 := value.nanos.property

theorem window_bounds (value : Stored) :
    7 ≤ value.window.val.val ∧ value.window.val.val ≤ 19 := value.window.property

theorem select_sound (value : Stored) :
    ∃ output, select value = ok output ∧ 7 ≤ output.val.val ∧ output.val.val ≤ 19 :=
  ⟨value.window, rfl, value.window.property⟩

end HasteBootsU32RangeProof
