namespace HasteBootsRuntimeChecksProof
open Aeneas Aeneas.Std Result

theorem on_checks : hasteboots_runtime_checks_on.checks = ok (true, true) := rfl

theorem on_guarded (input : U32) :
    hasteboots_runtime_checks_on.guarded input =
      ok (if input = 0#u32 then 17#u32 else input) := by
  by_cases h : input = 0#u32 <;>
    simp only [hasteboots_runtime_checks_on.guarded, h, ite_true, ite_false]

theorem off_checks : hasteboots_runtime_checks_off.checks = ok (false, false) := rfl

theorem off_guarded (input : U32) : hasteboots_runtime_checks_off.guarded input = ok input := rfl

theorem override_checks : hasteboots_runtime_checks_override.checks = ok (false, true) := rfl

theorem override_guarded (input : U32) :
    hasteboots_runtime_checks_override.guarded input = ok input := rfl

end HasteBootsRuntimeChecksProof
