namespace HasteBootsStdlibConfigurationProof
open Aeneas Aeneas.Std Result

theorem default_on : hasteboots_stdlib_default_on.core.ub_checks.check_language_ub = ok true := rfl

theorem default_off : hasteboots_stdlib_default_off.core.ub_checks.check_language_ub = ok false := rfl

theorem miri_on : hasteboots_stdlib_miri_on.core.ub_checks.check_language_ub = ok false := rfl

theorem default_on_miri_differ :
    hasteboots_stdlib_default_on.core.ub_checks.check_language_ub ≠
      hasteboots_stdlib_miri_on.core.ub_checks.check_language_ub := by
  rw [default_on, miri_on]
  intro same
  cases same

theorem default_on_off_differ :
    hasteboots_stdlib_default_on.core.ub_checks.check_language_ub ≠
      hasteboots_stdlib_default_off.core.ub_checks.check_language_ub := by
  rw [default_on, default_off]
  intro same
  cases same

end HasteBootsStdlibConfigurationProof
