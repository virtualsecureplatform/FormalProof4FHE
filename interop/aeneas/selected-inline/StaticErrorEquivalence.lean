namespace HasteBootsStaticErrorEquivalence
open Aeneas Aeneas.Std Result
open hasteboots_static_error_option

theorem convert_equivalent (value : Option Usize) : convert value = direct value := by
  cases value <;> rfl

theorem eager_equivalent (value : Option Usize) : eager_match value = direct value := rfl

end HasteBootsStaticErrorEquivalence
