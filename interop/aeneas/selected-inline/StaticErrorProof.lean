namespace HasteBootsStaticErrorControls
open Aeneas Aeneas.Std Result
open hasteboots_static_error_option

theorem eager_equivalent (value : Option Usize) : eager_match value = direct value := rfl

end HasteBootsStaticErrorControls
