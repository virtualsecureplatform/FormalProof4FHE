namespace HasteBootsCapturedOptionProof
open Aeneas Aeneas.Std Result
open hasteboots_captured_option

theorem none_exact (expected : Usize) :
    captured_option none expected = ok true := rfl

theorem some_exact (actual expected : Usize) :
    captured_option (some actual) expected = ok (actual != expected) := by
  rfl

end HasteBootsCapturedOptionProof
