namespace HasteBootsTimeCarrierProof
open Aeneas Aeneas.Std Result
open hasteboots_time_carriers

theorem duration_exact (value : core.time.Duration) : preserve_duration value = ok value := rfl

theorem time_exact (value : std.time.SystemTime) : preserve_time value = ok value := rfl

theorem error_exact (value : std.time.SystemTimeError) : preserve_error value = ok value := rfl

theorem duration_nanos_bounds (value : core.time.Duration) :
    0 ≤ value.nanos.val.val ∧ value.nanos.val.val ≤ 999999999 := value.nanos.property

theorem time_nanos_bounds (value : std.time.SystemTime) :
    0 ≤ value.t.tv_nsec.val.val ∧ value.t.tv_nsec.val.val ≤ 999999999 := value.t.tv_nsec.property

end HasteBootsTimeCarrierProof
