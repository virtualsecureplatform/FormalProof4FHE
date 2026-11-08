namespace HasteBootsLargeDiscriminantProof
open Aeneas Aeneas.Std Result
open hasteboots_wide_discriminants

theorem preserve_exact (value : Wide64) : preserve value = ok value := rfl

theorem u64_zero : cast_u64 .Zero = ok 0#u64 := rfl

theorem u64_high : cast_u64 .High = ok 9223372036854775808#u64 := rfl

theorem u64_last : cast_u64 .Last = ok 18446744073709551615#u64 := rfl

theorem u128_zero : cast_u128 .Zero = ok 0#u128 := rfl

theorem u128_last :
    cast_u128 .Last = ok 340282366920938463463374607431768211455#u128 := rfl

theorem u64_high_value :
    (read_discriminant Wide64.High : U64).val = 9223372036854775808 := rfl

theorem u128_last_value :
    (read_discriminant Wide128.Last : U128).val = 340282366920938463463374607431768211455 := rfl

end HasteBootsLargeDiscriminantProof
