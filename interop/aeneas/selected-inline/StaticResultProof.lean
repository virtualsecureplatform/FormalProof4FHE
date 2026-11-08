namespace HasteBootsStaticResultProof
open Aeneas Aeneas.Std Result
open hasteboots_static_result_input

abbrev NativeResult := core.result.Result.mono_cf5d9e832a18f6fc1c3c8168dfeb0b72

def expectedError : Str := toStr "table size overflow"
  (by simp only [U32.max, U32.numBits, UScalarTy.U32_numBits_eq]; decide +kernel)

theorem field_identity (error : hasteboots_static_result_input.Error) :
    error_field error = ok error := rfl

theorem choose_identity (value : NativeResult) : choose value = ok value := by
  cases value <;> rfl

theorem propagate_some (value : Usize) : propagate (some value) = ok (.Ok value) := rfl

theorem propagate_none : propagate none = ok (.Err expectedError) := rfl

end HasteBootsStaticResultProof
