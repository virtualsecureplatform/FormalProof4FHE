/-! Defined-input and guarded-call correctness of actual extracted functions. -/
namespace HasteBootsExtractedWord64IntrinsicsProof
open Aeneas Aeneas.Std
open hasteboots_word64_intrinsics

theorem raw_model (input : U64) : raw_leading input = HasteBootsWord64Intrinsics.leading input := rfl

theorem raw_defined (input : U64) (positive : input.val ≠ 0) :
    raw_leading input = .ok (core.num.U64.leading_zeros input) :=
  HasteBootsWord64Intrinsics.leading_nonzero input positive

theorem raw_undefined_rejected (input : U64) (zero : input.val = 0) :
    raw_leading input = .fail .undef := HasteBootsWord64Intrinsics.leading_zero input zero

theorem count_zero : checked_leading 0#u64 = .ok none := by
  simp only [checked_leading,ite_true]

theorem count_defined (input : U64) (positive : input.val ≠ 0) :
    checked_leading input = .ok (some (core.num.U64.leading_zeros input)) := by
  have notZero : input ≠ 0#u64 := by
    intro same
    apply positive
    rw [same]
    rfl
  simp only [checked_leading,notZero,ite_false,HasteBootsWord64Intrinsics.leading_nonzero input positive]
  rfl

theorem count_total (input : U64) :
    checked_leading input = .ok (if input.val = 0 then none else some (core.num.U64.leading_zeros input)) := by
  by_cases zero : input.val = 0
  · have same : input = 0#u64 := UScalar.eq_of_val_eq zero
    rw [ite_eq_left zero]
    exact same.symm ▸ count_zero
  · rw [count_defined input zero,ite_eq_right zero]

theorem raw_value (input : U64) (positive : input.val ≠ 0) :
    (do let result ← raw_leading input; pure result.val) =
      (Result.ok (64 - Nat.log 2 input.val - 1)) := by
  rw [raw_defined input positive]
  change Result.ok (core.num.U64.leading_zeros input).val = _
  rw [HasteBootsWord64Intrinsics.leading_value input positive]

theorem population_exact (input : U64) :
    population input = .ok (HasteBootsWord64Intrinsics.population input) := rfl

theorem population_value (input : U64) :
    (do let result ← population input; pure result.val) = Result.ok input.bv.cpop.toNat := by
  rw [population_exact]
  exact congrArg Result.ok (HasteBootsWord64Intrinsics.population_value input)

theorem power_of_two_exact (input : U64) :
    power_of_two input = .ok (decide ((HasteBootsWord64Intrinsics.population input) = 1#u32)) := rfl

theorem power_of_two_high : power_of_two 9223372036854775808#u64 = .ok true := rfl

theorem power_of_two_high_plus_one : power_of_two 9223372036854775809#u64 = .ok false := rfl

end HasteBootsExtractedWord64IntrinsicsProof
