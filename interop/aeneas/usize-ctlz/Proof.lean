/-! Defined-input and guarded-call correctness of actual extracted functions. -/
namespace HasteBootsExtractedUsizeCtlzProof
open Aeneas Aeneas.Std
open hasteboots_usize_ctlz

theorem raw_model (input : Usize) : raw_count input = HasteBootsUsizeCtlz.nonzero input := rfl

theorem raw_defined (input : Usize) (positive : input.val ≠ 0) :
    raw_count input = .ok (core.num.Usize.leading_zeros input) :=
  HasteBootsUsizeCtlz.nonzero_result input positive

theorem raw_undefined_rejected (input : Usize) (zero : input.val = 0) :
    raw_count input = .fail .undef := HasteBootsUsizeCtlz.zero_rejected input zero

theorem count_zero : count 0#usize = .ok none := by
  simp only [count,ite_true]

theorem count_defined (input : Usize) (positive : input.val ≠ 0) :
    count input = .ok (some (core.num.Usize.leading_zeros input)) := by
  have notZero : input ≠ 0#usize := by
    intro same
    apply positive
    rw [same]
    rfl
  simp only [count,notZero,ite_false,HasteBootsUsizeCtlz.nonzero_result input positive]
  rfl

theorem count_total (input : Usize) :
    count input = .ok (if input.val = 0 then none else some (core.num.Usize.leading_zeros input)) := by
  by_cases zero : input.val = 0
  · have same : input = 0#usize := UScalar.eq_of_val_eq zero
    rw [ite_eq_left zero]
    exact same.symm ▸ count_zero
  · rw [count_defined input zero,ite_eq_right zero]

theorem raw_value (input : Usize) (positive : input.val ≠ 0) :
    (do let result ← raw_count input; pure result.val) =
      (Result.ok (UScalarTy.Usize.numBits - Nat.log 2 input.val - 1)) := by
  rw [raw_defined input positive]
  change Result.ok (core.num.Usize.leading_zeros input).val = _
  rw [HasteBootsUsizeCtlz.leading_value input positive]

end HasteBootsExtractedUsizeCtlzProof
