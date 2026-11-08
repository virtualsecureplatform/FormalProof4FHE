namespace HasteBootsEnumNonzeroProof
open Aeneas Aeneas.Std Result
open hasteboots_enum_nonzero

abbrev NZ := core.num.nonzero.NonZero.mono_9de22c9317cfc6682f822ca4cbc6ada3

theorem get_exact (value : NZ) : get value = ok value.val := rfl

theorem nonzero_bits (value : Alignment64) :
    (do let output ← nonzero value; pure output.val) = ok (read_discriminant value) := by
  cases value <;> rfl

theorem nonzero_total (value : Alignment64) : ∃ output, nonzero value = ok output := by
  cases value <;> exact ⟨_, rfl⟩

theorem nonzero_sound (value : Alignment64) (output : NZ)
    (executed : nonzero value = ok output) : output.val = read_discriminant value := by
  cases value <;> simp only [nonzero, lift, bind_tc_ok] at executed <;> cases executed <;> rfl

theorem nonzero_bounds (value : Alignment64) (output : NZ)
    (_executed : nonzero value = ok output) :
    1 ≤ output.val.val ∧ output.val.val ≤ 18446744073709551615 := output.property

theorem roundtrip_exact (value : Alignment64) :
    roundtrip value = ok (read_discriminant value) := by cases value <;> rfl

theorem high_bit : roundtrip .A63 = ok 9223372036854775808#u64 := rfl

end HasteBootsEnumNonzeroProof
