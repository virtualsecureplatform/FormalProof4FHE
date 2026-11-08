namespace HasteBootsOverflowingMulProof
open Aeneas Aeneas.Std Result
open hasteboots_overflowing_mul

theorem unsigned_exact (value rhs : U64) :
    unsigned value rhs = ok (UScalar.overflowing_mul value rhs) := by
  simp [unsigned, hasteboots_overflowing_mul.core.num.Usize.overflowing_mul,
    UScalar.cast, UScalar.overflowing_mul, lift]

theorem signed_exact (value rhs : I64) :
    signed value rhs = ok (IScalar.overflowing_mul value rhs) := by
  simp [signed, hasteboots_overflowing_mul.core.num.Isize.overflowing_mul,
    IScalar.cast, IScalar.overflowing_mul, lift]

theorem unsigned_spec (value rhs : U64) :
    let z := UScalar.overflowing_mul value rhs
    unsigned value rhs = ok z ∧
    if value.val * rhs.val > UScalar.max .U64 then
      z.fst.val = (value.val * rhs.val) % UScalar.size .U64 ∧ z.snd = true
    else z.fst.val = value.val * rhs.val ∧ z.snd = false := by
  exact ⟨unsigned_exact value rhs, UScalar.overflowing_mul_eq value rhs⟩

theorem unsigned_wrap :
    unsigned 18446744073709551615#u64 2#u64 = ok (18446744073709551614#u64, true) := by
  rw [unsigned_exact]; rfl

theorem unsigned_high_product :
    unsigned 9223372036854775808#u64 2#u64 = ok (0#u64, true) := by
  rw [unsigned_exact]; rfl

theorem signed_min_negation :
    signed (-9223372036854775808)#i64 (-1)#i64 = ok ((-9223372036854775808)#i64, true) := by
  rw [signed_exact]; rfl

theorem signed_negative_product :
    signed 9223372036854775807#i64 (-2)#i64 = ok (2#i64, true) := by
  rw [signed_exact]; rfl

theorem signed_safe_min :
    signed (-9223372036854775808)#i64 1#i64 = ok ((-9223372036854775808)#i64, false) := by
  rw [signed_exact]; rfl

end HasteBootsOverflowingMulProof
