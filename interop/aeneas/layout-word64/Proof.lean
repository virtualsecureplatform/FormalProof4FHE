namespace HasteBootsLayoutWord64Proof
open Aeneas Aeneas.Std Result
open hasteboots_layout_word64
abbrev Layout := hasteboots_layout_word64.core.alloc.layout.Layout
abbrev Alignment := hasteboots_layout_word64.core.mem.alignment.Alignment
abbrev Tag := hasteboots_layout_word64.core.mem.alignment.AlignmentEnum

theorem preserve_exact (value : Layout) : preserve value = ok value := rfl

theorem size_exact (value : Layout) : size value = ok value.size := rfl

theorem align_exact (value : Layout) :
    align value = ok (hasteboots_layout_word64.core.mem.alignment.AlignmentEnum.read_discriminant value.align._inner_repr_trick) := by
  rcases value with ⟨s, ⟨tag⟩⟩
  cases tag <;> rfl

theorem high_alignment :
    align ⟨0#u64, ⟨._Align1Shl63⟩⟩ = ok 9223372036854775808#u64 := rfl

theorem word_max_exact : word_max = ok 18446744073709551615#u64 := by
  unfold word_max hasteboots_layout_word64.core.num.Usize.MAX
  rfl

theorem signed_min_exact : signed_min = ok (-9223372036854775808)#i64 := by
  unfold signed_min hasteboots_layout_word64.core.num.Isize.MIN
    hasteboots_layout_word64.core.num.Isize.MAX hasteboots_layout_word64.core.num.Usize.MAX
  rfl

theorem signed_identity_exact (value : I64) : signed_identity value = ok value := rfl

theorem overflowing_add_exact (value : U64) :
    overflowing_add_one value = ok (UScalar.overflowing_add value 1#u64) := by
  simp [overflowing_add_one, hasteboots_layout_word64.core.num.Usize.overflowing_add,
    UScalar.cast, UScalar.overflowing_add, lift]

theorem signed_overflowing_add_exact (value : I64) :
    signed_overflowing_add_one value = ok (IScalar.overflowing_add value 1#i64) := by
  simp [signed_overflowing_add_one, hasteboots_layout_word64.core.num.Isize.overflowing_add,
    IScalar.cast, IScalar.overflowing_add, lift]

theorem unsigned_overflow :
    overflowing_add_one 18446744073709551615#u64 = ok (0#u64, true) := by
  rw [overflowing_add_exact]; rfl

theorem unsigned_high_add :
    overflowing_add_one 9223372036854775808#u64 = ok (9223372036854775809#u64, false) := by
  rw [overflowing_add_exact]; rfl

theorem signed_overflow :
    signed_overflowing_add_one 9223372036854775807#i64 = ok ((-9223372036854775808)#i64, true) := by
  rw [signed_overflowing_add_exact]; rfl

end HasteBootsLayoutWord64Proof
