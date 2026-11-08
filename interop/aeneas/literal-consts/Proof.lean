namespace hasteboots_literal_consts
open Aeneas Aeneas.Std Result

theorem width_exact : WIDTH = 31#u64 := by unfold WIDTH; rfl
theorem mask_exact : MASK = 81985529216486895#u64 := by unfold MASK; rfl
theorem zero_exact : ZERO = 0#u8 := by unfold ZERO; rfl
theorem negative_exact : NEGATIVE = (-17)#i64 := by unfold NEGATIVE; rfl
theorem wide_exact : WIDE = 340282366920938463463374607431768211455#u128 := by unfold WIDE; rfl

theorem values_exact : values = ok (31#u64, 81985529216486895#u64, 0#u8, (-17)#i64,
    340282366920938463463374607431768211455#u128) := by
  simp only [values, WIDTH, MASK, ZERO, NEGATIVE, WIDE]

end hasteboots_literal_consts
