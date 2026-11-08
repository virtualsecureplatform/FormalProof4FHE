namespace HasteBootsEnumDecodingProof
open Aeneas Aeneas.Std Result
open hasteboots_enum_decoding

theorem direct_roundtrip (value : Sparse) :
    direct (read_discriminant value) = ok value := by cases value <;> rfl

theorem wrapped_roundtrip (value : Sparse) :
    wrapped (read_discriminant value) = ok value := by cases value <;> rfl

theorem alignment_roundtrip (value : Alignment64) :
    alignment (read_discriminant value) = ok value := by cases value <;> rfl

theorem direct_zero : direct 0#u32 = fail .panic := rfl

theorem wrapped_invalid : wrapped 3#u32 = fail .panic := rfl

theorem alignment_zero : alignment 0#u64 = fail .panic := rfl

theorem alignment_three : alignment 3#u64 = fail .panic := rfl

theorem alignment_high : alignment 9223372036854775808#u64 = ok .A63 := rfl

theorem alignment_high_invalid : alignment 9223372036854775809#u64 = fail .panic := rfl

theorem wrapped_sound (input : U32) (output : Wrapped) (executed : wrapped input = ok output) :
    read_discriminant output = input := by
  unfold wrapped at executed
  split at executed <;> cases executed
  all_goals
    apply UScalar.eq_of_val_eq
    rfl

theorem alignment_sound (input : U64) (output : Align) (executed : alignment input = ok output) :
    read_discriminant output = input := by
  unfold alignment at executed
  repeat first
    | contradiction
    | (cases executed; apply UScalar.eq_of_val_eq; rfl)
    | split at executed

theorem direct_sound (input : U32) (output : Sparse) (executed : direct input = ok output) :
    read_discriminant output = input := by
  unfold direct at executed
  simp only [lift, bind_tc_ok] at executed
  split at executed
  all_goals first
    | contradiction
    | exact wrapped_sound input output executed

theorem alignment_accepts_iff (input : U64) :
    (∃ output, alignment input = ok output) ↔
    ∃ value : Alignment64, read_discriminant value = input := by
  constructor
  · rintro ⟨value, executed⟩
    exact ⟨value, alignment_sound input value executed⟩
  · rintro ⟨value, encoded⟩
    exact ⟨value, encoded ▸ alignment_roundtrip value⟩

theorem alignment_bits (value : Alignment64) :
    ∃ exponent : Fin 64, (read_discriminant value : U64).val = 2 ^ exponent.val := by
  cases value <;> decide

theorem alignment_valid_bits (input : U64) (output : Align)
    (executed : alignment input = ok output) :
    ∃ exponent : Fin 64, input.val = 2 ^ exponent.val := by
  obtain ⟨exponent, bits⟩ := alignment_bits output
  exact ⟨exponent, (congrArg UScalar.val (alignment_sound input output executed)).symm.trans bits⟩

end HasteBootsEnumDecodingProof
