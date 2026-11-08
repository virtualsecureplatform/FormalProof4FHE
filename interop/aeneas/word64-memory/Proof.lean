namespace hasteboots_word64_memory
open Aeneas Aeneas.Std Result

theorem shared_words_exact (pointer : HasteBootsPointerRuntime.ConstRawPtr U64) (length : U64) :
    shared_words pointer length = ok (HasteBootsPointerPartsRuntime.from_slice_const (Slice U64) pointer length) := rfl

theorem mutable_words_exact (pointer : HasteBootsPointerRuntime.MutRawPtr U64) (length : U64) :
    mutable_words pointer length = ok (HasteBootsPointerPartsRuntime.from_slice_mut (Slice U64) pointer length) := rfl

theorem original_shared_exact (pointer : HasteBootsPointerRuntime.ConstRawPtr U64) (length : U64) :
    core.ptr.slice_from_raw_parts.mono_260b869b63d04e310fd2d7999d22ff55 pointer length =
      ok (HasteBootsPointerPartsRuntime.from_slice_const (Slice U64) pointer length) := rfl

theorem original_mutable_exact (pointer : HasteBootsPointerRuntime.MutRawPtr U64) (length : U64) :
    core.ptr.slice_from_raw_parts_mut.mono_a90570ea2daa7870227fd51b0cbe74b8 pointer length =
      ok (HasteBootsPointerPartsRuntime.from_slice_mut (Slice U64) pointer length) := rfl

theorem word_size_exact : WORD_SIZE = 8#u64 := by unfold WORD_SIZE; rfl

theorem word_alignment_exact : WORD_ALIGN = 8#u64 := by unfold WORD_ALIGN; rfl

theorem word_layout_exact : word_layout = ok (8#u64, 8#u64) := by
  simp only [word_layout, WORD_SIZE, WORD_ALIGN]

end hasteboots_word64_memory
