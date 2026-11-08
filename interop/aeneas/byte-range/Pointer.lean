namespace HasteBootsByteRangePointer
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots
open NativeByteMemory (State)

/-- A byte-view decoder changes only the phantom pointee index. It does not
create a Rust slice reference or a borrow permission. -/
def decode {mutable : Bool} (pointer : NativeRawPointer.RawPtr (Slice U8) mutable) :
    NativeRawPointer.RawPtr (List NativeByteMemory.Byte) mutable :=
  NativeRawPointer.cast (List NativeByteMemory.Byte) mutable pointer

theorem decode_storage {mutable : Bool} (pointer : NativeRawPointer.RawPtr (Slice U8) mutable) :
    (decode pointer).storage = pointer.storage := rfl

theorem decode_metadata {mutable : Bool} (pointer : NativeRawPointer.RawPtr (Slice U8) mutable) :
    (decode pointer).metadata = pointer.metadata := rfl

theorem source_const_range (state : State) (pointer : HasteBootsPointerRuntime.ConstRawPtr U8) (length : U64) :
    (do
      let result ← hasteboots_pointer_parts.slice_const pointer length;
      pure (NativeByteRange.loadSlice state (decode result))) =
      ok (NativeByteRange.loadRange state pointer.storage ⟨length.val, 1⟩) := rfl

theorem source_mut_range (state : State) (pointer : HasteBootsPointerRuntime.MutRawPtr U8) (length : U64) :
    (do
      let result ← hasteboots_pointer_parts.slice_mut pointer length;
      pure (NativeByteRange.loadSlice state (decode result))) =
      ok (NativeByteRange.loadRange state pointer.storage ⟨length.val, 1⟩) := rfl

theorem source_cast_range (state : State) (pointer : HasteBootsPointerRuntime.MutRawPtr U8) (length : U64) :
    (do
      let result ← hasteboots_pointer_parts.slice_const_from_mut pointer length;
      pure (NativeByteRange.loadSlice state (decode result))) =
      ok (NativeByteRange.loadRange state pointer.storage ⟨length.val, 1⟩) := rfl

theorem original_mut_range (state : State) (pointer : HasteBootsPointerRuntime.MutRawPtr U8) (length : U64) :
    (do
      let result ← hasteboots_pointer_parts.core.ptr.metadata.from_raw_parts_mut.mono_22ec1cc9473a101a472accb7192baec7 pointer length;
      pure (NativeByteRange.loadSlice state (decode result))) =
      ok (NativeByteRange.loadRange state pointer.storage ⟨length.val, 1⟩) := rfl

theorem original_const_range (state : State) (pointer : HasteBootsPointerRuntime.ConstRawPtr U8) (length : U64) :
    (do
      let result ← hasteboots_pointer_parts.core.ptr.metadata.from_raw_parts.mono_422d76a278de43af91049b4bc99c6b4f pointer length;
      pure (NativeByteRange.loadSlice state (decode result))) =
      ok (NativeByteRange.loadRange state pointer.storage ⟨length.val, 1⟩) := rfl

theorem source_mut_single_allocation (state : State) (pointer : HasteBootsPointerRuntime.MutRawPtr U8)
    (length : U64) (positive : 0 < length.val) (output : List NativeByteMemory.Byte)
    (executed : (do
      let result ← hasteboots_pointer_parts.slice_mut pointer length;
      pure (NativeByteRange.loadSlice state (decode result))) = ok (some output)) :
    ∃ block ∈ state.blocks, pointer.storage.provenance = some block.origin ∧
      block.base.val ≤ pointer.storage.address.val ∧
      pointer.storage.address.val + length.val ≤ block.base.val + block.layout.size := by
  rw [source_mut_range] at executed
  exact NativeByteRange.positive_range_single_allocation state pointer.storage ⟨length.val, 1⟩
    positive output (Result.ok.inj executed)

theorem source_mut_exact_length (state : State) (pointer : HasteBootsPointerRuntime.MutRawPtr U8)
    (length : U64) (output : List NativeByteMemory.Byte)
    (executed : (do
      let result ← hasteboots_pointer_parts.slice_mut pointer length;
      pure (NativeByteRange.loadSlice state (decode result))) = ok (some output)) : output.length = length.val := by
  rw [source_mut_range] at executed
  exact NativeByteRange.loadRange_length state pointer.storage ⟨length.val, 1⟩ output (Result.ok.inj executed)

end HasteBootsByteRangePointer
