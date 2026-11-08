namespace HasteBootsByteBorrowPointer
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots
open NativeByteBorrow (State Mode)

theorem source_shared (state : State) (parent : Option Nat)
    (pointer : HasteBootsPointerRuntime.ConstRawPtr U8) (length : U64) :
    (do
      let result ← hasteboots_pointer_parts.slice_const pointer length
      pure (NativeByteBorrow.borrowSlice state parent .shared (HasteBootsByteRangePointer.decode result))) =
      ok (NativeByteBorrow.borrow state parent .shared pointer.storage ⟨length.val, 1⟩) := rfl

theorem source_exclusive (state : State) (parent : Option Nat)
    (pointer : HasteBootsPointerRuntime.MutRawPtr U8) (length : U64) :
    (do
      let result ← hasteboots_pointer_parts.slice_mut pointer length
      pure (NativeByteBorrow.borrowSlice state parent .exclusive (HasteBootsByteRangePointer.decode result))) =
      ok (NativeByteBorrow.borrow state parent .exclusive pointer.storage ⟨length.val, 1⟩) := rfl

theorem source_cast_shared (state : State) (parent : Option Nat)
    (pointer : HasteBootsPointerRuntime.MutRawPtr U8) (length : U64) :
    (do
      let result ← hasteboots_pointer_parts.slice_const_from_mut pointer length
      pure (NativeByteBorrow.borrowSlice state parent .shared (HasteBootsByteRangePointer.decode result))) =
      ok (NativeByteBorrow.borrow state parent .shared pointer.storage ⟨length.val, 1⟩) := rfl

theorem original_exclusive (state : State) (parent : Option Nat)
    (pointer : HasteBootsPointerRuntime.MutRawPtr U8) (length : U64) :
    (do
      let result ← hasteboots_pointer_parts.core.ptr.metadata.from_raw_parts_mut.mono_22ec1cc9473a101a472accb7192baec7 pointer length
      pure (NativeByteBorrow.borrowSlice state parent .exclusive (HasteBootsByteRangePointer.decode result))) =
      ok (NativeByteBorrow.borrow state parent .exclusive pointer.storage ⟨length.val, 1⟩) := rfl

theorem issued_pointer_data (state : State) (parent : Option Nat)
    (pointer : HasteBootsPointerRuntime.MutRawPtr U8) (length : U64) (tag : Nat) (next : State)
    (executed : (do
      let result ← hasteboots_pointer_parts.slice_mut pointer length
      pure (NativeByteBorrow.borrowSlice state parent .exclusive (HasteBootsByteRangePointer.decode result))) = ok (some (tag, next))) :
    NativeByteBorrow.lookup next.leases tag = some ⟨tag, parent, pointer.storage, ⟨length.val, 1⟩, .exclusive⟩ := by
  rw [source_exclusive] at executed
  have leases := (NativeByteBorrow.borrow_success state parent .exclusive pointer.storage ⟨length.val, 1⟩ tag next
    (Result.ok.inj executed)).2.2.2.1
  rw [leases]
  exact ite_eq_left rfl

theorem issued_initialized_range (state : State) (parent : Option Nat)
    (pointer : HasteBootsPointerRuntime.MutRawPtr U8) (length : U64) (tag : Nat) (next : State)
    (executed : (do
      let result ← hasteboots_pointer_parts.slice_mut pointer length
      pure (NativeByteBorrow.borrowSlice state parent .exclusive (HasteBootsByteRangePointer.decode result))) = ok (some (tag, next))) :
    ∃ bytes, NativeByteRange.loadRange state.memory pointer.storage ⟨length.val, 1⟩ = some bytes := by
  rw [source_exclusive] at executed
  exact (NativeByteBorrow.borrow_success state parent .exclusive pointer.storage ⟨length.val, 1⟩ tag next
    (Result.ok.inj executed)).2.2.2.2.2

theorem shared_parent_rejected (state : State) (parent : Nat)
    (pointer : HasteBootsPointerRuntime.MutRawPtr U8) (length : U64) (lease : NativeByteBorrow.Lease)
    (found : NativeByteBorrow.lookup state.leases parent = some lease) (shared : lease.mode = .shared) :
    (do
      let result ← hasteboots_pointer_parts.slice_mut pointer length
      pure (NativeByteBorrow.borrowSlice state (some parent) .exclusive (HasteBootsByteRangePointer.decode result))) = ok none := by
  rw [source_exclusive]
  unfold NativeByteBorrow.borrow
  rw [NativeByteBorrow.shared_parent_no_upgrade state parent pointer.storage ⟨length.val, 1⟩ lease found shared]
  rfl

end HasteBootsByteBorrowPointer
