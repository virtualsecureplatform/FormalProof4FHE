namespace HasteBootsWord64MemoryPointer
open Aeneas Aeneas.Std Result
open FormalProof4FHE.HasteBoots

/-- Only the phantom slice-value carrier changes; the heap view still has to
pass its own geometry, allocation, initialization and permission checks. -/
def decode {mutable : Bool} (pointer : NativeRawPointer.RawPtr (Slice U64) mutable) :
    NativeRawPointer.RawPtr (List NativeWord64Memory.Word) mutable :=
  NativeRawPointer.cast (List NativeWord64Memory.Word) mutable pointer

theorem decode_storage {mutable : Bool} (pointer : NativeRawPointer.RawPtr (Slice U64) mutable) :
    (decode pointer).storage = pointer.storage := rfl

theorem decode_metadata {mutable : Bool} (pointer : NativeRawPointer.RawPtr (Slice U64) mutable) :
    (decode pointer).metadata = pointer.metadata := rfl

theorem source_mutable_borrow (state : NativeByteBorrow.State) (parent : Option Nat)
    (pointer : HasteBootsPointerRuntime.MutRawPtr U64) (length : U64) :
    (do let result ← hasteboots_word64_memory.mutable_words pointer length
        pure (NativeWord64Memory.borrowSlice state parent .exclusive (decode result))) =
      ok (NativeByteBorrow.borrow state parent .exclusive pointer.storage ⟨8 * length.val, 8⟩) := rfl

theorem source_shared_borrow (state : NativeByteBorrow.State) (parent : Option Nat)
    (pointer : HasteBootsPointerRuntime.ConstRawPtr U64) (length : U64) :
    (do let result ← hasteboots_word64_memory.shared_words pointer length
        pure (NativeWord64Memory.borrowSlice state parent .shared (decode result))) =
      ok (NativeByteBorrow.borrow state parent .shared pointer.storage ⟨8 * length.val, 8⟩) := rfl

theorem source_mutable_element (pointer : HasteBootsPointerRuntime.MutRawPtr U64) (length : U64) (index : Nat) :
    (do let result ← hasteboots_word64_memory.mutable_words pointer length
        pure (NativeWord64Memory.element (decode result) index)) =
      ok (if index < length.val ∧ NativeByteRange.Geometry pointer.storage ⟨8 * length.val, 8⟩ then
        (NativeByteRange.pointerAt pointer.storage (8 * index)).map
          (fun reference => (⟨reference, .thin⟩ : NativeRawPointer.RawPtr NativeWord64Memory.Word true))
      else none) := rfl

def word (value : U64) : NativeWord64Memory.Word := value.bv.toFin

theorem word_value (value : U64) : (word value).val = value.val := rfl

theorem word_roundtrip (value : U64) : (⟨BitVec.ofFin (word value)⟩ : U64) = value := by
  cases value
  rfl

theorem source_store_load (state next : NativeByteMemory.State) (pointer : HasteBootsPointerRuntime.MutRawPtr U64) (value : U64)
    (stored : NativeWord64Memory.store state pointer.storage (word value) = some next) :
    NativeWord64Memory.load next pointer.storage = some (word value) :=
  NativeWord64Memory.store_then_load state next pointer.storage (word value) stored

end HasteBootsWord64MemoryPointer
