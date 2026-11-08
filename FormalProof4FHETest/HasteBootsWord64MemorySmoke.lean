module
import all FormalProof4FHE.HasteBoots.NativeWord64Memory

namespace HasteBootsWord64MemorySmoke
open FormalProof4FHE.HasteBoots
open NativeByteMemory (State Byte)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)

private def allocated : Option (Pointer × State) := NativeByteMemory.allocate NativeByteMemory.empty ⟨64, by decide⟩ ⟨24, 8⟩
private def bytes16 : List Byte := [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]
private def borrowed : Option (Pointer × Nat × NativeByteBorrow.State) := do
  let (p, memory) ← allocated
  let memory ← NativeByteRangeWrite.storeRange memory p 8 bytes16
  let (tag, state) ← NativeByteBorrow.borrow ⟨memory, 0, []⟩ none .exclusive p ⟨16, 8⟩
  pure (p, tag, state)

example : (do let (p, state) ← allocated; NativeWord64Memory.load state p) = none := by decide
example : (do
    let (p, state) ← allocated
    let state ← NativeWord64Memory.store state p ⟨0, by decide⟩
    NativeWord64Memory.load state p) = some ⟨0, by decide⟩ := by decide
example : (do
    let (p, state) ← allocated
    let state ← NativeWord64Memory.store state p ⟨0x0102030405060708, by decide⟩
    NativeByteRange.loadRange state p ⟨8, 8⟩) = some [8,7,6,5,4,3,2,1] := by decide
example : (do
    let (p, state) ← allocated
    let state ← NativeWord64Memory.store state p ⟨2^64-1, by decide⟩
    NativeWord64Memory.load state p) = some ⟨2^64-1, by decide⟩ := by decide
example : NativeWord64Memory.decode [255,255,255,255,255,255,255,255] = some ⟨2^64-1, by decide⟩ := by decide
example : NativeWord64Memory.decode [1,2,3,4,5,6,7] = none := by decide
example : NativeWord64Memory.decode [1,2,3,4,5,6,7,8,9] = none := by decide
example : (do
    let (p, state) ← allocated
    let q ← NativeByteRange.pointerAt p 8
    let state ← NativeWord64Memory.store state q ⟨77, by decide⟩
    let before := NativeByteMemory.loadByte state p
    let after ← NativeByteRange.pointerAt p 16
    pure (before, NativeByteMemory.loadByte state after)) = some (none, none) := by decide
example : (do
    let (p, state) ← allocated
    let q ← NativeByteRange.pointerAt p 1
    NativeWord64Memory.store state q ⟨77, by decide⟩) = none := by decide
example : (do
    let (p, state) ← allocated
    let q ← NativeByteRange.pointerAt p 24
    NativeWord64Memory.store state q ⟨77, by decide⟩) = none := by decide
example : (do
    let (p, state) ← allocated
    let state ← NativeByteRangeWrite.storeRange state p 8 bytes16
    NativeByteRange.loadRange state p ⟨16, 8⟩) = some bytes16 := by decide
example : (do
    let (p, state) ← allocated
    let state ← NativeByteRangeWrite.storeRange state p 8 bytes16
    let q ← NativeByteRange.pointerAt p 4
    let state ← NativeByteRangeWrite.storeRange state q 1 [99,98,97]
    NativeByteRange.loadRange state p ⟨16, 8⟩) = some [1,2,3,4,99,98,97,8,9,10,11,12,13,14,15,16] := by decide
example : NativeByteRangeWrite.storeRange NativeByteMemory.empty ⟨⟨64, by decide⟩, none⟩ 8 [] = some NativeByteMemory.empty := by decide
example : NativeByteRangeWrite.storeRange NativeByteMemory.empty ⟨⟨0, by decide⟩, none⟩ 8 [] = none := by decide
example : (do
    let (p, state) ← allocated
    let state ← NativeByteMemory.deallocate state p ⟨24, 8⟩
    NativeWord64Memory.store state p ⟨77, by decide⟩) = none := by decide
example : (do
    let (p, state) ← allocated
    let state ← NativeByteMemory.deallocate state p ⟨24, 8⟩
    let (_, state) ← NativeByteMemory.allocate state ⟨64, by decide⟩ ⟨24, 8⟩
    NativeWord64Memory.store state p ⟨77, by decide⟩) = none := by decide
example : (do
    let (p, parent, state) ← borrowed
    let (_, state) ← NativeByteBorrow.borrow state (some parent) .exclusive p ⟨8, 8⟩
    let state ← NativeByteRangeWrite.write state parent 8 [99,98,97,96,95,94,93,92]
    NativeByteRange.loadRange state.memory p ⟨16, 8⟩) = some [1,2,3,4,5,6,7,8,99,98,97,96,95,94,93,92] := by decide
example : (do
    let (p, parent, state) ← borrowed
    let (_, state) ← NativeByteBorrow.borrow state (some parent) .exclusive p ⟨8, 8⟩
    NativeByteRangeWrite.write state parent 4 [99,98,97,96,95,94,93,92]) = none := by decide
example : (do
    let (p, _, state) ← borrowed
    NativeWord64Memory.rawWrite state p ⟨77, by decide⟩) = none := by decide
example : (do
    let (p, parent, state) ← borrowed
    let state ← NativeByteBorrow.endBorrow state parent
    let state ← NativeWord64Memory.rawWrite state p ⟨77, by decide⟩
    pure (NativeByteBorrow.lookup state.leases parent)) = some none := by decide

private def words (p : Pointer) (length : Nat) (fits : length < 2^64) : NativeRawPointer.RawPtr (List Word) true :=
  ⟨p, .slice ⟨length, fits⟩⟩

example : (do
    let (p, _) ← allocated
    let result ← NativeWord64Memory.element (words p 2 (by decide)) 1
    pure result.storage.address.val) = some 72 := by decide
example : (do
    let (p, _) ← allocated
    NativeWord64Memory.element (words p 2 (by decide)) 2) = none := by decide
example : NativeWord64Memory.element (words ⟨⟨64, by decide⟩, none⟩ (2^64-1) (by decide)) 0 = none := by decide
example : (do
    let (p, _, state) ← borrowed
    let state ← NativeByteBorrow.endBorrow state 0
    let (tag, state) ← NativeWord64Memory.borrowSlice state none .exclusive (words p 2 (by decide))
    let lease ← NativeByteBorrow.lookup state.leases tag
    pure lease.layout) = some ⟨16, 8⟩ := by decide

end HasteBootsWord64MemorySmoke
