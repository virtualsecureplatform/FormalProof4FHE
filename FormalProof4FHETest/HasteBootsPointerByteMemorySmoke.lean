module
import all FormalProof4FHE.HasteBoots.NativePointerByteMemory

namespace HasteBootsPointerByteMemorySmoke
open FormalProof4FHE.HasteBoots
open NativePointerStorage (Pointer)
open NativePointerByteMemory (State)

private def allocated : Option (Pointer × Pointer × State) := do
  let (p, state) ← NativePointerByteMemory.allocate NativePointerByteMemory.empty ⟨64, by decide⟩ ⟨32, 8⟩
  let (q, state) ← NativePointerByteMemory.allocate state ⟨128, by decide⟩ ⟨8, 8⟩
  pure (p, q, state)

example : (do
    let (p, _, state) ← allocated
    NativePointerByteMemory.load state p) = none := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.store state p q
    let value ← NativePointerByteMemory.load state p
    pure (value == q)) = some true := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.store state p q
    NativeByteRange.loadRange state.memory p ⟨8, 8⟩) = some [128,0,0,0,0,0,0,0] := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.store state p q
    let state ← NativePointerByteMemory.writeWord state p q.address
    let value ← NativePointerByteMemory.load state p
    pure (value.address.val, value.provenance)) = some (128, none) := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.writeWord state p q.address
    let value ← NativePointerByteMemory.load state p
    NativePointerByteMemory.store state value p) = none := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.store state p q
    let slot ← NativeByteRange.pointerAt p 2
    let state ← NativePointerByteMemory.writeBytes state slot 1 [0]
    NativePointerByteMemory.load state p) = none := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.store state p q
    let slot ← NativeByteRange.pointerAt p 1
    NativePointerByteMemory.store state slot q) = none := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.store state p q
    let slot ← NativeByteRange.pointerAt p 8
    let state ← NativePointerByteMemory.copyNonoverlapping state p slot 8 8
    let value ← NativePointerByteMemory.load state slot
    pure (value == q)) = some true := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.store state p q
    NativePointerByteMemory.copyNonoverlapping state p p 8 8) = none := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.store state p q
    let slot ← NativeByteRange.pointerAt p 8
    let state ← NativePointerByteMemory.store state slot p
    let state ← NativePointerByteMemory.copy state p slot 16 8
    let first ← NativePointerByteMemory.load state slot
    let last ← NativeByteRange.pointerAt p 16
    let second ← NativePointerByteMemory.load state last
    pure (first == q, second == p)) = some (true, true) := by decide
example : (do
    let (p, _, state) ← allocated
    let slot ← NativeByteRange.pointerAt p 8
    let state ← NativePointerByteMemory.copy state p slot 8 8
    NativeRawByteRange.loadRange state.memory slot ⟨8, 8⟩) = some [none,none,none,none,none,none,none,none] := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.store state p q
    let state ← NativePointerByteMemory.deallocate state q ⟨8, 8⟩
    let value ← NativePointerByteMemory.load state p
    pure (value == q)) = some true := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.store state p q
    let state ← NativePointerByteMemory.deallocate state q ⟨8, 8⟩
    let (fresh, state) ← NativePointerByteMemory.allocate state ⟨128, by decide⟩ ⟨8, 8⟩
    let state ← NativePointerByteMemory.writeWord state fresh ⟨77, by decide⟩
    let value ← NativePointerByteMemory.load state p
    pure (value.address == fresh.address, value.provenance == fresh.provenance,
      NativeWord64Memory.load state.memory value)) = some (true, false, none) := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.store state p q
    let state ← NativePointerByteMemory.deallocate state p ⟨32, 8⟩
    pure state.shadow.length) = some 0 := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.store state p q
    let state ← NativePointerByteMemory.store state q p
    let state ← NativePointerByteMemory.deallocate state p ⟨32, 8⟩
    let value ← NativePointerByteMemory.load state q
    pure (state.shadow.length, value == p)) = some (8, true) := by decide
example : (do
    let (p, q, state) ← allocated
    let state ← NativePointerByteMemory.deallocate state p ⟨32, 8⟩
    NativePointerByteMemory.store state p q) = none := by decide
example : (do
    let (p, _, state) ← allocated
    let state ← NativePointerByteMemory.deallocate state p ⟨32, 8⟩
    NativePointerByteMemory.load state p) = none := by decide
private def null : Pointer := ⟨⟨0, by decide⟩, none⟩
example : NativePointerByteMemory.copy NativePointerByteMemory.empty null null 0 8 = some NativePointerByteMemory.empty := by decide
example : (do
    let (p, _, state) ← allocated
    let state ← NativePointerByteMemory.store state p null
    NativePointerByteMemory.load state p) = some null := by decide
end HasteBootsPointerByteMemorySmoke
