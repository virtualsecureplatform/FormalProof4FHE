module
import FormalProof4FHE.HasteBoots.NativeRecordHeapBounds
namespace FormalProof4FHETest.HasteBootsHeapReleaseSmoke
open FormalProof4FHE.HasteBoots
open NativeHeapRelease (Releases)
open NativeHeapLoss (Loss)
private def dataPointer : NativePointerStorage.Pointer := ⟨64,some ⟨64,0⟩⟩
private def slotPointer : NativePointerStorage.Pointer := ⟨128,some ⟨128,1⟩⟩
private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.writeBytes 0 1 (List.replicate 8 0)),
     .raw (.allocate 128 ⟨8,8⟩),.raw (.store 0 1)]).getD NativeReferenceMachine.empty
private def freed : NativeReferenceMachine.State :=
  (NativeByteDeallocation.execute ready ⟨dataPointer,none⟩ 8 1).getD NativeReferenceMachine.empty
private theorem release : Releases ready.pointers.heap freed.pointers.heap :=
  .free (.refl _) dataPointer ⟨8,1⟩ (by decide) (by decide) (by decide) (by decide)
example : freed.pointers.heap.memory.blocks.length = 1 := by decide
example : freed.pointers.heap.shadow = ready.pointers.heap.shadow := by decide
example : NativePointerByteMemory.load freed.pointers.heap slotPointer = some dataPointer := by decide
example : NativeByteRange.loadRange freed.pointers.heap.memory dataPointer ⟨8,1⟩ = none := by decide
example : freed.pointers.heap.memory.nextGeneration = ready.pointers.heap.memory.nextGeneration := release.generation

private def reused : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute freed (.raw (.allocate 64 ⟨8,1⟩))).getD NativeReferenceMachine.empty
example : reused.pointers.registers[0]? = some ⟨64,some ⟨64,2⟩⟩ := by decide
-- Stored dangling values retain the old origin even after address reuse.
example : NativePointerByteMemory.load reused.pointers.heap slotPointer = some dataPointer := by decide
example : NativeByteRange.loadRange reused.pointers.heap.memory dataPointer ⟨1,1⟩ = none := by decide

private def damaged : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute freed (.raw (.writeBytes 0 1 [7]))).getD NativeReferenceMachine.empty
private def damagedBlock : NativeByteMemory.Block :=
  ⟨⟨128,1⟩,128,⟨8,8⟩,some 7 :: List.replicate 7 (some 0)⟩
-- The former count-only premises hold, but the exact-release path rejects damage.
example : NativeHeapLoss.count damaged ≤ NativeHeapLoss.count ready ∧
    NativeHeapLoss.count ready ≤ NativeHeapLoss.count damaged + 1 ∧
    (NativeHeapLoss.count damaged = NativeHeapLoss.count ready → damaged.pointers.heap = ready.pointers.heap) := by decide
example : ¬ Loss ready damaged 1 := by
  intro bound
  have member : damagedBlock ∈ damaged.pointers.heap.memory.blocks := by decide
  have missing : damagedBlock ∉ ready.pointers.heap.memory.blocks := by decide
  exact missing (bound.released.blocks_sublist.subset member)

private def twice : NativeReferenceMachine.State :=
  (NativeByteDeallocation.execute freed ⟨slotPointer,none⟩ 8 8).getD NativeReferenceMachine.empty
example : twice.pointers.heap.memory.blocks.length = 0 := by decide
example : ¬ Loss ready twice 1 := by
  intro bound
  have before : NativeHeapLoss.count ready = 2 := by decide
  have after : NativeHeapLoss.count twice = 0 := by decide
  have bounded := bound.bounded
  omega
end FormalProof4FHETest.HasteBootsHeapReleaseSmoke
