module
import all FormalProof4FHE.HasteBoots.NativeByteRange

namespace HasteBootsByteRangeSmoke
open FormalProof4FHE.HasteBoots
open NativeByteMemory (Byte State)
open NativePointerStorage (Address Pointer)
open NativeByteRange

private def base : Address := ⟨64, by decide⟩
private def dangling : Pointer := ⟨base, none⟩

example : loadRange NativeByteMemory.empty dangling ⟨0, 1⟩ = some [] := by decide
example : loadRange NativeByteMemory.empty dangling ⟨0, 4⟩ = some [] := by decide
example : loadRange NativeByteMemory.empty ⟨0, none⟩ ⟨0, 1⟩ = none := by decide
example : loadRange NativeByteMemory.empty ⟨⟨65, by decide⟩, none⟩ ⟨0, 4⟩ = none := by decide
example : loadRange NativeByteMemory.empty dangling ⟨0, 3⟩ = none := by decide
example : loadRange NativeByteMemory.empty dangling ⟨1, 1⟩ = none := by decide
example : checkRange NativeByteMemory.empty dangling ⟨0, 1⟩ = true := by decide
example : checkRange NativeByteMemory.empty dangling ⟨1, 1⟩ = false := by decide
example : pointerAt ⟨⟨2 ^ 64 - 1, by decide⟩, none⟩ 1 = none := by decide
example : loadRange NativeByteMemory.empty ⟨⟨2 ^ 64 - 1, by decide⟩, none⟩ ⟨1, 1⟩ = none := by decide
example : loadRange NativeByteMemory.empty dangling ⟨2 ^ 63, 1⟩ = none := by decide

private def prepared : Option (Pointer × State) := do
  let (pointer, allocated) ← NativeByteMemory.allocate NativeByteMemory.empty base ⟨4, 1⟩
  let first ← NativeByteMemory.storeByte allocated pointer 10
  let next ← pointerAt pointer 1
  let second ← NativeByteMemory.storeByte first next 20
  let next ← pointerAt pointer 2
  let third ← NativeByteMemory.storeByte second next 30
  let next ← pointerAt pointer 3
  let fourth ← NativeByteMemory.storeByte third next 40
  pure (pointer, fourth)

example : (do
    let (p, state) ← prepared; loadRange state p ⟨4, 1⟩) = some [10, 20, 30, 40] := by decide
example : (do
    let (p, state) ← prepared; loadRange state p ⟨5, 1⟩) = none := by decide
example : (do
    let (p, state) ← prepared; let q ← pointerAt p 1; loadRange state q ⟨2, 1⟩) = some [20, 30] := by decide
example : (do
    let (p, state) ← prepared; let q ← pointerAt p 4; loadRange state q ⟨1, 1⟩) = none := by decide
example : (do
    let (p, state) ← prepared; let q ← pointerAt p 4; loadRange state q ⟨0, 1⟩) = some [] := by decide
example : (do
    let (p, state) ← prepared; loadRange state ⟨p.address, none⟩ ⟨4, 1⟩) = none := by decide
example : (do
    let (p, state) ← prepared; pure (checkRange state p ⟨4, 1⟩)) = some true := by decide

example : (do
    let (p, state) ← NativeByteMemory.allocate NativeByteMemory.empty base ⟨4, 1⟩;
    pure (checkRange state p ⟨4, 1⟩, loadRange state p ⟨4, 1⟩)) = some (true, none) := by decide

example : (do
    let (p, state) ← NativeByteMemory.allocate NativeByteMemory.empty base ⟨4, 1⟩;
    let written ← NativeByteMemory.storeByte state p 10; loadRange written p ⟨2, 1⟩) = none := by decide

private def adjacent : Option Bool := do
  let (p, first) ← NativeByteMemory.allocate NativeByteMemory.empty base ⟨2, 1⟩
  let (_, both) ← NativeByteMemory.allocate first ⟨66, by decide⟩ ⟨2, 1⟩
  pure (checkRange both p ⟨4, 1⟩)

example : adjacent = some false := by decide

private def afterFree (size : Nat) : Option (List Byte) := do
  let (p, state) ← prepared
  let released ← NativeByteMemory.deallocate state p ⟨4, 1⟩
  loadRange released p ⟨size, 1⟩

example : afterFree 4 = none := by decide
example : afterFree 0 = some [] := by decide

example : (do
    let (p, state) ← prepared;
    loadSlice state (⟨p, .slice ⟨4, by decide⟩⟩ :
      NativeRawPointer.RawPtr (List Byte) true)) = some [10, 20, 30, 40] := by decide

example : loadSlice NativeByteMemory.empty (⟨dangling, .thin⟩ : NativeRawPointer.RawPtr (List Byte) true) = none := by decide
example : loadSlice NativeByteMemory.empty (⟨dangling, .slice 0⟩ : NativeRawPointer.RawPtr (List Byte) true) = some [] := by decide
example : loadSlice NativeByteMemory.empty (⟨⟨0, none⟩, .slice 0⟩ : NativeRawPointer.RawPtr (List Byte) true) = none := by decide

end HasteBootsByteRangeSmoke
