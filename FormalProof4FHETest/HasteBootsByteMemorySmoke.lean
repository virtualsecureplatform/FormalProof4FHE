module
import all FormalProof4FHE.HasteBoots.NativeByteMemory

namespace HasteBootsByteMemorySmoke
open FormalProof4FHE.HasteBoots
open NativeByteMemory
open NativePointerStorage (Address Pointer)

private def base : Address := ⟨64, by decide⟩
private def layout : Layout := ⟨4, 4⟩
private def block : Block := freshBlock empty base layout
private def live : State := ⟨1, [block]⟩
private def pointer : Pointer := block.pointer

example : allocate empty base layout = some (pointer, live) := by decide
example : loadByte live pointer = none := by decide
example : loadByte live ⟨base, none⟩ = none := by decide
example : storeByte live ⟨base, none⟩ 42 = none := by decide
example : allocate empty 0 layout = none := by decide
example : allocate empty base ⟨0, 4⟩ = none := by decide
example : allocate empty base ⟨4, 0⟩ = none := by decide
example : allocate empty base ⟨4, 3⟩ = none := by decide
example : allocate empty ⟨65, by decide⟩ layout = none := by decide
example : allocate empty ⟨2 ^ 64 - 4, by decide⟩ ⟨8, 4⟩ = none := by decide
example : allocate empty base ⟨2 ^ 63, 4⟩ = none := by decide
example : allocate live base layout = none := by decide
example : allocate live ⟨66, by decide⟩ ⟨4, 2⟩ = none := by decide
example : loadByte live ⟨⟨68, by decide⟩, pointer.provenance⟩ = none := by decide
example : storeByte live ⟨⟨68, by decide⟩, pointer.provenance⟩ 42 = none := by decide
example : deallocate live ⟨⟨65, by decide⟩, pointer.provenance⟩ layout = none := by decide
example : deallocate live pointer ⟨3, 4⟩ = none := by decide
example : deallocate live pointer ⟨4, 2⟩ = none := by decide
example : deallocate live pointer layout = some ⟨1, []⟩ := by decide

private def roundtrip : Option (Byte × State × Option Byte) := do
  let (p, allocated) ← allocate empty base layout
  let written ← storeByte allocated p 42
  let byte ← loadByte written p
  let released ← deallocate written p layout
  pure (byte, released, loadByte released p)

example : roundtrip = some (42, ⟨1, []⟩, none) := by decide

private def reused : Option (Bool × Option Byte × Option Byte) := do
  let (old, allocated) ← allocate empty base layout
  let written ← storeByte allocated old 42
  let released ← deallocate written old layout
  let (fresh, allocatedAgain) ← allocate released base layout
  let writtenAgain ← storeByte allocatedAgain fresh 27
  pure (decide (old.provenance ≠ fresh.provenance), loadByte writtenAgain old, loadByte writtenAgain fresh)

example : reused = some (true, none, some 27) := by decide

private def neighbors : Option (Option Byte × Option Byte) := do
  let (first, allocated) ← allocate empty base layout
  let written ← storeByte allocated first 42
  let (second, extended) ← allocate written ⟨68, by decide⟩ layout
  let writtenSecond ← storeByte extended second 27
  pure (loadByte writtenSecond first, loadByte writtenSecond second)

example : neighbors = some (some 42, some 27) := by decide

end HasteBootsByteMemorySmoke
