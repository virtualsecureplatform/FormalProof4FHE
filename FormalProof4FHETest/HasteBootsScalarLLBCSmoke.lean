module
import all FormalProof4FHE.HasteBoots.NativeScalarLLBC

namespace HasteBootsScalarLLBCSmoke
open FormalProof4FHE.HasteBoots
open NativeScalarLLBC
open NativePointerStorage (Pointer)

private def p : Pointer := ⟨⟨64, by decide⟩, some ⟨64, 0⟩⟩
private def invalid : Pointer := ⟨⟨0, by decide⟩, none⟩
private def allocated : NativePointerByteMemory.State :=
  ⟨⟨1, [⟨⟨64,0⟩, ⟨64, by decide⟩, ⟨8,8⟩, List.replicate 8 none⟩]⟩, []⟩
private def writeFail : Function := ⟨"write_then_invalid_read", [.unit, .ptr true .word, .word, .ptr false .word, .word], 3,
  .storageLive 0 (.assign (.var 0) .unit (.assign (.deref 1 .word) (.use (.move 2))
    (.storageLive 4 (.assign (.var 4) (.use (.copy (.deref 3 .word))) .ret))))⟩
private def writeUnwind : Body := .storageLive 0 (.assign (.var 0) .unit (.assign (.deref 1 .word) (.use (.move 2)) .resume))
private def unwindCaller : Function := ⟨"write_then_unwind", [.unit, .ptr true .word, .word], 2,
  .storageLive 0 (.call "retained_callee" [.unit, .ptr true .word, .word] 2 (.var 0) [.copy (.var 1), .move 2]
    writeUnwind (.storageDead 1 .resume) .ret)⟩
private def moved : Function := ⟨"moved_value", [.word, .word], 1,
  .storageLive 0 (.assign (.var 0) (.use (.move 1)) (.assign (.var 0) (.use (.copy (.var 1))) .ret))⟩
private def dead : Function := ⟨"dead_value", [.word, .word], 1,
  .storageLive 0 (.storageDead 1 (.assign (.var 0) (.use (.copy (.var 1))) .ret))⟩
private def noLive : Function := ⟨"dead_destination", [.word, .word], 1, .assign (.var 0) (.use (.copy (.var 1))) .ret⟩

example : (invoke writeFail allocated [.pointer p, .word ⟨77, by decide⟩, .pointer invalid]).heap.memory.nextGeneration = 1 := by decide
example : NativeWord64Memory.load (invoke writeFail allocated [.pointer p, .word ⟨77, by decide⟩, .pointer invalid]).heap.memory p =
    some ⟨77, by decide⟩ := by decide
example : (match invoke writeFail allocated [.pointer p, .word ⟨77, by decide⟩, .pointer invalid] with | .invalid _ => true | _ => false) = true := by decide
example : NativeWord64Memory.load (invoke unwindCaller allocated [.pointer p, .word ⟨88, by decide⟩]).heap.memory p = some ⟨88, by decide⟩ := by decide
example : (match invoke unwindCaller allocated [.pointer p, .word ⟨88, by decide⟩] with | .unwind _ => true | _ => false) = true := by decide
example : invoke moved allocated [.word ⟨7, by decide⟩] = .invalid allocated := by decide
example : invoke dead allocated [.word ⟨7, by decide⟩] = .invalid allocated := by decide
example : invoke noLive allocated [.word ⟨7, by decide⟩] = .invalid allocated := by decide
example : invoke moved allocated [] = .invalid allocated := by decide
example : invoke moved allocated [.pointer p] = .invalid allocated := by decide

end HasteBootsScalarLLBCSmoke
