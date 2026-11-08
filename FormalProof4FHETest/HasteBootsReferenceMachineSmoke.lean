module
import all FormalProof4FHE.HasteBoots.NativeReferenceMachine

namespace HasteBootsReferenceMachineSmoke
open FormalProof4FHE.HasteBoots
open NativePointerStorage (Address Pointer)
open NativeReferenceMachine (Op State)

private def p : Address := ⟨64, by decide⟩
private def q : Address := ⟨128, by decide⟩
private def pValue : Pointer := ⟨p, some ⟨64, 0⟩⟩
private def qValue : Pointer := ⟨q, some ⟨128, 1⟩⟩
private def setup : List Op := [.raw (.allocate p ⟨32, 8⟩), .raw (.allocate q ⟨8, 8⟩),
  .raw (.writeBytes 1 8 (List.replicate 32 0)), .raw (.store 1 0)]
private def exclusive8 : List Op := setup ++ [.borrow 1 .exclusive ⟨8, 8⟩]
private def shared8 : List Op := setup ++ [.borrow 1 .shared ⟨8, 8⟩]
private def child8 : List Op := setup ++ [.borrow 1 .exclusive ⟨16, 8⟩, .reborrow 0 1 .exclusive ⟨8, 8⟩]
private def finish (ops : List Op) : Option State := NativeReferenceMachine.run NativeReferenceMachine.empty ops
private def first (ops : List Op) : Option Pointer := (finish ops).bind (fun state => state.pointers.registers.head?)
private def output (ops : List Op) : Option (List NativeByteMemory.Byte) := (finish ops).bind (fun state => state.outputs.head?)

example : output (exclusive8 ++ [.access 0 0 (.read 8 8)]) = some [128,0,0,0,0,0,0,0] := by decide
example : first (exclusive8 ++ [.access 0 0 .loadPointer]) = some qValue := by decide
example : first (exclusive8 ++ [.access 0 0 (.storePointer 0), .access 0 0 .loadPointer]) = some qValue := by decide
example : first (exclusive8 ++ [.access 0 0 (.writeBytes 8 [128,0,0,0,0,0,0,0]), .access 0 0 .loadPointer]) = some ⟨q, none⟩ := by decide
example : (do
    let state ← finish (exclusive8 ++ [.access 0 2 (.writeBytes 1 [99])])
    NativeByteRange.loadRange state.pointers.heap.memory pValue ⟨8, 8⟩) = some [128,0,99,0,0,0,0,0] := by decide
example : (do
    let state ← finish (exclusive8 ++ [.access 0 2 (.writeBytes 1 [99])])
    NativePointerByteMemory.load state.pointers.heap pValue) = none := by decide
example : finish (exclusive8 ++ [.raw (.load 1)]) = none := by decide
example : finish (exclusive8 ++ [.raw (.writeBytes 1 1 [99])]) = none := by decide
example : finish (exclusive8 ++ [.raw (.store 1 0)]) = none := by decide
example : finish (exclusive8 ++ [.raw (.free 1 ⟨32, 8⟩)]) = none := by decide
example : finish (exclusive8 ++ [.raw (.copy 1 0 8 8)]) = none := by decide
example : first (shared8 ++ [.raw (.load 1)]) = some qValue := by decide
example : finish (shared8 ++ [.access 0 0 (.writeBytes 1 [99])]) = none := by decide
example : finish (shared8 ++ [.access 0 0 (.storePointer 0)]) = none := by decide
example : finish (shared8 ++ [.raw (.copy 0 1 8 8)]) = none := by decide
example : finish (shared8 ++ [.raw (.free 1 ⟨32, 8⟩)]) = none := by decide
example : (do
    let state ← finish (shared8 ++ [.borrow 1 .shared ⟨8, 8⟩])
    pure (state.references.map (fun reference => reference.tag), state.nextTag)) = some ([1,0], 2) := by decide
example : finish (shared8 ++ [.reborrow 0 1 .exclusive ⟨8, 8⟩]) = none := by decide
example : output (child8 ++ [.access 0 0 (.read 8 8)]) = some [128,0,0,0,0,0,0,0] := by decide
example : finish (child8 ++ [.access 1 0 (.read 8 8)]) = none := by decide
example : finish (child8 ++ [.endBorrow 1]) = none := by decide
example : output (child8 ++ [.endBorrow 0, .access 1 0 (.read 8 8)]) = some [128,0,0,0,0,0,0,0] := by decide
example : finish (child8 ++ [.endBorrow 0, .access 0 0 (.read 8 8)]) = none := by decide
example : finish (child8 ++ [.endBorrow 0, .reborrow 1 1 .exclusive ⟨8, 8⟩, .access 1 0 (.read 8 8)]) = none := by decide
example : (do
    let state ← finish (child8 ++ [.endBorrow 0, .reborrow 1 1 .exclusive ⟨8, 8⟩])
    pure (state.references.map (fun reference => reference.tag), state.births.map (fun birth => birth.tag), state.nextTag)) =
    some ([2,1,0], [2,1,0], 3) := by decide
example : output (child8 ++ [.access 1 8 (.writeBytes 8 [1,2,3,4,5,6,7,8]), .access 1 8 (.read 8 8)]) =
    some [1,2,3,4,5,6,7,8] := by decide
example : finish (exclusive8 ++ [.endBorrow 0, .endBorrow 0]) = none := by decide
example : (do
    let state ← finish (exclusive8 ++ [.endBorrow 0, .raw (.free 1 ⟨32, 8⟩)])
    pure state.pointers.heap.memory.blocks.length) = some 1 := by decide
example : finish (exclusive8 ++ [.endBorrow 0, .raw (.free 1 ⟨32, 8⟩), .access 0 0 (.read 1 1)]) = none := by decide
example : finish (setup ++ [.borrow 0 .exclusive ⟨8, 8⟩]) = none := by decide
example : finish (exclusive8 ++ [.reborrow 0 0 .shared ⟨8, 8⟩]) = none := by decide
example : finish (exclusive8 ++ [.raw (.withAddress 1 ⟨72, by decide⟩), .reborrow 0 0 .exclusive ⟨8, 8⟩]) = none := by decide
example : finish (exclusive8 ++ [.access 0 8 (.read 1 1)]) = none := by decide
example : finish (setup ++ [.borrow 1 .exclusive ⟨16, 8⟩, .access 0 1 .loadPointer]) = none := by decide
example : finish (setup ++ [.access 0 0 (.read 1 1)]) = none := by decide
example : output (exclusive8 ++ [.raw (.fromAddress p), .access 0 0 (.read 8 8)]) = some [128,0,0,0,0,0,0,0] := by decide

end HasteBootsReferenceMachineSmoke
