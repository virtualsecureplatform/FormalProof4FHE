module
import all FormalProof4FHE.HasteBoots.NativePointerMachine

namespace HasteBootsPointerMachineSmoke
open FormalProof4FHE.HasteBoots
open NativePointerStorage (Address Pointer)
open NativePointerMachine (Op)

private def p : Address := ⟨64, by decide⟩
private def q : Address := ⟨128, by decide⟩
private def allocations : List Op := [.allocate p ⟨32, 8⟩, .allocate q ⟨8, 8⟩]
private def first (ops : List Op) : Option Pointer :=
  (NativePointerMachine.run NativePointerMachine.empty ops).bind (fun state => state.registers.head?)

example : first [.fromAddress q] = some ⟨q, none⟩ := by decide
example : first [.allocate p ⟨32, 8⟩] = some ⟨p, some ⟨64, 0⟩⟩ := by decide
example : first allocations = some ⟨q, some ⟨128, 1⟩⟩ := by decide
example : first (allocations ++ [.store 1 0, .load 1]) = some ⟨q, some ⟨128, 1⟩⟩ := by decide
example : first (allocations ++ [.fromAddress q, .withAddress 0 p]) = some ⟨p, none⟩ := by decide
example : first (allocations ++ [.withAddress 0 p]) = some ⟨p, some ⟨128, 1⟩⟩ := by decide
example : NativePointerMachine.run NativePointerMachine.empty
    (allocations ++ [.withAddress 0 p, .writeBytes 0 1 [99]]) = none := by decide
example : NativePointerMachine.run NativePointerMachine.empty
    (allocations ++ [.fromAddress q, .store 0 1]) = none := by decide
example : first (allocations ++ [.fromAddress q, .store 2 0, .load 2]) = some ⟨q, none⟩ := by decide
example : first (allocations ++ [.writeBytes 1 8 [128,0,0,0,0,0,0,0], .load 1]) = some ⟨q, none⟩ := by decide
example : first (allocations ++ [.store 1 0, .withAddress 1 ⟨72, by decide⟩, .copy 2 0 8 8, .load 0]) =
    some ⟨q, some ⟨128, 1⟩⟩ := by decide
example : first (allocations ++ [.store 1 0, .withAddress 1 ⟨72, by decide⟩, .copyNonoverlapping 2 0 8 8, .load 0]) =
    some ⟨q, some ⟨128, 1⟩⟩ := by decide
example : first (allocations ++ [.store 1 0, .copy 1 1 8 8, .load 1]) = some ⟨q, some ⟨128, 1⟩⟩ := by decide
example : NativePointerMachine.run NativePointerMachine.empty
    (allocations ++ [.copyNonoverlapping 1 1 8 8]) = none := by decide
example : NativePointerMachine.run NativePointerMachine.empty
    (allocations ++ [.copy 1 0 8 8, .load 0]) = none := by decide
example : NativePointerMachine.execute NativePointerMachine.empty (.withAddress 0 p) = none := by decide
example : NativePointerMachine.execute NativePointerMachine.empty (.load 0) = none := by decide
example : NativePointerMachine.run NativePointerMachine.empty [.allocate p ⟨32, 8⟩, .allocate ⟨72, by decide⟩ ⟨8, 8⟩] = none := by decide
example : NativePointerMachine.run NativePointerMachine.empty (allocations ++ [.free 0 ⟨7, 8⟩]) = none := by decide
example : NativePointerMachine.run NativePointerMachine.empty (allocations ++ [.free 0 ⟨8, 8⟩, .free 0 ⟨8, 8⟩]) = none := by decide
example : NativePointerMachine.run NativePointerMachine.empty
    (allocations ++ [.free 0 ⟨8, 8⟩, .allocate q ⟨8, 8⟩, .store 1 2]) = none := by decide
example : first (allocations ++ [.store 1 0, .free 0 ⟨8, 8⟩, .allocate q ⟨8, 8⟩, .load 2]) =
    some ⟨q, some ⟨128, 1⟩⟩ := by decide
example : (do
    let state ← NativePointerMachine.run NativePointerMachine.empty (allocations ++ [.free 0 ⟨8, 8⟩, .allocate q ⟨8, 8⟩])
    pure (state.history.map NativePointerMachine.Allocation.origin, state.heap.memory.nextGeneration)) =
    some ([⟨128, 2⟩, ⟨128, 1⟩, ⟨64, 0⟩], 3) := by decide
example : (do
    let state ← NativePointerMachine.run NativePointerMachine.empty (allocations ++ [.free 0 ⟨8, 8⟩])
    pure (state.history.length, state.heap.memory.nextGeneration)) = some (2, 2) := by decide

end HasteBootsPointerMachineSmoke
