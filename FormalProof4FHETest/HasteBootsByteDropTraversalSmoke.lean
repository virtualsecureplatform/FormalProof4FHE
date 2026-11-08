module
import FormalProof4FHE.HasteBoots.NativeByteDropTraversal

namespace FormalProof4FHETest.HasteBootsByteDropTraversalSmoke
open FormalProof4FHE.HasteBoots
open NativeByteSliceIndex

private def ready (length : Nat) (mode : NativeByteBorrow.Mode := .exclusive) : Option NativeReferenceMachine.State :=
  NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64, by decide⟩ ⟨8,8⟩), .raw (.writeBytes 0 8 (List.replicate 8 0)), .borrow 0 mode ⟨length,1⟩]
private def slice : Slice := ⟨⟨0⟩, ⟨3, by decide⟩⟩

example : (do
    let world ← ready 3
    pure (match index world slice ⟨2, by decide⟩ with
      | .value reference next => (reference.tag, next.nextTag, next.leases.length, next.pointers.registers.head?.map (fun p => p.address.val))
      | _ => (99,99,99,none))) = some (1,2,2,some 66) := by decide

example : (do
    let world ← ready 3
    pure ((index world slice ⟨3, by decide⟩) == .invalid world)) = some true := by decide

example : (do
    let world ← ready 3
    pure ((index world ⟨⟨0⟩,⟨4, by decide⟩⟩ ⟨2, by decide⟩) == .invalid world)) = some true := by decide

example : (do
    let world ← ready 3 .shared
    pure ((index world slice ⟨2, by decide⟩) == .invalid world)) = some true := by decide

example : (do
    let world ← ready 3
    pure ((index world ⟨⟨99⟩,⟨3, by decide⟩⟩ ⟨0, by decide⟩) == .invalid world)) = some true := by decide

example : (do
    let world ← ready 3
    let first := (index world slice ⟨2, by decide⟩).world
    pure (match index first slice ⟨2, by decide⟩ with
      | .invalid next => (next.nextTag, next.leases.length, next.pointers.registers.length,
          next.pointers.heap == first.pointers.heap)
      | _ => (99,99,99,false))) = some (2,2,3,true) := by decide

example : (do
    let world ← ready 3
    let next := (index world slice ⟨2, by decide⟩).world
    pure ((rawByte next ⟨1⟩).map (fun pointer => (pointer.address.val,
      pointer.provenance == world.pointers.registers[0]?.bind (fun p => p.provenance))))) = some (some (66,true)) := by decide

example : (do
    let world ← ready 3
    pure (rawByte world ⟨0⟩)) = some none := by decide

example : (do
    let world ← ready 0
    pure ((index world ⟨⟨0⟩,⟨0, by decide⟩⟩ ⟨0, by decide⟩) == .invalid world)) = some true := by decide

example : (do
    let world ← ready 3
    let result := NativeByteDropTraversal.run world slice
    pure (result.complete, result.cursor, result.last.map (fun pointer => pointer.address.val), result.world.nextTag)) =
    some (true,3,some 66,7) := by
  simp only [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom, slice]
  decide

example : (do
    let world ← ready 3
    let result := NativeByteDropTraversal.run world slice
    pure (result.world.leases.map NativeByteBorrow.Lease.tag, result.world.pointers.registers.length,
      result.world.pointers.heap == world.pointers.heap)) = some ([0],4,true) := by
  simp only [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom, slice]
  decide

example : (do
    let world ← ready 0
    let result := NativeByteDropTraversal.run world ⟨⟨0⟩,⟨0, by decide⟩⟩
    pure (result.complete, result.cursor, result.last, result.world == world)) = some (true,0,none,true) := by
  simp only [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom]
  decide

example : (do
    let world ← ready 3
    let indexed := (index world slice ⟨2, by decide⟩).world
    let result := NativeByteDropTraversal.run indexed slice
    pure (result.complete, result.cursor, result.world == indexed)) = some (false,0,true) := by
  simp only [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom, slice]
  decide

example : (do
    let world ← ready 3
    NativeReferenceMachine.execute (NativeByteDropTraversal.run world slice).world (.raw (.free 3 ⟨8,8⟩))) = none := by
  simp only [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom, slice]
  decide

example : (do
    let world ← ready 3
    let result := NativeByteDropTraversal.run world slice
    let final ← NativeReferenceMachine.run result.world [.endBorrow 6, .raw (.free 3 ⟨8,8⟩)]
    pure (final.pointers.heap.memory.blocks.length, final.nextTag)) = some (0,7) := by
  simp only [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom, slice]
  decide

end FormalProof4FHETest.HasteBootsByteDropTraversalSmoke
