module
import FormalProof4FHE.HasteBoots.NativeByteLoopLLBC

namespace FormalProof4FHETest.HasteBootsByteLoopLLBCSmoke
open FormalProof4FHE.HasteBoots
open NativeByteLoopLLBC

private def ready (mode : NativeByteBorrow.Mode := .exclusive) : Option NativeReferenceMachine.State :=
  NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64, by decide⟩ ⟨8,8⟩), .raw (.writeBytes 0 8 (List.replicate 8 0)), .borrow 0 mode ⟨3,1⟩]
private def frame (world : NativeReferenceMachine.State) : Frame :=
  ⟨[.unit,.sliceRef,.usize,.usize,.rawByte,.boolean,.sliceRef,.byteRef],
    [.live (some .unit),.live (some (.sliceRef ⟨⟨0⟩,⟨3, by decide⟩⟩)),.live (some (.usize ⟨3, by decide⟩)),
      .live (some (.usize ⟨0, by decide⟩)),.live none,.live none,
      .live (some (.sliceRef ⟨⟨0⟩,⟨3, by decide⟩⟩)),.live none],world⟩

example : (do
    let world ← ready
    let changed ← storageLive (frame world) 6
    pure (readLocal changed 6, changed.world == world)) = some (none,true) := by decide

example : (do
    let world ← ready
    let once ← storageDead (frame world) 7
    let twice ← storageDead once 7
    pure (twice == once, twice.world.leases.length)) = some (true,1) := by decide

example : (do
    let world ← ready
    let start := frame world
    pure (evalOperand start (.metadata 1) == some (.usize ⟨3, by decide⟩,start))) = some true := by decide

example : (do
    let world ← ready
    evalOperand (frame world) (.copy 1)) = none := by decide

example : (do
    let world ← ready
    pure (evalRvalue (frame world) (.eq (.copy 3) (.copy 2)) == .value (.boolean false) (frame world))) = some true := by decide

example : (do
    let world ← ready
    pure (evalRvalue (frame world) (.addWrap (.literal ⟨2^64-1, by decide⟩) (.literal ⟨1, by decide⟩)) ==
      .value (.usize ⟨0, by decide⟩) (frame world))) = some true := by decide

example : (do
    let world ← ready
    pure (match evalIndex (frame world) 7 (.move 6) (.literal ⟨3, by decide⟩) with
      | .unwind changed => (readLocal changed 6, changed.world == world)
      | _ => (some .unit,false))) = some (none,true) := by decide

example : (do
    let world ← ready
    pure (match eval (.index 7 (.move 6) (.literal ⟨3, by decide⟩)
        (.storageDead 7 (.storageDead 6 .abort)) .done) (frame world) with
      | .invalid changed => (changed.slots[6]?,changed.slots[7]?,changed.world == world)
      | _ => (none,none,false))) = some (some .dead,some .dead,true) := by decide

example : (do
    let world ← ready
    pure (match evalIndex (frame world) 7 (.move 6) (.literal ⟨1, by decide⟩) with
      | .next changed => (changed.world.nextTag, readLocal changed 6, readLocal changed 7)
      | _ => (99,none,none))) = some (2,none,some (.byteRef ⟨1⟩)) := by decide

example : (do
    let world ← ready
    let first := (evalIndex (frame world) 7 (.move 6) (.literal ⟨1, by decide⟩)).frame
    pure (match evalIndex (frame first.world) 7 (.move 6) (.literal ⟨1, by decide⟩) with
      | .invalid changed => (changed.world.nextTag, changed.world.pointers.registers.length,
          readLocal changed 6, changed.world.pointers.heap == world.pointers.heap)
      | _ => (99,99,some .unit,false))) = some (2,3,none,true) := by decide

example : (do
    let world ← ready
    pure (decodeSlice world 0, decodeSlice world 99)) = some (some ⟨⟨0⟩,⟨3, by decide⟩⟩,none) := by decide

example : (do
    let world ← ready .shared
    decodeSlice world 0) = none := by decide

example : (do
    let world ← ready
    pure (match eval (.branch (.copy 2) .ret .ret .done) (frame world) with
      | .invalid changed => changed == frame world
      | _ => false)) = some true := by decide

end FormalProof4FHETest.HasteBootsByteLoopLLBCSmoke
