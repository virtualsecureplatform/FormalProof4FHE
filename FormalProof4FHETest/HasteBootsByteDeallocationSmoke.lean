module
import FormalProof4FHE.HasteBoots.NativeByteDropCalls

namespace FormalProof4FHETest.HasteBootsByteDeallocationSmoke
open FormalProof4FHE.HasteBoots
open NativeSliceLLBC (Frame Flow Value)

private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64, by decide⟩ ⟨8,8⟩), .raw (.allocate ⟨128, by decide⟩ ⟨8,8⟩),
     .raw (.store 1 0), .raw (.store 0 1)]).getD NativeReferenceMachine.empty

private def frame (world : NativeReferenceMachine.State) (register size alignment : Nat) : Frame :=
  ⟨[.unit,.raw false,.usize,.usize],
   [.dead,.live (NativeSliceLLBC.decodeInput world (.rawRegister register)),
    .live (some (.usize ⟨size % 2^64, Nat.mod_lt _ (by decide)⟩)),
    .live (some (.usize ⟨alignment % 2^64, Nat.mod_lt _ (by decide)⟩))],world⟩

private def free (world : NativeReferenceMachine.State) (register size alignment : Nat) : Flow :=
  NativeByteDeallocation.eval (frame world register size alignment) [.move 1,.move 2,.move 3]

private def borrowed (register : Nat) : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute ready (.borrow register .exclusive ⟨8,8⟩)).getD ready

example : (match free ready 0 8 8 with
    | .returned .unit world => (world.pointers.heap.memory.blocks.length,
        world.pointers.registers == ready.pointers.registers, world.pointers.history == ready.pointers.history,
        world.pointers.heap.memory.nextGeneration)
    | _ => (99,false,false,99)) = (1,true,true,2) := by decide

-- The allocation owning slot 128 loses its shadow cells. Slot 64 retains its
-- stored dangling pointer to 128, whose origin cannot be reassigned by reuse.
example : (match free ready 0 8 8 with
    | .returned .unit world =>
      (world.pointers.heap.shadow.map (fun cell => cell.owner.allocation),
       NativePointerByteMemory.load world.pointers.heap ⟨⟨64,by decide⟩,some ⟨64,0⟩⟩,
       NativeByteMemory.loadByte world.pointers.heap.memory ⟨⟨128,by decide⟩,some ⟨128,1⟩⟩)
    | _ => ([],none,some 0)) =
    (List.replicate 8 64,some ⟨⟨128,by decide⟩,some ⟨128,1⟩⟩,none) := by decide

example : free ready 0 7 8 = .invalid ready := by decide
example : free ready 0 8 1 = .invalid ready := by decide
example : free ready 0 8 3 = .invalid ready := by decide
example : free ready 0 0 8 = .invalid ready := by decide
example : free ready 99 8 8 = .invalid ready := by decide
example : free (borrowed 0) 0 8 8 = .invalid (borrowed 0) := by decide

example : (match free (borrowed 1) 0 8 8 with
    | .returned .unit world => (world.pointers.heap.memory.blocks.length,world.leases == (borrowed 1).leases)
    | _ => (99,false)) = (1,true) := by decide

example : (do
    let ended ← NativeReferenceMachine.execute (borrowed 0) (.endBorrow 0)
    pure (match free ended 0 8 8 with | .returned .unit _ => true | _ => false)) = some true := by decide

example : (do
    let bare ← NativeReferenceMachine.execute ready (.raw (.fromAddress ⟨128, by decide⟩))
    pure (free bare 0 8 8 == .invalid bare)) = some true := by decide

example : (match free ready 0 8 8 with
    | .returned .unit world => free world 0 8 8 == .invalid world
    | _ => false) = true := by decide

example : (match free ready 0 8 8 with
    | .returned .unit world => do
      let reused ← NativeReferenceMachine.execute world (.raw (.allocate ⟨128, by decide⟩ ⟨8,8⟩))
      pure (free reused 1 8 8 == .invalid reused, reused.pointers.heap.memory.nextGeneration,
        reused.pointers.history.length)
    | _ => none) = some (true,3,3) := by decide

example : NativeByteDeallocation.execute ready
    ⟨⟨⟨128,by decide⟩,some ⟨128,1⟩⟩,some ⟨8,by decide⟩⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ = none := by decide

example : NativeByteDeallocation.execute ready
    ⟨⟨⟨128,by decide⟩,some ⟨128,99⟩⟩,none⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ = none := by decide

example : (match NativeByteDropCalls.resumeCall ready (frame ready 0 8 8) 99 (free ready 0 8 8) with
    | .invalid world => world.pointers.heap.memory.blocks.length
    | _ => 99) = 1 := by decide

end FormalProof4FHETest.HasteBootsByteDeallocationSmoke
