namespace HasteBootsLayoutStorageSmoke
open FormalProof4FHE.HasteBoots
open NativeLayoutBytes (Words)
open HasteBootsLayoutStorage

private def value : Words := ⟨⟨24,by decide⟩,⟨8,by decide⟩⟩
private def ready (bytes : List NativeByteMemory.Byte) : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64,by decide⟩ ⟨16,8⟩),.raw (.writeBytes 0 8 bytes),
     .raw (.allocate ⟨128,by decide⟩ ⟨24,8⟩),.borrow 1 .shared ⟨16,8⟩]).getD NativeReferenceMachine.empty

-- The read inserts a scratch pointer at register 0; the data pointer was
-- captured beforehand, so the distinct 24-byte allocation is still freed.
example : (match call (ready (NativeLayoutBytes.encode value)) 0 0 with
    | .returned (.scalar .unit) world =>
      (world.pointers.heap.memory.blocks.map (fun block => block.layout.size),
       world.outputs,world.pointers.registers.length,world.pointers.history.length,
       world.leases.map NativeByteBorrow.Lease.tag)
    | _ => ([],[],99,99,[])) = ([16],[NativeLayoutBytes.encode value],3,2,[0]) := by decide

example : call (ready (NativeLayoutBytes.encode value)) 99 0 =
    .invalid (ready (NativeLayoutBytes.encode value)) := by decide
example : call (ready (NativeLayoutBytes.encode value)) 0 99 =
    .invalid (ready (NativeLayoutBytes.encode value)) := by decide

example : (match call (ready (NativeLayoutBytes.encode ⟨⟨16,by decide⟩,⟨8,by decide⟩⟩)) 0 0 with
    | .invalid world => (world.pointers.heap.memory.blocks.length,world.outputs.length,world.pointers.registers.length)
    | _ => (99,99,99)) = (2,1,3) := by decide

example : (match call (ready (NativeLayoutBytes.encode ⟨⟨24,by decide⟩,⟨3,by decide⟩⟩)) 0 0 with
    | .invalid world => (world.pointers.heap.memory.blocks.length,world.outputs.length,world.pointers.registers.length)
    | _ => (99,99,99)) = (2,1,3) := by decide

example : (match call (ready (NativeWord64Memory.encode value.size ++ NativeWord64Memory.encode value.alignment)) 0 0 with
    | .invalid world => world.pointers.heap.memory.blocks.length
    | _ => 99) = 2 := by decide

example : (do
    let ended ← NativeReferenceMachine.execute (ready (NativeLayoutBytes.encode value)) (.endBorrow 0)
    pure (call ended 0 0 == .invalid ended)) = some true := by decide

example : (do
    let bare ← NativeReferenceMachine.execute (ready (NativeLayoutBytes.encode value)) (.raw (.fromAddress ⟨128,by decide⟩))
    pure (match call bare 0 0 with
      | .invalid world => (world.pointers.heap.memory.blocks.length,world.outputs.length)
      | _ => (99,99))) = some (2,1) := by decide

end HasteBootsLayoutStorageSmoke
