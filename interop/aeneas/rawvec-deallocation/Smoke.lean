namespace HasteBootsRawVecDeallocation.Smoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def world (cap : NativeWord64Memory.Word) : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.allocate 128 ⟨16,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode cap)),.raw (.withAddress 0 136),
     .raw (.store 0 2),.borrow 1 .exclusive ⟨16,8⟩]).getD NativeReferenceMachine.empty

example : (world 8).nextTag = 1 := by decide
example : (match invoke f7 (world 8) [.rawVecExclusiveReference 0,layoutInput 1 1] with
    | .returned (.scalar .unit) next => (next.pointers.heap.memory.blocks.length,next.nextTag,
      next.leases.map NativeByteBorrow.Lease.tag,next.outputs.length,next.births.length,
      next.pointers.history == (world 8).pointers.history)
    | _ => (99,99,[],99,99,false)) = (1,3,[0],3,3,true) := by decide
example : (match invoke f7 (world 0) [.rawVecExclusiveReference 0,layoutInput 1 1] with
    | .returned (.scalar .unit) next => (next.pointers.heap == (world 0).pointers.heap,next.nextTag,
      next.leases.map NativeByteBorrow.Lease.tag,next.outputs.length)
    | _ => (false,99,[],99)) = (true,2,[0],1) := by decide
example : (match invoke f7 (world 8) [.rawVecExclusiveReference 0,layoutInput 0 1] with
    | .returned (.scalar .unit) next => (next.pointers.heap == (world 8).pointers.heap,next.nextTag,
      next.leases.map NativeByteBorrow.Lease.tag,next.outputs.length)
    | _ => (false,99,[],99)) = (true,2,[0],0) := by decide
example : (match invoke f7 (world 8) [.rawVecExclusiveReference 0,layoutInput 1 2] with
    | .invalid next => (next.pointers.heap == (world 8).pointers.heap,next.nextTag,next.outputs.length)
    | _ => (false,99,99)) = (true,3,3) := by decide
example : invoke f7 (world 8) [.rawVecSharedReference 0,layoutInput 1 1] = .invalid (world 8) := by decide
example : invoke f7 (world 8) [.rawVecExclusiveReference 99,layoutInput 1 1] = .invalid (world 8) := by decide
example : invoke f7 (world 8) [.rawVecExclusiveReference 0,layoutInput 1 3] = .invalid (world 8) := by decide

example : (match invoke f7 (world ⟨2^63,by decide⟩) [.rawVecExclusiveReference 0,layoutInput 1 1] with
    | .invalid next => (next.pointers.heap == (world ⟨2^63,by decide⟩).pointers.heap,next.nextTag,next.outputs.length)
    | _ => (false,99,99)) = (true,2,1) := by decide
private def afterFree : NativeReferenceMachine.State :=
  match invoke f7 (world 8) [.rawVecExclusiveReference 0,layoutInput 1 1] with
  | .returned (.scalar .unit) next => next
  | _ => NativeReferenceMachine.empty
example : afterFree.pointers.heap.memory.blocks.length = 1 ∧ afterFree.nextTag = 3 := by decide
example : (match invoke f7 afterFree [.rawVecExclusiveReference 2,layoutInput 1 1] with
    | .invalid next => (next.pointers.heap == afterFree.pointers.heap,next.nextTag)
    | _ => (false,99)) = (true,5) := by decide
private def reused : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute afterFree (.raw (.allocate 64 ⟨8,1⟩))).getD NativeReferenceMachine.empty
example : reused.pointers.registers[0]? = some ⟨64,some ⟨64,2⟩⟩ := by decide
example : (match invoke f7 reused [.rawVecExclusiveReference 2,layoutInput 1 1] with
    | .invalid next => (next.pointers.heap == reused.pointers.heap,next.pointers.heap.memory.blocks.length,next.nextTag)
    | _ => (false,99,99)) = (true,2,5) := by decide
private def leased : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run (world 8)
    [.raw (.writeBytes 2 1 (List.replicate 8 0)),.borrow 2 .shared ⟨8,1⟩]).getD NativeReferenceMachine.empty
example : leased.nextTag = 2 := by decide
example : (match invoke f7 leased [.rawVecExclusiveReference 1,layoutInput 1 1] with
    | .invalid next => (next.pointers.heap == leased.pointers.heap,next.nextTag,next.outputs.length)
    | _ => (false,99,99)) = (true,4,3) := by decide

end HasteBootsRawVecDeallocation.Smoke
