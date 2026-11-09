namespace HasteBootsRawVecDrop.Smoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def world (cap : NativeWord64Memory.Word) : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.allocate 128 ⟨16,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode cap)),.raw (.withAddress 0 136),
     .raw (.store 0 2),.borrow 1 .exclusive ⟨16,8⟩]).getD NativeReferenceMachine.empty

example : (world 8).nextTag = 1 := by decide
example : (match invoke f4 (world 8) [.rawVecExclusiveReference 0] with
    | .returned (.scalar .unit) next => (next.pointers.heap.memory.blocks.length,next.nextTag,
      next.leases.map NativeByteBorrow.Lease.tag,next.outputs.length,next.births.length)
    | _ => (99,99,[],99,99)) = (1,5,[0],3,5) := by decide
example : (match invoke f5 (world 8) [.rawVecExclusiveReference 0] with
    | .returned (.scalar .unit) next => (next.pointers.heap.memory.blocks.length,next.nextTag,
      next.leases.map NativeByteBorrow.Lease.tag,next.outputs.length)
    | _ => (99,99,[],99)) = (1,4,[0],3) := by decide
example : (match invoke f4 (world 0) [.rawVecExclusiveReference 0] with
    | .returned (.scalar .unit) next => (next.pointers.heap == (world 0).pointers.heap,next.nextTag,
      next.leases.map NativeByteBorrow.Lease.tag,next.outputs.length)
    | _ => (false,99,[],99)) = (true,4,[0],1) := by decide
example : invoke f4 (world 8) [.rawVecSharedReference 0] = .invalid (world 8) := by decide
example : invoke f4 (world 8) [.rawVecExclusiveReference 99] = .invalid (world 8) := by decide
example : (match invoke f4 (world ⟨2^63,by decide⟩) [.rawVecExclusiveReference 0] with
    | .invalid next => (next.pointers.heap == (world ⟨2^63,by decide⟩).pointers.heap,next.nextTag,next.outputs.length)
    | _ => (false,99,99)) = (true,4,1) := by decide
private def afterFree : NativeReferenceMachine.State :=
  match invoke f4 (world 8) [.rawVecExclusiveReference 0] with
  | .returned (.scalar .unit) next => next
  | _ => NativeReferenceMachine.empty
example : afterFree.pointers.heap.memory.blocks.length = 1 ∧ afterFree.nextTag = 5 := by decide
example : (match invoke f4 afterFree [.rawVecExclusiveReference 4] with
    | .invalid next => (next.pointers.heap == afterFree.pointers.heap,next.nextTag)
    | _ => (false,99)) = (true,9) := by decide
private def reused : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute afterFree (.raw (.allocate 64 ⟨8,1⟩))).getD NativeReferenceMachine.empty
example : (match invoke f4 reused [.rawVecExclusiveReference 4] with
    | .invalid next => (next.pointers.heap == reused.pointers.heap,next.nextTag)
    | _ => (false,99)) = (true,9) := by decide
private def blocked : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute (world 8) (.reborrow 0 1 .shared ⟨16,8⟩)).getD NativeReferenceMachine.empty
example : (match invoke f4 blocked [.rawVecExclusiveReference 1] with
    | .invalid next => (next.nextTag,next.pointers.heap == blocked.pointers.heap)
    | _ => (99,false)) = (2,true) := by decide
end HasteBootsRawVecDrop.Smoke
