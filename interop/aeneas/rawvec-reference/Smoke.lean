namespace HasteBootsRawVecReference.Smoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def world (cap : NativeWord64Memory.Word) : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 128 ⟨24,8⟩), .raw (.writeBytes 0 8
      (NativeWord64Memory.encode cap ++ NativeWord64Memory.encode 64 ++ NativeWord64Memory.encode 5)),
     .borrow 0 .shared ⟨24,8⟩]).getD NativeReferenceMachine.empty

example : (world 8).nextTag = 1 := by decide
example : (match invoke capacity (world 8) [.vectorSharedReference 0] with
    | .returned value next => (value,next.outputs.length,next.pointers.registers.length,
      next.pointers.heap == (world 8).pointers.heap)
    | _ => (.uninit,99,99,false)) = (.scalar (.usize 8),1,2,true) := by decide
example : (match invoke capacity (world 0) [.vectorSharedReference 0] with
    | .returned value _ => value | _ => .uninit) = .scalar (.usize 0) := by decide
example : (match invoke capacity (world ⟨2^63,by decide⟩) [.vectorSharedReference 0] with
    | .invalid next => (next.outputs.length,next.pointers.registers.length)
    | _ => (99,99)) = (1,2) := by decide
example : invoke capacity (world 8) [.vectorSharedReference 99] = .invalid (world 8) := by decide
example : invoke capacity (world 8) [.rawVecSharedReference 0] = .invalid (world 8) := by decide

end HasteBootsRawVecReference.Smoke
