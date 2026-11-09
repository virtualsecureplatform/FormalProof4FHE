namespace HasteBootsRawVecCurrentMemory.Smoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def world (cap : NativeWord64Memory.Word) (address : NativePointerStorage.Address := 64) : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,8⟩), .raw (.allocate 128 ⟨16,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode cap)), .raw (.withAddress 0 136),
     .raw (.fromAddress address), .raw (.store 1 0), .borrow 2 .shared ⟨16,8⟩]).getD NativeReferenceMachine.empty

example : (world 8).nextTag = 1 := by decide
example : (match invoke f8 (world 8) [.rawVecSharedReference 0,layoutInput 0 1] with
    | .returned value next => (value,next == world 8) | _ => (.uninit,false)) = (noneValue,true) := by decide
example : (match invoke f8 (world 0 0) [.rawVecSharedReference 0,layoutInput 1 1] with
    | .returned value next => (value,next.outputs.length,next.pointers.registers.length)
    | _ => (.uninit,99,99)) = (noneValue,1,5) := by decide
example : (match invoke f8 (world 8) [.rawVecSharedReference 0,layoutInput 1 1] with
    | .returned value next => (value,next.outputs.length,next.pointers.registers.length,
      next.pointers.heap == (world 8).pointers.heap)
    | _ => (.uninit,99,99,false)) = (someValue ⟨64,none⟩ 8 1,3,9,true) := by decide
example : (match invoke f8 (world 8) [.rawVecSharedReference 0,layoutInput 3 4] with
    | .returned value _ => value | _ => .uninit) = someValue ⟨64,none⟩ 24 4 := by decide
example : (match invoke f8 (world 8 0) [.rawVecSharedReference 0,layoutInput 1 1] with
    | .invalid next => (next.outputs.length,next.pointers.registers.length)
    | _ => (99,99)) = (2,8) := by decide
example : (match invoke f8 (world ⟨2^63,by decide⟩) [.rawVecSharedReference 0,layoutInput 1 1] with
    | .invalid next => (next.outputs.length,next.pointers.registers.length)
    | _ => (99,99)) = (1,5) := by decide
example : (match invoke f8 (world 8) [.rawVecSharedReference 0,layoutInput ⟨2^64-1,by decide⟩ 1] with
    | .invalid next => (next.outputs.length,next.pointers.registers.length)
    | _ => (99,99)) = (2,6) := by decide
example : invoke f8 (world 8) [.rawVecSharedReference 99,layoutInput 1 1] = .invalid (world 8) := by decide
example : invoke f8 (world 8) [.rawVecSharedReference 0,layoutInput 1 3] = .invalid (world 8) := by decide

private def issued : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,8⟩), .raw (.allocate 128 ⟨16,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)), .raw (.withAddress 0 136),
     .raw (.store 0 2), .borrow 1 .shared ⟨16,8⟩]).getD NativeReferenceMachine.empty
example : issued.nextTag = 1 := by decide
example : (match invoke f8 issued [.rawVecSharedReference 0,layoutInput 1 1] with
    | .returned value _ => value | _ => .uninit) = someValue ⟨64,some ⟨64,0⟩⟩ 8 1 := by decide
private def reused : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run issued [.raw (.free 2 ⟨8,8⟩),.raw (.allocate 64 ⟨8,8⟩)]).getD NativeReferenceMachine.empty
example : reused.pointers.registers[0]? = some ⟨64,some ⟨64,2⟩⟩ := by decide
example : (match invoke f8 reused [.rawVecSharedReference 0,layoutInput 1 1] with
    | .returned value _ => value | _ => .uninit) = someValue ⟨64,some ⟨64,0⟩⟩ 8 1 := by decide

end HasteBootsRawVecCurrentMemory.Smoke
