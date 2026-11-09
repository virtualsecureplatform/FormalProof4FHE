namespace HasteBootsRawVecFields.Smoke
open FormalProof4FHE.HasteBoots

private def world : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,8⟩), .raw (.allocate 128 ⟨16,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)),
     .raw (.withAddress 0 136), .raw (.store 0 2), .borrow 1 .shared ⟨16,8⟩]).getD NativeReferenceMachine.empty

example : (match capacityRead world 0 with | .value value _ => value.val | _ => 99) = 8 := by decide
example : (match pointerRead world 0 with | .value value _ => value | _ => ⟨0,none⟩) =
    ⟨64,some ⟨64,0⟩⟩ := by decide
example : (match capacityRead world 0 with
    | .value _ next => (next.outputs.length,next.pointers.heap == world.pointers.heap)
    | _ => (99,false)) = (1,true) := by decide
example : capacityRead world 1 = .invalid world := by decide
example : pointerRead world 1 = .invalid world := by decide

end HasteBootsRawVecFields.Smoke
