namespace HasteBootsAllocatorCallerSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC HasteBootsAllocatorCaller

private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64,by decide⟩ ⟨8,8⟩),.raw (.writeBytes 0 8 (List.replicate 8 0))]).getD NativeReferenceMachine.empty

example : (match invoke f2 ready (inputs 0 ⟨8,by decide⟩ ⟨8,by decide⟩) with
    | .returned (.scalar .unit) world =>
      (world.pointers.heap.memory.blocks.length, world.pointers.history == ready.pointers.history,
       world.pointers.heap.memory.nextGeneration,world.nextTag)
    | _ => (99,false,99,99)) = (0,true,1,0) := by decide

example : invoke f2 ready (inputs 0 ⟨7,by decide⟩ ⟨8,by decide⟩) = .invalid ready := by decide
example : invoke f2 ready (inputs 0 ⟨8,by decide⟩ ⟨3,by decide⟩) = .invalid ready := by decide
example : invoke f2 ready (inputs 99 ⟨8,by decide⟩ ⟨8,by decide⟩) = .invalid ready := by decide
example : invoke f2 ready (inputs 0 ⟨0,by decide⟩ ⟨8,by decide⟩) = .invalid ready := by decide

private def borrowed : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute ready (.borrow 0 .exclusive ⟨8,8⟩)).getD ready
example : invoke f2 borrowed (inputs 0 ⟨8,by decide⟩ ⟨8,by decide⟩) = .invalid borrowed := by decide

example : (match invoke f2 ready (inputs 0 ⟨8,by decide⟩ ⟨8,by decide⟩) with
    | .returned (.scalar .unit) world => invoke f2 world (inputs 0 ⟨8,by decide⟩ ⟨8,by decide⟩) == .invalid world
    | _ => false) = true := by decide

example : (do
    let bare ← NativeReferenceMachine.execute ready (.raw (.fromAddress ⟨64,by decide⟩))
    pure (invoke f2 bare (inputs 0 ⟨8,by decide⟩ ⟨8,by decide⟩) == .invalid bare)) = some true := by decide

end HasteBootsAllocatorCallerSmoke
