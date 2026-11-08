namespace HasteBootsGlobalDeallocationSmoke
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC HasteBootsGlobalDeallocation

private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.fromAddress ⟨1,by decide⟩),.borrow 0 .shared ⟨0,1⟩,
     .raw (.allocate ⟨64,by decide⟩ ⟨8,8⟩),.raw (.writeBytes 0 8 (List.replicate 8 0))]).getD NativeReferenceMachine.empty

example : invoke f1 ready (inputs 0 0 ⟨0,by decide⟩ ⟨8,by decide⟩) = .returned (.scalar .unit) ready := by decide

example : (match invoke f1 ready (inputs 0 0 ⟨8,by decide⟩ ⟨8,by decide⟩) with
    | .returned (.scalar .unit) world => (world.pointers.heap.memory.blocks.length,
      world.leases == ready.leases,world.pointers.history == ready.pointers.history,world.nextTag)
    | _ => (99,false,false,99)) = (0,true,true,1) := by decide

example : invoke f1 ready (inputs 0 0 ⟨7,by decide⟩ ⟨8,by decide⟩) = .invalid ready := by decide
example : invoke f1 ready (inputs 99 0 ⟨0,by decide⟩ ⟨8,by decide⟩) = .invalid ready := by decide
example : invoke f1 ready (inputs 0 99 ⟨0,by decide⟩ ⟨8,by decide⟩) = .invalid ready := by decide
example : invoke f1 ready (inputs 0 0 ⟨0,by decide⟩ ⟨3,by decide⟩) = .invalid ready := by decide

example : (do
    let bare ← NativeReferenceMachine.execute ready (.raw (.fromAddress ⟨128,by decide⟩))
    pure (invoke f1 bare (inputs 0 0 ⟨0,by decide⟩ ⟨8,by decide⟩) == .returned (.scalar .unit) bare,
      invoke f1 bare (inputs 0 0 ⟨8,by decide⟩ ⟨8,by decide⟩) == .invalid bare)) = some (true,true) := by decide

example : (do
    let ended ← NativeReferenceMachine.execute ready (.endBorrow 0)
    pure (invoke f1 ended (inputs 0 0 ⟨0,by decide⟩ ⟨8,by decide⟩) == .invalid ended)) = some true := by decide

example : (match invoke f1 ready (inputs 0 0 ⟨8,by decide⟩ ⟨8,by decide⟩) with
    | .returned (.scalar .unit) world => invoke f1 world (inputs 0 0 ⟨8,by decide⟩ ⟨8,by decide⟩) == .invalid world
    | _ => false) = true := by decide

example : (do
    let borrowed ← NativeReferenceMachine.execute ready (.borrow 0 .exclusive ⟨8,8⟩)
    pure (invoke f1 borrowed (inputs 1 0 ⟨8,by decide⟩ ⟨8,by decide⟩) == .invalid borrowed)) = some true := by decide

end HasteBootsGlobalDeallocationSmoke
