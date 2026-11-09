namespace HasteBootsVecDrop.EmptyConstructionSmoke
open FormalProof4FHE.HasteBoots
private def allocated : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty [.raw (.allocate 128 ⟨24,8⟩)]).getD NativeReferenceMachine.empty
private theorem reached : NativeReferenceMachine.Reachable allocated :=
  NativeReferenceMachine.run_reachable _ _ .empty [.raw (.allocate 128 ⟨24,8⟩)] (by decide)
private theorem separate : NativeVecBytePrefix.Available allocated ⟨128,some ⟨128,0⟩⟩ 24 := by
  intro lease member
  cases member
example : ∃ stored, ∃ ready : NativeEmptyVecStorage.Ready stored, ∃ final,
    HasteBootsVecEmpty.constructStored allocated 0 = some stored ∧
    execute stored [.vectorExclusiveReference 0] = .returned (.scalar .unit) final ∧
    NativeReferenceMachine.Reachable final ∧ final.leases = stored.leases ∧
    final.pointers.heap = stored.pointers.heap ∧ stored.leases = ready.descriptor.lease :: allocated.leases :=
  empty_construct_destroy_complete allocated 0 ⟨128,some ⟨128,0⟩⟩ reached (by decide) (by decide) separate
example (stored : NativeReferenceMachine.State)
    (constructed : HasteBootsVecEmpty.constructStored allocated 0 = some stored)
    (flow : NativeRecordLLBC.Flow)
    (invoked : NativeRecordDropCalls.Invokes f1 stored [.vectorExclusiveReference 0] flow) :
    ∃ final, flow = .returned (.scalar .unit) final ∧ NativeReferenceMachine.Reachable final ∧
      final.leases = stored.leases ∧ final.pointers.heap = stored.pointers.heap :=
  constructed_empty_every_invocation allocated stored 0 ⟨128,some ⟨128,0⟩⟩ reached (by decide) (by decide) separate constructed flow invoked
end HasteBootsVecDrop.EmptyConstructionSmoke
