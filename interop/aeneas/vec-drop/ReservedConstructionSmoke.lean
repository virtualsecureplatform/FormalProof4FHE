namespace HasteBootsVecDrop.ReservedConstructionSmoke
open FormalProof4FHE.HasteBoots
private def world : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty [.raw (.allocate 128 ⟨24,8⟩)]).getD NativeReferenceMachine.empty
private theorem reached : NativeReferenceMachine.Reachable world :=
  NativeReferenceMachine.run_reachable _ _ .empty [.raw (.allocate 128 ⟨24,8⟩)] (by decide)
private theorem headerAvailable : NativeVecBytePrefix.Available world ⟨128,some ⟨128,0⟩⟩ 24 := by
  intro lease member
  cases member
private theorem bufferAvailable : NativeVecBytePrefix.Available world (NativeReservedVecConstruction.buffer world 64) 8 := by
  intro lease member
  cases member
private theorem space : ∀ block ∈ world.pointers.heap.memory.blocks,
    NativeByteMemory.Disjoint (NativeByteMemory.freshBlock world.pointers.heap.memory 64 ⟨8,1⟩) block := by
  intro block member
  have same : block = NativeByteMemory.freshBlock NativeByteMemory.empty 128 ⟨24,8⟩ := List.mem_singleton.mp member
  subst block
  decide
example : ∃ stored final, NativeReservedVecConstruction.reserve world 0 64 8 = some stored ∧
    execute stored [.vectorExclusiveReference 0] = .returned (.scalar .unit) final ∧
    NativeReferenceMachine.Reachable final ∧ final.leases = stored.leases ∧
    NativePointerByteMemory.deallocate stored.pointers.heap (NativeReservedVecConstruction.buffer world 64)
      ⟨8,1⟩ = some final.pointers.heap :=
  modeled_reservation_destroy_complete world 0 ⟨128,some ⟨128,0⟩⟩ 64 8 reached (by decide) (by decide) headerAvailable
    (by decide) (by decide) (by decide) (by decide) space bufferAvailable (by decide)
example (stored : NativeReferenceMachine.State)
    (reserved : NativeReservedVecConstruction.reserve world 0 64 8 = some stored)
    (flow : NativeRecordLLBC.Flow) (invoked : NativeRecordDropCalls.Invokes f1 stored [.vectorExclusiveReference 0] flow) :
    ∃ final, flow = .returned (.scalar .unit) final ∧ NativeReferenceMachine.Reachable final ∧
      final.leases = stored.leases ∧ NativePointerByteMemory.deallocate stored.pointers.heap
        (NativeReservedVecConstruction.buffer world 64) ⟨8,1⟩ = some final.pointers.heap :=
  modeled_reservation_every_invocation world stored 0 ⟨128,some ⟨128,0⟩⟩ 64 8 reached (by decide) (by decide) headerAvailable
    (by decide) (by decide) (by decide) (by decide) space bufferAvailable (by decide) reserved flow invoked
end HasteBootsVecDrop.ReservedConstructionSmoke
