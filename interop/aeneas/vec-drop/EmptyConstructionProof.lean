namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots

/-- The actual empty constructor, checked header write and fresh borrow supply
all resident conditions of the original complete destructor. -/
theorem empty_construct_destroy_complete (world : NativeReferenceMachine.State) (register : Nat) (header : NativePointerStorage.Pointer)
    (reachable : NativeReferenceMachine.Reachable world)
    (resident : world.pointers.registers[register]? = some header)
    (checked : NativeByteRange.checkRange world.pointers.heap.memory header ⟨24,8⟩ = true)
    (separate : NativeVecBytePrefix.Available world header 24) :
    ∃ stored, ∃ ready : NativeEmptyVecStorage.Ready stored, ∃ final,
      HasteBootsVecEmpty.constructStored world register = some stored ∧
      execute stored [.vectorExclusiveReference 0] = .returned (.scalar .unit) final ∧
      NativeReferenceMachine.Reachable final ∧ final.leases = stored.leases ∧
      final.pointers.heap = stored.pointers.heap ∧ stored.leases = ready.descriptor.lease :: world.leases := by
  obtain ⟨stored,ready,constructed,reached,_,loans,references,reference⟩ :=
    HasteBootsVecEmpty.constructStored_complete world register header reachable resident checked separate
  have index : stored.references.idxOf ready.descriptor.reference = 0 := by
    rw [reference,references]
    exact List.idxOf_cons_self
  obtain ⟨final,executed,finalReached,finalLoans,effect⟩ :=
    vec_execute_complete ready.descriptor reached ready.initialized ready.available ready.frontier ready.owned
  rw [index] at executed
  rw [ready.capacity_zero] at effect
  change final.pointers.heap = _ at effect
  exact ⟨stored,ready,final,constructed,executed,finalReached,finalLoans,effect,loans⟩

/-- Every operational invocation of a successfully constructed empty Vec returns
normally with the stored heap and complete incoming loan list preserved. -/
theorem constructed_empty_every_invocation (world stored : NativeReferenceMachine.State) (register : Nat)
    (header : NativePointerStorage.Pointer)
    (reachable : NativeReferenceMachine.Reachable world)
    (resident : world.pointers.registers[register]? = some header)
    (checked : NativeByteRange.checkRange world.pointers.heap.memory header ⟨24,8⟩ = true)
    (separate : NativeVecBytePrefix.Available world header 24)
    (constructed : HasteBootsVecEmpty.constructStored world register = some stored)
    (flow : NativeRecordLLBC.Flow)
    (invoked : NativeRecordDropCalls.Invokes f1 stored [.vectorExclusiveReference 0] flow) :
    ∃ final, flow = .returned (.scalar .unit) final ∧ NativeReferenceMachine.Reachable final ∧
      final.leases = stored.leases ∧ final.pointers.heap = stored.pointers.heap := by
  obtain ⟨actual,ready,expected,reached,_,_,references,reference⟩ :=
    HasteBootsVecEmpty.constructStored_complete world register header reachable resident checked separate
  have same := Option.some.inj (expected.symm.trans constructed)
  subst stored
  have index : actual.references.idxOf ready.descriptor.reference = 0 := by
    rw [reference,references]
    exact List.idxOf_cons_self
  rw [← index] at invoked
  obtain ⟨final,returned,finalReached,loans,effect⟩ :=
    vec_glue_invokes_unit ready.descriptor reached ready.initialized ready.available ready.frontier ready.owned flow invoked
  rw [ready.capacity_zero] at effect
  change final.pointers.heap = _ at effect
  exact ⟨final,returned,finalReached,loans,effect⟩
end HasteBootsVecDrop
