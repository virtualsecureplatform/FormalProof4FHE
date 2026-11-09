namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeReferenceMachine (State)
open NativePointerStorage (Pointer Address)
open NativeWord64Memory (Word)

/-- A fresh modeled reservation and its stored complete pointer supply every
condition for the retained reference destructor. Rust with_capacity refinement
is a separate obligation. Unused reserved bytes need not be initialized. -/
theorem modeled_reservation_destroy_complete (world : State) (headerRegister : Nat) (header : Pointer) (base : Address) (capacity : Word)
    (reachable : NativeReferenceMachine.Reachable world)
    (headerResident : world.pointers.registers[headerRegister]? = some header)
    (checked : NativeByteRange.checkRange world.pointers.heap.memory header ⟨24,8⟩ = true)
    (headerAvailable : NativeVecBytePrefix.Available world header 24)
    (positive : 0 < capacity.val) (capacityBound : capacity.val < 2^63)
    (nonnull : base.val ≠ 0) (addressBound : base.val + capacity.val ≤ 2^64)
    (space : ∀ block ∈ world.pointers.heap.memory.blocks,
      NativeByteMemory.Disjoint (NativeByteMemory.freshBlock world.pointers.heap.memory base ⟨capacity.val,1⟩) block)
    (bufferAvailable : NativeVecBytePrefix.Available world (NativeReservedVecConstruction.buffer world base) capacity.val)
    (headerSeparate : ¬ NativeByteBorrow.Overlap (NativeReservedVecConstruction.buffer world base) ⟨capacity.val,1⟩ header ⟨24,8⟩) :
    ∃ stored final, NativeReservedVecConstruction.reserve world headerRegister base capacity = some stored ∧
      execute stored [.vectorExclusiveReference 0] = .returned (.scalar .unit) final ∧
      NativeReferenceMachine.Reachable final ∧ final.leases = stored.leases ∧
      NativePointerByteMemory.deallocate stored.pointers.heap (NativeReservedVecConstruction.buffer world base)
        ⟨capacity.val,1⟩ = some final.pointers.heap := by
  obtain ⟨stored,ready,reserved,reached,owned,available,_,references,reference⟩ :=
    NativeReservedVecConstruction.reserve_complete world headerRegister header base capacity reachable headerResident checked
      headerAvailable positive capacityBound nonnull addressBound space bufferAvailable headerSeparate
  have index : stored.references.idxOf ready.descriptor.reference = 0 := by
    rw [reference,references]
    exact List.idxOf_cons_self
  obtain ⟨final,executed,finalReached,loans,effect⟩ :=
    vec_execute_complete ready.descriptor reached ready.initialized available ready.frontier owned
  have nonzero : capacity ≠ 0 := by
    intro zero
    rw [zero] at positive
    exact Nat.not_lt_zero _ positive
  rw [index] at executed
  have freed : NativePointerByteMemory.deallocate stored.pointers.heap (NativeReservedVecConstruction.buffer world base)
      ⟨capacity.val,1⟩ = some final.pointers.heap := by
    simpa only [ready.capacity_eq,ready.buffer_eq,nonzero,ite_false] using effect
  exact ⟨stored,final,reserved,executed,finalReached,loans,freed⟩

/-- Every operational destructor invocation of the modeled fresh reservation
releases exactly its original complete pointer and allocation extent. -/
theorem modeled_reservation_every_invocation (world stored : State) (headerRegister : Nat) (header : Pointer) (base : Address) (capacity : Word)
    (reachable : NativeReferenceMachine.Reachable world)
    (headerResident : world.pointers.registers[headerRegister]? = some header)
    (checked : NativeByteRange.checkRange world.pointers.heap.memory header ⟨24,8⟩ = true)
    (headerAvailable : NativeVecBytePrefix.Available world header 24)
    (positive : 0 < capacity.val) (capacityBound : capacity.val < 2^63)
    (nonnull : base.val ≠ 0) (addressBound : base.val + capacity.val ≤ 2^64)
    (space : ∀ block ∈ world.pointers.heap.memory.blocks,
      NativeByteMemory.Disjoint (NativeByteMemory.freshBlock world.pointers.heap.memory base ⟨capacity.val,1⟩) block)
    (bufferAvailable : NativeVecBytePrefix.Available world (NativeReservedVecConstruction.buffer world base) capacity.val)
    (headerSeparate : ¬ NativeByteBorrow.Overlap (NativeReservedVecConstruction.buffer world base) ⟨capacity.val,1⟩ header ⟨24,8⟩)
    (reserved : NativeReservedVecConstruction.reserve world headerRegister base capacity = some stored)
    (flow : NativeRecordLLBC.Flow)
    (invoked : NativeRecordDropCalls.Invokes f1 stored [.vectorExclusiveReference 0] flow) :
    ∃ final, flow = .returned (.scalar .unit) final ∧ NativeReferenceMachine.Reachable final ∧
      final.leases = stored.leases ∧ NativePointerByteMemory.deallocate stored.pointers.heap
        (NativeReservedVecConstruction.buffer world base) ⟨capacity.val,1⟩ = some final.pointers.heap := by
  obtain ⟨actual,ready,expected,reached,owned,available,_,references,reference⟩ :=
    NativeReservedVecConstruction.reserve_complete world headerRegister header base capacity reachable headerResident checked
      headerAvailable positive capacityBound nonnull addressBound space bufferAvailable headerSeparate
  have same := Option.some.inj (expected.symm.trans reserved)
  subst stored
  have index : actual.references.idxOf ready.descriptor.reference = 0 := by
    rw [reference,references]
    exact List.idxOf_cons_self
  rw [← index] at invoked
  obtain ⟨final,returned,finalReached,loans,effect⟩ :=
    vec_glue_invokes_unit ready.descriptor reached ready.initialized available ready.frontier owned flow invoked
  have nonzero : capacity ≠ 0 := by
    intro zero
    rw [zero] at positive
    exact Nat.not_lt_zero _ positive
  refine ⟨final,returned,finalReached,loans,?_⟩
  simpa only [ready.capacity_eq,ready.buffer_eq,nonzero,ite_false] using effect
end HasteBootsVecDrop
