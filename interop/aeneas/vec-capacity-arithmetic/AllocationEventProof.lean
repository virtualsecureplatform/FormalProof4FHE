namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

/-- The successful vector allocator result comes from this actual checked
machine step; the step is not inferred from a counter or an arbitrary log. -/
theorem allocator_success_step (before after : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (size alignment : NativeWord64Memory.Word) (pointer : NativePointerStorage.Pointer)
    (returned : NativeAllocatorExecution.run before .allocate (some base) size alignment = .value (.raw ⟨pointer,none⟩) after) :
    NativeReferenceMachine.execute before (.raw (.allocate base (NativeAllocatorExecution.request size alignment))) = some after := by
  by_cases accepted : (NativeAllocatorExecution.request size alignment).Valid ∧ 0 < size.val
  · simp only [NativeAllocatorExecution.run,ite_eq_left accepted] at returned
    cases executed : NativeReferenceMachine.execute before (.raw (.allocate base (NativeAllocatorExecution.request size alignment))) with
    | none => simp only [executed] at returned; cases returned
    | some allocated =>
      simp only [executed] at returned
      cases registered : allocated.pointers.registers[0]? with
      | none => simp only [registered] at returned; cases returned
      | some actual =>
        simp only [registered] at returned
        have same := (NativeRawVecFields.Result.value.inj returned).2
        exact congrArg some same
  · simp only [NativeAllocatorExecution.run,ite_eq_right accepted] at returned
    cases returned

theorem allocator_success_history (before after : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (size alignment : NativeWord64Memory.Word) (pointer : NativePointerStorage.Pointer)
    (returned : NativeAllocatorExecution.run before .allocate (some base) size alignment = .value (.raw ⟨pointer,none⟩) after) :
    after.pointers.history = ⟨base,NativeAllocatorExecution.request size alignment,before.pointers.heap.memory.nextGeneration⟩ :: before.pointers.history ∧
    pointer.provenance = some ⟨base.val,before.pointers.heap.memory.nextGeneration⟩ ∧
    after.pointers.heap.memory.nextGeneration = before.pointers.heap.memory.nextGeneration+1 := by
  obtain ⟨pointerEq,worldEq,_⟩ := allocator_some_success_exact before after base size alignment pointer returned
  rw [pointerEq,worldEq]
  exact ⟨rfl,rfl,rfl⟩

theorem allocator_success_issued (before after : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (size alignment : NativeWord64Memory.Word) (pointer : NativePointerStorage.Pointer)
    (returned : NativeAllocatorExecution.run before .allocate (some base) size alignment = .value (.raw ⟨pointer,none⟩) after) :
    NativePointerMachine.Issued after.pointers ⟨base.val,before.pointers.heap.memory.nextGeneration⟩ := by
  obtain ⟨history,_,_⟩ := allocator_success_history before after base size alignment pointer returned
  refine ⟨⟨base,NativeAllocatorExecution.request size alignment,before.pointers.heap.memory.nextGeneration⟩,?_,rfl⟩
  rw [history]
  exact List.mem_cons_self

/-- This is a witness for one modeled allocation operation, not a physical
instruction count or an attacker-work lower bound. -/
theorem terminal_root_return_allocation_step (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld : NativeReferenceMachine.State)
    (valid : NativeReferenceMachine.WellFormed start) (positive : 0 < capacity.val)
    (shimReturned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted start address) [] =
      .returned (.scalar .unit) shimWorld)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State)
    (returned : terminalRootInvoke fields formatter panic start base address outcome shim capacity = .returned value world) :
    ∃ allocationBase, outcome = some allocationBase ∧
      NativeReferenceMachine.execute shimWorld (.raw (.allocate allocationBase (NativeAllocatorExecution.request capacity 1))) = some world ∧
      NativePointerMachine.Issued world.pointers ⟨allocationBase.val,shimWorld.pointers.heap.memory.nextGeneration⟩ := by
  obtain ⟨allocationBase,outcomeEq,valueEq,worldEq,blockValid⟩ := terminal_root_return_fresh_allocation fields formatter panic
    start capacity base address nonzero outcome shim shimWorld valid positive shimReturned value world returned
  subst outcome
  obtain ⟨pointer,allocated,_,_⟩ := terminal_root_return_requires_allocation fields formatter panic start capacity base address nonzero
    (some allocationBase) shim shimWorld valid positive shimReturned value world returned
  exact ⟨allocationBase,rfl,allocator_success_step shimWorld world allocationBase capacity 1 pointer allocated,
    allocator_success_issued shimWorld world allocationBase capacity 1 pointer allocated⟩

theorem terminal_root_return_history_growth (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld : NativeReferenceMachine.State)
    (valid : NativeReferenceMachine.WellFormed start) (positive : 0 < capacity.val)
    (shimReturned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted start address) [] =
      .returned (.scalar .unit) shimWorld)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State)
    (returned : terminalRootInvoke fields formatter panic start base address outcome shim capacity = .returned value world) :
    world.pointers.history.length = shimWorld.pointers.history.length+1 ∧
    world.pointers.heap.memory.blocks.length = shimWorld.pointers.heap.memory.blocks.length+1 ∧
    world.pointers.heap.memory.nextGeneration = shimWorld.pointers.heap.memory.nextGeneration+1 := by
  obtain ⟨allocationBase,_,_,worldEq,_⟩ := terminal_root_return_fresh_allocation fields formatter panic
    start capacity base address nonzero outcome shim shimWorld valid positive shimReturned value world returned
  rw [worldEq]
  simp [NativeAllocatorExecution.allocated]

theorem terminal_root_return_reference_state (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld : NativeReferenceMachine.State)
    (valid : NativeReferenceMachine.WellFormed start) (positive : 0 < capacity.val)
    (shimReturned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted start address) [] =
      .returned (.scalar .unit) shimWorld)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State)
    (returned : terminalRootInvoke fields formatter panic start base address outcome shim capacity = .returned value world) :
    world.leases = shimWorld.leases ∧ world.references = shimWorld.references ∧
    world.births = shimWorld.births ∧ world.nextTag = shimWorld.nextTag := by
  obtain ⟨allocationBase,_,_,worldEq,_⟩ := terminal_root_return_fresh_allocation fields formatter panic
    start capacity base address nonzero outcome shim shimWorld valid positive shimReturned value world returned
  rw [worldEq]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem terminal_root_return_new_origin (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld : NativeReferenceMachine.State)
    (valid : NativeReferenceMachine.WellFormed start) (positive : 0 < capacity.val)
    (shimReturned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted start address) [] =
      .returned (.scalar .unit) shimWorld)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State)
    (returned : terminalRootInvoke fields formatter panic start base address outcome shim capacity = .returned value world) :
    ∃ allocationBase, outcome = some allocationBase ∧
      NativePointerMachine.Issued world.pointers ⟨allocationBase.val,shimWorld.pointers.heap.memory.nextGeneration⟩ ∧
      ¬ NativePointerMachine.Issued shimWorld.pointers ⟨allocationBase.val,shimWorld.pointers.heap.memory.nextGeneration⟩ := by
  have borrowedValid : NativeReferenceMachine.WellFormed (NativeZstBorrow.granted start address) :=
    NativeReferenceMachine.execute_wellFormed _ _
      (NativeReferenceMachine.execute_wellFormed _ _ valid _ (NativeZstBorrow.placement_step start address)) _
      (NativeZstBorrow.grant_step start address nonzero)
  have shimValid := NativeSliceLLBC.reference_runs_wellFormed _ _ borrowedValid
    (NativeAllocatorLLBC.invokeValues_projects (runtimeShim shim) (NativeZstBorrow.granted start address) [])
  rw [shimReturned] at shimValid
  obtain ⟨allocationBase,outcomeEq,_,issued⟩ := terminal_root_return_allocation_step fields formatter panic start capacity base
    address nonzero outcome shim shimWorld valid positive shimReturned value world returned
  exact ⟨allocationBase,outcomeEq,issued,NativePointerMachine.fresh_not_issued shimWorld.pointers shimValid.1 allocationBase⟩

end HasteBootsVecCapacityArithmetic
