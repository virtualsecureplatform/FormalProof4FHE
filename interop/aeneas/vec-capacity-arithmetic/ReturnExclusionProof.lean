namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem handled_terminal_no_return (flow : Flow) (terminal : handledTerminal flow)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State) : flow ≠ .returned value world := by
  cases flow <;> simp_all [handledTerminal]

theorem terminal_root_rejected_terminal (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (large : 2^63 ≤ capacity.val) (valid : NativeReferenceMachine.WellFormed start) :
    handledTerminal (terminalRootInvoke fields formatter panic start base address outcome shim capacity) := by
  rw [terminal_root_rejected fields formatter panic start capacity base address nonzero outcome shim large valid]
  exact effect_outer_error_terminal _ _ _

theorem terminal_root_null_terminal (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (shim : NativeAllocatorLLBC.Body)
    (shimWorld : NativeReferenceMachine.State) (valid : NativeReferenceMachine.WellFormed start)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted start address) [] =
      .returned (.scalar .unit) shimWorld) :
    handledTerminal (terminalRootInvoke fields formatter panic start base address none shim capacity) := by
  rw [terminal_root_allocation_failure fields formatter panic start capacity base address nonzero shim shimWorld valid positive bounded returned]
  exact effect_outer_error_terminal _ _ _

theorem terminal_root_rejected_no_return (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (large : 2^63 ≤ capacity.val) (valid : NativeReferenceMachine.WellFormed start)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State) :
    terminalRootInvoke fields formatter panic start base address outcome shim capacity ≠ .returned value world := by
  intro returned
  have actual := terminal_root_rejected fields formatter panic start capacity base address nonzero outcome shim large valid
  exact effect_outer_error_no_return base
    (fun placement => effectHandlerEval placement (terminalHandlerTail fields formatter panic))
    (handledRawErrorFrame start capacity (NativeZstBorrow.grantedExclusive start address) .capacityOverflow)
    value world (actual.symm.trans returned)

theorem terminal_root_null_no_return (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (shim : NativeAllocatorLLBC.Body)
    (shimWorld : NativeReferenceMachine.State) (valid : NativeReferenceMachine.WellFormed start)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63)
    (shimReturned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted start address) [] =
      .returned (.scalar .unit) shimWorld) (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State) :
    terminalRootInvoke fields formatter panic start base address none shim capacity ≠ .returned value world := by
  intro returned
  have actual := terminal_root_allocation_failure fields formatter panic start capacity base address nonzero shim shimWorld valid positive bounded shimReturned
  exact effect_outer_error_no_return base
    (fun placement => effectHandlerEval placement (terminalHandlerTail fields formatter panic))
    (handledRawErrorFrame start capacity (NativeZstBorrow.grantedExclusive shimWorld address) (.allocationError capacity 1))
    value world (actual.symm.trans returned)

-- No snapshot-success, formatting, panic or callback-trace assumption is used.
theorem terminal_root_return_capacity_bound (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (valid : NativeReferenceMachine.WellFormed start)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State)
    (returned : terminalRootInvoke fields formatter panic start base address outcome shim capacity = .returned value world) :
    capacity.val < 2^63 := by
  by_contra rejected
  have large : 2^63 ≤ capacity.val := by omega
  exact terminal_root_rejected_no_return fields formatter panic start capacity base address nonzero outcome shim large valid value world returned

theorem terminal_root_return_requires_allocation (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld : NativeReferenceMachine.State)
    (valid : NativeReferenceMachine.WellFormed start) (positive : 0 < capacity.val)
    (shimReturned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted start address) [] =
      .returned (.scalar .unit) shimWorld)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State)
    (returned : terminalRootInvoke fields formatter panic start base address outcome shim capacity = .returned value world) :
    ∃ pointer, NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 =
      .value (.raw ⟨pointer,none⟩) world ∧ pointer.address.val ≠ 0 ∧ value = positiveVecValue pointer capacity := by
  have bounded := terminal_root_return_capacity_bound fields formatter panic start capacity base address nonzero outcome shim valid value world returned
  cases outcome with
  | none =>
    exact False.elim (terminal_root_null_no_return fields formatter panic start capacity base address nonzero shim shimWorld
      valid positive bounded shimReturned value world returned)
  | some allocationBase =>
    rcases allocator_some_classification shimWorld allocationBase capacity 1 with failed | ⟨pointer,after,allocated,nonnull⟩
    · rw [terminal_root_allocator_invalid fields formatter panic start capacity base address nonzero (some allocationBase)
        shim shimWorld shimWorld positive bounded shimReturned failed] at returned
      cases returned
    · rw [terminal_root_success fields formatter panic start capacity base address nonzero (some allocationBase)
        shim shimWorld after pointer positive bounded nonnull shimReturned allocated] at returned
      obtain ⟨valueEq,worldEq⟩ := Flow.returned.inj returned
      rw [worldEq] at allocated
      exact ⟨pointer,allocated,nonnull,valueEq.symm⟩

theorem terminal_root_return_fresh_allocation (fields : NativeRecordValues.Ty)
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
      value = positiveVecValue
        (NativeByteMemory.freshBlock shimWorld.pointers.heap.memory allocationBase (NativeAllocatorExecution.request capacity 1)).pointer capacity ∧
      world = NativeAllocatorExecution.allocated shimWorld allocationBase (NativeAllocatorExecution.request capacity 1) ∧
      (NativeByteMemory.freshBlock shimWorld.pointers.heap.memory allocationBase (NativeAllocatorExecution.request capacity 1)).Valid := by
  obtain ⟨pointer,allocated,nonnull,valueEq⟩ := terminal_root_return_requires_allocation fields formatter panic start capacity
    base address nonzero outcome shim shimWorld valid positive shimReturned value world returned
  cases outcome with
  | none =>
    have bounded := terminal_root_return_capacity_bound fields formatter panic start capacity base address nonzero none shim valid value world returned
    exact False.elim (terminal_root_null_no_return fields formatter panic start capacity base address nonzero shim shimWorld
      valid positive bounded shimReturned value world returned)
  | some allocationBase =>
    obtain ⟨pointerEq,worldEq,blockValid⟩ := allocator_some_success_exact shimWorld world allocationBase capacity 1 pointer allocated
    exact ⟨allocationBase,rfl,by rw [valueEq,pointerEq],worldEq,blockValid⟩

end HasteBootsVecCapacityArithmetic
