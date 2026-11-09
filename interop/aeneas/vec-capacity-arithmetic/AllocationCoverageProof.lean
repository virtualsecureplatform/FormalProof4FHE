namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem allocator_some_classification (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (size alignment : NativeWord64Memory.Word) :
    NativeAllocatorExecution.run world .allocate (some base) size alignment = .invalid world ∨
      ∃ pointer final, NativeAllocatorExecution.run world .allocate (some base) size alignment =
        .value (.raw ⟨pointer,none⟩) final ∧ pointer.address.val ≠ 0 := by
  by_cases accepted : (NativeAllocatorExecution.request size alignment).Valid ∧ 0 < size.val
  · cases memoryStep : NativeByteMemory.allocate world.pointers.heap.memory base (NativeAllocatorExecution.request size alignment) with
    | none =>
      left
      simp [NativeAllocatorExecution.run,accepted,NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,
        NativePointerMachine.execute,NativePointerByteMemory.allocate,memoryStep]
    | some pair =>
      rcases pair with ⟨pointer,memory⟩
      obtain ⟨pointerEq,memoryEq,blockValid,separated⟩ := NativeByteMemory.allocate_success _ _ _ _ _ memoryStep
      subst pointer
      subst memory
      right
      refine ⟨(NativeByteMemory.freshBlock world.pointers.heap.memory base (NativeAllocatorExecution.request size alignment)).pointer,
        NativeAllocatorExecution.allocated world base (NativeAllocatorExecution.request size alignment),?_,?_⟩
      · simp [NativeAllocatorExecution.run,accepted,NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,
          NativePointerMachine.execute,NativePointerByteMemory.allocate,memoryStep,NativeReferenceMachine.setPointers,
          NativeAllocatorExecution.allocated]
      · exact blockValid.2.2.1
  · left
    simp only [NativeAllocatorExecution.run,ite_eq_right accepted]

theorem allocator_some_success_exact (world after : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (size alignment : NativeWord64Memory.Word) (pointer : NativePointerStorage.Pointer)
    (returned : NativeAllocatorExecution.run world .allocate (some base) size alignment = .value (.raw ⟨pointer,none⟩) after) :
    pointer = (NativeByteMemory.freshBlock world.pointers.heap.memory base (NativeAllocatorExecution.request size alignment)).pointer ∧
    after = NativeAllocatorExecution.allocated world base (NativeAllocatorExecution.request size alignment) ∧
    (NativeByteMemory.freshBlock world.pointers.heap.memory base (NativeAllocatorExecution.request size alignment)).Valid := by
  by_cases accepted : (NativeAllocatorExecution.request size alignment).Valid ∧ 0 < size.val
  · cases memoryStep : NativeByteMemory.allocate world.pointers.heap.memory base (NativeAllocatorExecution.request size alignment) with
    | none =>
      simp [NativeAllocatorExecution.run,accepted,NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,
        NativePointerMachine.execute,NativePointerByteMemory.allocate,memoryStep] at returned
    | some pair =>
      rcases pair with ⟨fresh,memory⟩
      obtain ⟨freshEq,memoryEq,blockValid,separated⟩ := NativeByteMemory.allocate_success _ _ _ _ _ memoryStep
      subst fresh
      subst memory
      have actual : NativeAllocatorExecution.run world .allocate (some base) size alignment =
          .value (.raw ⟨(NativeByteMemory.freshBlock world.pointers.heap.memory base (NativeAllocatorExecution.request size alignment)).pointer,none⟩)
            (NativeAllocatorExecution.allocated world base (NativeAllocatorExecution.request size alignment)) := by
        simp [NativeAllocatorExecution.run,accepted,NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,
          NativePointerMachine.execute,NativePointerByteMemory.allocate,memoryStep,NativeReferenceMachine.setPointers,
          NativeAllocatorExecution.allocated]
      rw [actual] at returned
      obtain ⟨valueEq,worldEq⟩ := NativeRawVecFields.Result.value.inj returned
      have pointerEq := congrArg NativeSliceLLBC.Raw.storage (NativeSliceLLBC.Value.raw.inj valueEq)
      exact ⟨pointerEq.symm,worldEq.symm,blockValid⟩
  · simp only [NativeAllocatorExecution.run,ite_eq_right accepted] at returned
    cases returned

theorem runtime_allocation_invalid (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (outcome : Option NativePointerStorage.Address) (before after : NativeReferenceMachine.State)
    (failed : NativeAllocatorExecution.run before (if zeroed then .zeroed else .allocate) outcome capacity 1 = .invalid after) :
    NativeAllocatorLLBC.eval (runtimeAfterAlignment zeroed outcome) (runtimeAlignmentFrame ambient capacity zeroed before) =
      .invalid after := by
  have decoded : NativeAllocatorLLBC.decodeRequest 11 12 [.scalar (.usize capacity),byteAlignment] = some (capacity,1) :=
    NativeAllocatorLLBC.decode_request_exact 11 12 capacity 1
  rw [runtimeAfterAlignment,NativeAllocatorLLBC.eval,runtime_allocator_arguments]
  simp only [decoded]
  rw [show (runtimeArgumentsFrame ambient capacity zeroed before).world = before from rfl,failed]

theorem runtime_positive_invalid (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (outcome : Option NativePointerStorage.Address) (shim null nonnull : NativeAllocatorLLBC.Body)
    (shimWorld after : NativeReferenceMachine.State)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .returned (.scalar .unit) shimWorld)
    (failed : NativeAllocatorExecution.run shimWorld (if zeroed then .zeroed else .allocate) outcome capacity 1 = .invalid after) :
    NativeAllocatorLLBC.eval (runtimePositive outcome shim null nonnull) (implementationPrepared ambient capacity zeroed) = .invalid after := by
  rw [runtime_mode_dispatch,runtime_after_returned_shim _ _ _ _ _ _ returned,
    runtime_allocation_invalid _ _ _ _ _ _ failed]
  rfl

theorem method_allocator_invalid (ambient : Frame) (reference : NativeReferenceMachine.Reference)
    (capacity : NativeWord64Memory.Word) (zeroed : Bool) (outcome : Option NativePointerStorage.Address)
    (shim zero null : NativeAllocatorLLBC.Body) (shimWorld after : NativeReferenceMachine.State)
    (nonzero : capacity ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .returned (.scalar .unit) shimWorld)
    (failed : NativeAllocatorExecution.run shimWorld (if zeroed then .zeroed else .allocate) outcome capacity 1 = .invalid after) :
    NativeAllocatorLLBC.invokeValues
      (allocationMethod ambient zeroed zero (runtimePositive outcome shim null runtimeSuccess)) ambient.world
      [.scalar (.reference false reference 0),capacityLayout capacity] = .invalid after := by
  rw [method_invocation_forwarding,implementation_positive_invocation _ _ _ nonzero,
    runtime_positive_invalid _ _ _ _ _ _ _ _ _ returned failed]
  rfl

theorem positive_method_invalid (ambient calleeAmbient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim zero null unwind : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State)
    (failed : NativeAllocatorLLBC.invokeValues
      (allocationMethod calleeAmbient zeroed zero (runtimePositive outcome shim null runtimeSuccess))
      (NativeZstBorrow.granted ambient.world address)
      [.scalar (.reference false ⟨ambient.world.nextTag⟩ 0),capacityLayout capacity] = .invalid world) :
    NativeAllocatorLLBC.eval (positiveMethodCall calleeAmbient zeroed outcome shim zero null unwind)
      (positiveBorrowFrame ambient capacity zeroed address) = .invalid world := by
  have called := NativeAllocatorLLBC.eval_call
    (allocationMethod calleeAmbient zeroed zero (runtimePositive outcome shim null runtimeSuccess))
    (positiveBorrowFrame ambient capacity zeroed address) 10 (positiveCallArgs zeroed) unwind
    (.legacy (.dead (if zeroed then 12 else 11) .done) .done)
  rw [positive_call_arguments] at called
  simp only at called
  rw [show (positiveMovedFrame ambient capacity zeroed address).world = NativeZstBorrow.granted ambient.world address from rfl,failed] at called
  simpa only [positiveMethodCall,NativeAllocatorLLBC.resume] using called

theorem unified_constructor_allocator_invalid (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld after : NativeReferenceMachine.State)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) shimWorld)
    (failed : NativeAllocatorExecution.run shimWorld (if zeroed then .zeroed else .allocate) outcome capacity 1 = .invalid after) :
    NativeAllocatorLLBC.invokeValues (unifiedConstructorFunction ambient zeroed address outcome shim) ambient.world
      [.scalar (.usize capacity),allocationModeValue zeroed,allocatorValue,byteLayout] = .invalid after := by
  have distinct : capacity ≠ 0 := by intro same; subst capacity; simp at positive
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (unified_constructor_initialized ambient capacity zeroed address outcome shim),
    unified_constructor_dispatch,ite_eq_left bounded,unified_accepted_dispatch,ite_eq_right distinct,unifiedPositiveBody]
  rw [positive_constructor_selection _ _ _ _ _ nonzero]
  rw [positive_method_invalid _ _ _ _ _ _ _ _ _ _ _
    (method_allocator_invalid {ambient with world := NativeZstBorrow.granted ambient.world address} ⟨ambient.world.nextTag⟩
      capacity zeroed outcome shim _ runtimeNull shimWorld after distinct returned failed)]
  rfl

theorem effect_raw_constructor_terminal (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow)
    (flow : Flow) (terminal : handledTerminal flow)
    (returned : NativeAllocatorLLBC.invokeValues
      (unifiedConstructorFunction (rawEntryAmbient (handledAmbient start)) false address outcome shim) start
      [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] = flow) :
    effectRawInvoke start base address outcome shim handler capacity = flow := by
  let ambient := rawEntryAmbient (handledAmbient start)
  have initialized := unified_raw_caller_initialized (handledAmbient start) capacity address outcome shim
  change initial (rawCallerTypes ambient) 3 _ start = _ at initialized
  rw [effectRawInvoke,handledInvoke,initialized]
  change settle start (effectRawEval ambient base address outcome shim handler (rawCallerFrame ambient capacity)) = flow
  have prepared : eval (rawCallerPrefix .done) (rawCallerFrame ambient capacity) = .normal (rawCallerPrepared ambient capacity) := by
    rw [raw_caller_prefix_exact]; rfl
  rw [effectRawEval,unifiedRawCallerCall,NativeAllocatorLLBC.legacy_normal _ prepared]
  have called := NativeAllocatorLLBC.eval_call (unifiedConstructorFunction ambient false address outcome shim)
    (rawCallerPrepared ambient capacity) 4 rawCallerArgs (.legacy (outerErrorCleanup .resume) .done) .done
  rw [raw_caller_arguments] at called
  simp only at called
  rw [show (rawCallerMoved ambient capacity).world = start from rfl,returned] at called
  rw [called]
  cases flow with
  | normal changed => cases terminal
  | returned value world => cases terminal
  | invalid world => rfl
  | unsupported source world => rfl
  | unwind world => simp [NativeAllocatorLLBC.resume,NativeAllocatorLLBC.legacy_done,outerErrorCleanup,
      eval,storageDead,rawCallerMoved,handledContinue,settle]

theorem effect_root_constructor_terminal (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow)
    (flow : Flow) (terminal : handledTerminal flow)
    (returned : NativeAllocatorLLBC.invokeValues
      (unifiedConstructorFunction (rawEntryAmbient (handledAmbient start)) false address outcome shim) start
      [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] = flow) :
    effectRootInvoke start base address outcome shim handler capacity = flow :=
  effect_root_terminal start capacity base address outcome shim handler flow terminal
    (effect_raw_constructor_terminal start capacity base address outcome shim handler flow terminal returned)

theorem terminal_root_allocator_invalid (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld after : NativeReferenceMachine.State)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted start address) [] =
      .returned (.scalar .unit) shimWorld)
    (failed : NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 = .invalid after) :
    terminalRootInvoke fields formatter panic start base address outcome shim capacity = .invalid after := by
  apply effect_root_constructor_terminal start capacity base address outcome shim _ (.invalid after) (by trivial)
  exact unified_constructor_allocator_invalid (rawEntryAmbient (handledAmbient start)) capacity false address nonzero
    outcome shim shimWorld after positive bounded returned failed

-- This total normal-shim case split computes the allocator result rather than
-- assuming allocation success. It is a modeled outcome, not native work cost.
def normalAllocationOutcome (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shimWorld : NativeReferenceMachine.State) : Flow :=
  match NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 with
  | .invalid after => .invalid after
  | .value (.raw ⟨pointer,none⟩) after =>
    if pointer.address.val = 0 then
      effectOuterErrorEval base (fun placement => effectHandlerEval placement (terminalHandlerTail fields formatter panic))
        (handledRawErrorFrame start capacity (NativeZstBorrow.grantedExclusive after address) (.allocationError capacity 1))
    else .returned (positiveVecValue pointer capacity) after
  | .value _ after => .invalid after

theorem terminal_root_normal_allocation (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld : NativeReferenceMachine.State)
    (valid : NativeReferenceMachine.WellFormed start) (positive : 0 < capacity.val) (bounded : capacity.val < 2^63)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted start address) [] =
      .returned (.scalar .unit) shimWorld) :
    terminalRootInvoke fields formatter panic start base address outcome shim capacity =
      normalAllocationOutcome fields formatter panic start capacity base address outcome shimWorld := by
  cases outcome with
  | none =>
    have layoutValid : (NativeAllocatorExecution.request capacity 1).Valid := by
      refine ⟨?_,?_⟩
      · change 1 ∈ (List.range 64).map (fun exponent => 2 ^ exponent)
        decide
      · change capacity.val + (1-1) ≤ 2^63-1
        omega
    rw [terminal_root_allocation_failure fields formatter panic start capacity base address nonzero shim shimWorld valid positive bounded returned]
    simp [normalAllocationOutcome,NativeAllocatorExecution.failure_result shimWorld .allocate capacity 1 layoutValid positive,
      NativeAllocatorExecution.nullValue]
  | some allocationBase =>
    rcases allocator_some_classification shimWorld allocationBase capacity 1 with failed | ⟨pointer,after,allocated,nonnull⟩
    · rw [terminal_root_allocator_invalid fields formatter panic start capacity base address nonzero (some allocationBase)
        shim shimWorld shimWorld positive bounded returned failed]
      simp only [normalAllocationOutcome,failed]
    · rw [terminal_root_success fields formatter panic start capacity base address nonzero (some allocationBase)
        shim shimWorld after pointer positive bounded nonnull returned allocated]
      simp only [normalAllocationOutcome,allocated,ite_eq_right nonnull]

end HasteBootsVecCapacityArithmetic
