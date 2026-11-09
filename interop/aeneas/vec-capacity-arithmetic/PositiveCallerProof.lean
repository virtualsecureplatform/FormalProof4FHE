namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem positive_raw_caller_resumes (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim unwind next : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (positiveConstructorFunction ambient false address outcome shim) ambient.world
      [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] = .returned (positiveResultValue pointer capacity) world) :
    NativeAllocatorLLBC.eval (positiveRawCallerCall ambient address outcome shim unwind next) (rawCallerFrame ambient capacity) =
      NativeAllocatorLLBC.eval next (positiveRawCallerReturned ambient capacity world pointer) := by
  have prepared : eval (rawCallerPrefix .done) (rawCallerFrame ambient capacity) = .normal (rawCallerPrepared ambient capacity) := by
    rw [raw_caller_prefix_exact]; rfl
  rw [positiveRawCallerCall,NativeAllocatorLLBC.legacy_normal _ prepared]
  have called := NativeAllocatorLLBC.eval_call (positiveConstructorFunction ambient false address outcome shim)
    (rawCallerPrepared ambient capacity) 4 rawCallerArgs unwind next
  rw [raw_caller_arguments] at called
  simp only at called
  rw [show (rawCallerMoved ambient capacity).world = ambient.world from rfl,returned] at called
  rw [called]
  simp [NativeAllocatorLLBC.resume,positiveRawCallerReturned,write,rawCallerMoved,rawCallerTypes,layoutTypes,calleeEntryAmbient,
    positiveResultValue,positiveRawValue,runtimeThinValue,allocatorValue,nonnull,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem positive_raw_capacity_prefix (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (nonnull : pointer.address.val ≠ 0)
    (error next : Body) :
    eval (positiveRawCallerCapacityPrefix error next) (positiveRawCallerReturned ambient capacity world pointer) =
      eval next (positiveRawCallerCapacityFrame ambient capacity world pointer) := by
  simp [positiveRawCallerCapacityPrefix,positiveRawCallerCapacityFrame,positiveRawCallerReturned,rawCallerMoved,
    rawCallerTypes,layoutTypes,calleeEntryAmbient,positiveResultValue,positiveRawValue,runtimeThinValue,allocatorValue,
    byteLayout,nonnull,eval,evalRvalue,evalOperand,selectChoice,storageLive,storageDead,NativeRecordLLBC.read,
    write,retag,NativeSliceLLBC.retagValue,NativeRecordValues.sideAt,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.replace,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
    NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem positive_raw_capacity_arithmetic (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (next : Body) :
    eval (positiveRawCallerArithmetic next) (positiveRawCallerCapacityFrame ambient capacity world pointer) =
      eval next (positiveRawCallerCheckedFrame ambient capacity world pointer) := by
  have reduced : capacity.val % 18446744073709551616 = capacity.val := Nat.mod_eq_of_lt capacity.isLt
  simp [positiveRawCallerArithmetic,positiveRawCallerCheckedFrame,positiveRawCallerCapacityFrame,
    positiveRawCallerReturned,rawCallerMoved,rawCallerTypes,expr_wrappingSubtract,expr_greater,expr_logicalNot,
    eval,evalRvalue,evalArithmetic,evalArgs,evalOperand,storageDead,NativeRecordLLBC.read,write,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits,
    NativeRecordArithmetic.eval,NativeRecordArithmetic.word,reduced]

theorem positive_raw_checked_return (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (nonnull : pointer.address.val ≠ 0)
    (cold : Body) :
    eval (positiveRawCallerReturn cold) (positiveRawCallerCheckedFrame ambient capacity world pointer) =
      .returned (positiveRawValue pointer capacity) world := by
  simp [positiveRawCallerReturn,positiveRawCallerCheckedFrame,positiveRawCallerCapacityFrame,positiveRawCallerReturned,
    rawCallerMoved,rawCallerTypes,layoutTypes,calleeEntryAmbient,positiveRawValue,runtimeThinValue,allocatorValue,nonnull,
    eval,evalBooleanOperand,evalOperand,storageDead,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem positive_raw_caller_tail (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (nonnull : pointer.address.val ≠ 0)
    (error cold : Body) :
    eval (rawCallerTail error cold) (positiveRawCallerReturned ambient capacity world pointer) = .returned (positiveRawValue pointer capacity) world := by
  change eval (positiveRawCallerCapacityPrefix error (positiveRawCallerArithmetic (positiveRawCallerReturn cold))) _ = _
  rw [positive_raw_capacity_prefix _ _ _ _ nonnull,positive_raw_capacity_arithmetic,positive_raw_checked_return _ _ _ _ nonnull]

theorem positive_raw_caller_initialized (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    initial (positiveRawCallerFunction ambient address outcome shim).types 3 [.scalar (.usize capacity),allocatorValue,byteLayout] ambient.world =
      some (rawCallerFrame (rawEntryAmbient ambient) capacity) := by
  simp [positiveRawCallerFunction,rawEntryAmbient,rawCallerFrame,rawCallerTypes,initial,layoutTypes,calleeEntryAmbient,
    allocatorValue,byteLayout,byteAlignment,alignmentDiscriminants,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits,List.replicate_succ]

theorem positive_vec_caller_resumes (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim unwind next : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (positiveRawCallerFunction ambient address outcome shim) ambient.world
      [.scalar (.usize capacity),allocatorValue,byteLayout] = .returned (positiveRawValue pointer capacity) world) :
    NativeAllocatorLLBC.eval (positiveVecCallerCall ambient address outcome shim unwind next) (vecCallerFrame ambient capacity) =
      NativeAllocatorLLBC.eval next (positiveVecCallerReturned ambient capacity world pointer) := by
  have prepared : eval (vecCallerPrefix .done) (vecCallerFrame ambient capacity) = .normal (vecCallerPrepared ambient capacity) := by
    rw [vec_caller_prefix_exact]; rfl
  rw [positiveVecCallerCall,NativeAllocatorLLBC.legacy_normal _ prepared]
  have called := NativeAllocatorLLBC.eval_call (positiveRawCallerFunction ambient address outcome shim)
    (vecCallerPrepared ambient capacity) 3 vecCallerArgs unwind next
  rw [vec_caller_arguments] at called
  simp only at called
  rw [show (vecCallerMoved ambient capacity).world = ambient.world from rfl,returned] at called
  rw [called]
  simp [NativeAllocatorLLBC.resume,positiveVecCallerReturned,write,vecCallerMoved,vecCallerTypes,layoutTypes,calleeEntryAmbient,
    positiveRawValue,runtimeThinValue,allocatorValue,nonnull,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem positive_vec_caller_tail (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (nonnull : pointer.address.val ≠ 0) :
    eval vecCallerTail (positiveVecCallerReturned ambient capacity world pointer) = .returned (positiveVecValue pointer capacity) world := by
  simp [vecCallerTail,positiveVecCallerReturned,vecCallerMoved,vecCallerTypes,layoutTypes,calleeEntryAmbient,
    positiveVecValue,positiveRawValue,runtimeThinValue,allocatorValue,nonnull,eval,evalRvalue,evalArgs,evalOperand,
    storageLive,storageDead,NativeRecordLLBC.read,write,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem positive_vec_caller_initialized (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    initial (positiveVecCallerFunction ambient address outcome shim).types 1 [.scalar (.usize capacity)] ambient.world =
      some (vecCallerFrame ambient capacity) := by
  simp [positiveVecCallerFunction,vecCallerFrame,vecCallerTypes,initial,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem positive_capacity_root_resumes (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim unwind next : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (positiveVecCallerFunction ambient address outcome shim) ambient.world
      [.scalar (.usize capacity)] = .returned (positiveVecValue pointer capacity) world) :
    NativeAllocatorLLBC.eval (positiveCapacityRootCall ambient address outcome shim unwind next) (capacityRootFrame ambient capacity) =
      NativeAllocatorLLBC.eval next (positiveCapacityRootReturned ambient capacity world pointer) := by
  have prepared : eval (capacityRootPrefix .done) (capacityRootFrame ambient capacity) = .normal (capacityRootPrepared ambient capacity) := by
    rw [capacity_root_prefix]; rfl
  rw [positiveCapacityRootCall,NativeAllocatorLLBC.legacy_normal _ prepared]
  have called := NativeAllocatorLLBC.eval_call (positiveVecCallerFunction ambient address outcome shim)
    (capacityRootPrepared ambient capacity) 0 [.move 2 []] unwind next
  rw [capacity_root_arguments] at called
  simp only at called
  rw [show (capacityRootMoved ambient capacity).world = ambient.world from rfl,returned] at called
  rw [called]
  simp [NativeAllocatorLLBC.resume,positiveCapacityRootReturned,write,capacityRootMoved,capacityRootTypes,vecCallerTypes,
    layoutTypes,calleeEntryAmbient,positiveVecValue,positiveRawValue,runtimeThinValue,allocatorValue,nonnull,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem positive_capacity_root_tail (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (nonnull : pointer.address.val ≠ 0) :
    eval capacityRootTail (positiveCapacityRootReturned ambient capacity world pointer) = .returned (positiveVecValue pointer capacity) world := by
  simp [capacityRootTail,positiveCapacityRootReturned,capacityRootMoved,capacityRootTypes,vecCallerTypes,layoutTypes,calleeEntryAmbient,
    positiveVecValue,positiveRawValue,runtimeThinValue,allocatorValue,nonnull,eval,storageDead,NativeRecordLLBC.read,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem positive_capacity_root_initialized (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    initial (positiveCapacityRoot ambient address outcome shim).types 1 [.scalar (.usize capacity)] ambient.world =
      some (capacityRootFrame ambient capacity) := by
  simp [positiveCapacityRoot,capacityRootTypes,capacityRootFrame,initial,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem positive_raw_caller_invocation (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 = .value (.raw ⟨pointer,none⟩) resultWorld) :
    NativeAllocatorLLBC.invokeValues (positiveRawCallerFunction ambient address outcome shim) ambient.world
      [.scalar (.usize capacity),allocatorValue,byteLayout] = .returned (positiveRawValue pointer capacity) resultWorld := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (positive_raw_caller_initialized ambient capacity address outcome shim)]
  change settle ambient.world (NativeAllocatorLLBC.eval (positiveRawCallerCall (rawEntryAmbient ambient) address outcome shim _ _)
    (rawCallerFrame (rawEntryAmbient ambient) capacity)) = _
  rw [positive_raw_caller_resumes _ _ _ _ _ _ _ _ _ nonnull
    (positive_constructor_invocation (rawEntryAmbient ambient) capacity false address nonzero outcome shim shimWorld resultWorld pointer
      positive bounded nonnull returned allocated)]
  rw [NativeAllocatorLLBC.legacy_done,positive_raw_caller_tail _ _ _ _ nonnull]
  rfl

theorem positive_vec_caller_invocation (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 = .value (.raw ⟨pointer,none⟩) resultWorld) :
    NativeAllocatorLLBC.invokeValues (positiveVecCallerFunction ambient address outcome shim) ambient.world [.scalar (.usize capacity)] =
      .returned (positiveVecValue pointer capacity) resultWorld := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (positive_vec_caller_initialized ambient capacity address outcome shim)]
  change settle ambient.world (NativeAllocatorLLBC.eval (positiveVecCallerCall ambient address outcome shim _ _)
    (vecCallerFrame ambient capacity)) = _
  rw [positive_vec_caller_resumes _ _ _ _ _ _ _ _ _ nonnull
    (positive_raw_caller_invocation ambient capacity address nonzero outcome shim shimWorld resultWorld pointer
      positive bounded nonnull returned allocated)]
  rw [NativeAllocatorLLBC.legacy_done,positive_vec_caller_tail _ _ _ _ nonnull]
  rfl

theorem positive_capacity_root_values (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 = .value (.raw ⟨pointer,none⟩) resultWorld) :
    NativeAllocatorLLBC.invokeValues (positiveCapacityRoot ambient address outcome shim) ambient.world [.scalar (.usize capacity)] =
      .returned (positiveVecValue pointer capacity) resultWorld := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (positive_capacity_root_initialized ambient capacity address outcome shim)]
  change settle ambient.world (NativeAllocatorLLBC.eval (positiveCapacityRootCall ambient address outcome shim _ _)
    (capacityRootFrame ambient capacity)) = _
  rw [positive_capacity_root_resumes _ _ _ _ _ _ _ _ _ nonnull
    (positive_vec_caller_invocation ambient capacity address nonzero outcome shim shimWorld resultWorld pointer
      positive bounded nonnull returned allocated)]
  rw [NativeAllocatorLLBC.legacy_done,positive_capacity_root_tail _ _ _ _ nonnull]
  rfl

theorem positive_capacity_decoded (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 = .value (.raw ⟨pointer,none⟩) resultWorld) :
    NativeAllocatorLLBC.invoke (positiveCapacityRoot ambient address outcome shim) ambient.world [.scalar (.usize capacity)] =
      .returned (positiveVecValue pointer capacity) resultWorld := by
  simpa [NativeAllocatorLLBC.invoke,decodeArgs,decode,NativeSliceLLBC.decodeInput] using
    positive_capacity_root_values ambient capacity address nonzero outcome shim shimWorld resultWorld pointer
      positive bounded nonnull returned allocated

theorem positive_capacity_reachable (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value)
    (reachable : NativeReferenceMachine.Reachable ambient.world)
    (returned : NativeAllocatorLLBC.invoke (positiveCapacityRoot ambient address outcome shim) ambient.world [.scalar (.usize capacity)] =
      .returned value world) : NativeReferenceMachine.Reachable world := by
  have result := NativeAllocatorLLBC.invoke_reachable (positiveCapacityRoot ambient address outcome shim) ambient.world
    [.scalar (.usize capacity)] reachable
  simpa only [returned,Flow.world] using result

end HasteBootsVecCapacityArithmetic
