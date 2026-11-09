namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem unified_raw_caller_resumes (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim unwind next : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (unifiedConstructorFunction ambient false address outcome shim) ambient.world
      [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] = .returned (positiveResultValue pointer capacity) world) :
    NativeAllocatorLLBC.eval (unifiedRawCallerCall ambient address outcome shim unwind next) (rawCallerFrame ambient capacity) =
      NativeAllocatorLLBC.eval next (positiveRawCallerReturned ambient capacity world pointer) := by
  have prepared : eval (rawCallerPrefix .done) (rawCallerFrame ambient capacity) = .normal (rawCallerPrepared ambient capacity) := by
    rw [raw_caller_prefix_exact]; rfl
  rw [unifiedRawCallerCall,NativeAllocatorLLBC.legacy_normal _ prepared]
  have called := NativeAllocatorLLBC.eval_call (unifiedConstructorFunction ambient false address outcome shim)
    (rawCallerPrepared ambient capacity) 4 rawCallerArgs unwind next
  rw [raw_caller_arguments] at called
  simp only at called
  rw [show (rawCallerMoved ambient capacity).world = ambient.world from rfl,returned] at called
  rw [called]
  simp [NativeAllocatorLLBC.resume,positiveRawCallerReturned,write,rawCallerMoved,rawCallerTypes,layoutTypes,calleeEntryAmbient,
    positiveResultValue,positiveRawValue,runtimeThinValue,allocatorValue,nonnull,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem unified_raw_caller_initialized (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    initial (unifiedRawCallerFunction ambient address outcome shim).types 3 [.scalar (.usize capacity),allocatorValue,byteLayout] ambient.world =
      some (rawCallerFrame (rawEntryAmbient ambient) capacity) := by
  simp [unifiedRawCallerFunction,rawEntryAmbient,rawCallerFrame,rawCallerTypes,initial,layoutTypes,calleeEntryAmbient,
    allocatorValue,byteLayout,byteAlignment,alignmentDiscriminants,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits,List.replicate_succ]

theorem unified_vec_caller_resumes (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim unwind next : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (unifiedRawCallerFunction ambient address outcome shim) ambient.world
      [.scalar (.usize capacity),allocatorValue,byteLayout] = .returned (positiveRawValue pointer capacity) world) :
    NativeAllocatorLLBC.eval (unifiedVecCallerCall ambient address outcome shim unwind next) (vecCallerFrame ambient capacity) =
      NativeAllocatorLLBC.eval next (positiveVecCallerReturned ambient capacity world pointer) := by
  have prepared : eval (vecCallerPrefix .done) (vecCallerFrame ambient capacity) = .normal (vecCallerPrepared ambient capacity) := by
    rw [vec_caller_prefix_exact]; rfl
  rw [unifiedVecCallerCall,NativeAllocatorLLBC.legacy_normal _ prepared]
  have called := NativeAllocatorLLBC.eval_call (unifiedRawCallerFunction ambient address outcome shim)
    (vecCallerPrepared ambient capacity) 3 vecCallerArgs unwind next
  rw [vec_caller_arguments] at called
  simp only at called
  rw [show (vecCallerMoved ambient capacity).world = ambient.world from rfl,returned] at called
  rw [called]
  simp [NativeAllocatorLLBC.resume,positiveVecCallerReturned,write,vecCallerMoved,vecCallerTypes,layoutTypes,calleeEntryAmbient,
    positiveRawValue,runtimeThinValue,allocatorValue,nonnull,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem unified_vec_caller_initialized (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    initial (unifiedVecCallerFunction ambient address outcome shim).types 1 [.scalar (.usize capacity)] ambient.world =
      some (vecCallerFrame ambient capacity) := by
  simp [unifiedVecCallerFunction,vecCallerFrame,vecCallerTypes,initial,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem unified_capacity_root_resumes (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim unwind next : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (unifiedVecCallerFunction ambient address outcome shim) ambient.world
      [.scalar (.usize capacity)] = .returned (positiveVecValue pointer capacity) world) :
    NativeAllocatorLLBC.eval (unifiedCapacityRootCall ambient address outcome shim unwind next) (capacityRootFrame ambient capacity) =
      NativeAllocatorLLBC.eval next (positiveCapacityRootReturned ambient capacity world pointer) := by
  have prepared : eval (capacityRootPrefix .done) (capacityRootFrame ambient capacity) = .normal (capacityRootPrepared ambient capacity) := by
    rw [capacity_root_prefix]; rfl
  rw [unifiedCapacityRootCall,NativeAllocatorLLBC.legacy_normal _ prepared]
  have called := NativeAllocatorLLBC.eval_call (unifiedVecCallerFunction ambient address outcome shim)
    (capacityRootPrepared ambient capacity) 0 [.move 2 []] unwind next
  rw [capacity_root_arguments] at called
  simp only at called
  rw [show (capacityRootMoved ambient capacity).world = ambient.world from rfl,returned] at called
  rw [called]
  simp [NativeAllocatorLLBC.resume,positiveCapacityRootReturned,write,capacityRootMoved,capacityRootTypes,vecCallerTypes,
    layoutTypes,calleeEntryAmbient,positiveVecValue,positiveRawValue,runtimeThinValue,allocatorValue,nonnull,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem unified_capacity_root_initialized (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    initial (unifiedCapacityRoot ambient address outcome shim).types 1 [.scalar (.usize capacity)] ambient.world =
      some (capacityRootFrame ambient capacity) := by
  simp [unifiedCapacityRoot,capacityRootTypes,capacityRootFrame,initial,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem unified_raw_caller_invocation (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 = .value (.raw ⟨pointer,none⟩) resultWorld) :
    NativeAllocatorLLBC.invokeValues (unifiedRawCallerFunction ambient address outcome shim) ambient.world
      [.scalar (.usize capacity),allocatorValue,byteLayout] = .returned (positiveRawValue pointer capacity) resultWorld := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (unified_raw_caller_initialized ambient capacity address outcome shim)]
  change settle ambient.world (NativeAllocatorLLBC.eval (unifiedRawCallerCall (rawEntryAmbient ambient) address outcome shim _ _)
    (rawCallerFrame (rawEntryAmbient ambient) capacity)) = _
  rw [unified_raw_caller_resumes _ _ _ _ _ _ _ _ _ nonnull
    (unified_constructor_success (rawEntryAmbient ambient) capacity false address nonzero outcome shim shimWorld resultWorld pointer
      positive bounded nonnull returned allocated)]
  rw [NativeAllocatorLLBC.legacy_done,positive_raw_caller_tail _ _ _ _ nonnull]
  rfl

theorem unified_vec_caller_invocation (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 = .value (.raw ⟨pointer,none⟩) resultWorld) :
    NativeAllocatorLLBC.invokeValues (unifiedVecCallerFunction ambient address outcome shim) ambient.world [.scalar (.usize capacity)] =
      .returned (positiveVecValue pointer capacity) resultWorld := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (unified_vec_caller_initialized ambient capacity address outcome shim)]
  change settle ambient.world (NativeAllocatorLLBC.eval (unifiedVecCallerCall ambient address outcome shim _ _)
    (vecCallerFrame ambient capacity)) = _
  rw [unified_vec_caller_resumes _ _ _ _ _ _ _ _ _ nonnull
    (unified_raw_caller_invocation ambient capacity address nonzero outcome shim shimWorld resultWorld pointer
      positive bounded nonnull returned allocated)]
  rw [NativeAllocatorLLBC.legacy_done,positive_vec_caller_tail _ _ _ _ nonnull]
  rfl

theorem unified_capacity_root_values (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 = .value (.raw ⟨pointer,none⟩) resultWorld) :
    NativeAllocatorLLBC.invokeValues (unifiedCapacityRoot ambient address outcome shim) ambient.world [.scalar (.usize capacity)] =
      .returned (positiveVecValue pointer capacity) resultWorld := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (unified_capacity_root_initialized ambient capacity address outcome shim)]
  change settle ambient.world (NativeAllocatorLLBC.eval (unifiedCapacityRootCall ambient address outcome shim _ _)
    (capacityRootFrame ambient capacity)) = _
  rw [unified_capacity_root_resumes _ _ _ _ _ _ _ _ _ nonnull
    (unified_vec_caller_invocation ambient capacity address nonzero outcome shim shimWorld resultWorld pointer
      positive bounded nonnull returned allocated)]
  rw [NativeAllocatorLLBC.legacy_done,positive_capacity_root_tail _ _ _ _ nonnull]
  rfl

theorem unified_capacity_decoded (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 = .value (.raw ⟨pointer,none⟩) resultWorld) :
    NativeAllocatorLLBC.invoke (unifiedCapacityRoot ambient address outcome shim) ambient.world [.scalar (.usize capacity)] =
      .returned (positiveVecValue pointer capacity) resultWorld := by
  simpa [NativeAllocatorLLBC.invoke,decodeArgs,decode,NativeSliceLLBC.decodeInput] using
    unified_capacity_root_values ambient capacity address nonzero outcome shim shimWorld resultWorld pointer
      positive bounded nonnull returned allocated

theorem unified_capacity_reachable (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value)
    (reachable : NativeReferenceMachine.Reachable ambient.world)
    (returned : NativeAllocatorLLBC.invoke (unifiedCapacityRoot ambient address outcome shim) ambient.world [.scalar (.usize capacity)] =
      .returned value world) : NativeReferenceMachine.Reachable world := by
  have result := NativeAllocatorLLBC.invoke_reachable (unifiedCapacityRoot ambient address outcome shim) ambient.world
    [.scalar (.usize capacity)] reachable
  simpa only [returned,Flow.world] using result

theorem unified_raw_caller_zero (ambient : Frame) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.invokeValues (unifiedRawCallerFunction ambient address outcome shim) ambient.world
      [.scalar (.usize 0),allocatorValue,byteLayout] = .returned zeroRawValue ambient.world := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (unified_raw_caller_initialized ambient 0 address outcome shim)]
  change settle ambient.world (NativeAllocatorLLBC.eval (unifiedRawCallerCall (rawEntryAmbient ambient) address outcome shim _ _)
    (rawCallerFrame (rawEntryAmbient ambient) 0)) = _
  have returned : NativeAllocatorLLBC.invokeValues
      (unifiedConstructorFunction (rawEntryAmbient ambient) false address outcome shim) ambient.world
      [.scalar (.usize 0),uninitializedValue,allocatorValue,byteLayout] =
      .returned (positiveResultValue ⟨1,none⟩ 0) ambient.world :=
    unified_constructor_zero (rawEntryAmbient ambient) false address outcome shim
  rw [unified_raw_caller_resumes _ _ _ _ _ _ _ _ _ (by decide) returned,
    NativeAllocatorLLBC.legacy_done,positive_raw_caller_tail _ _ _ _ (by decide)]
  rfl

theorem unified_vec_caller_zero (ambient : Frame) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.invokeValues (unifiedVecCallerFunction ambient address outcome shim) ambient.world
      [.scalar (.usize 0)] = .returned zeroVecValue ambient.world := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (unified_vec_caller_initialized ambient 0 address outcome shim)]
  change settle ambient.world (NativeAllocatorLLBC.eval (unifiedVecCallerCall ambient address outcome shim _ _)
    (vecCallerFrame ambient 0)) = _
  have returned : NativeAllocatorLLBC.invokeValues (unifiedRawCallerFunction ambient address outcome shim) ambient.world
      [.scalar (.usize 0),allocatorValue,byteLayout] = .returned (positiveRawValue ⟨1,none⟩ 0) ambient.world :=
    unified_raw_caller_zero ambient address outcome shim
  rw [unified_vec_caller_resumes _ _ _ _ _ _ _ _ _ (by decide) returned,
    NativeAllocatorLLBC.legacy_done,positive_vec_caller_tail _ _ _ _ (by decide)]
  rfl

theorem unified_capacity_root_zero_values (ambient : Frame) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.invokeValues (unifiedCapacityRoot ambient address outcome shim) ambient.world
      [.scalar (.usize 0)] = .returned zeroVecValue ambient.world := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (unified_capacity_root_initialized ambient 0 address outcome shim)]
  change settle ambient.world (NativeAllocatorLLBC.eval (unifiedCapacityRootCall ambient address outcome shim _ _)
    (capacityRootFrame ambient 0)) = _
  have returned : NativeAllocatorLLBC.invokeValues (unifiedVecCallerFunction ambient address outcome shim) ambient.world
      [.scalar (.usize 0)] = .returned (positiveVecValue ⟨1,none⟩ 0) ambient.world :=
    unified_vec_caller_zero ambient address outcome shim
  rw [unified_capacity_root_resumes _ _ _ _ _ _ _ _ _ (by decide) returned,
    NativeAllocatorLLBC.legacy_done,positive_capacity_root_tail _ _ _ _ (by decide)]
  rfl

theorem unified_capacity_zero_decoded (ambient : Frame) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.invoke (unifiedCapacityRoot ambient address outcome shim) ambient.world
      [.scalar (.usize 0)] = .returned zeroVecValue ambient.world := by
  simpa [NativeAllocatorLLBC.invoke,decodeArgs,decode,NativeSliceLLBC.decodeInput] using
    unified_capacity_root_zero_values ambient address outcome shim

end HasteBootsVecCapacityArithmetic
