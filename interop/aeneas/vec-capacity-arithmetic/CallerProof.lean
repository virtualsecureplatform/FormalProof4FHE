namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

/-- The source initializes the allocation mode before evaluating call arguments. -/
theorem raw_caller_prefix_exact (ambient : Frame) (capacity : NativeWord64Memory.Word) (next : Body) :
    eval (rawCallerPrefix next) (rawCallerFrame ambient capacity) = eval next (rawCallerPrepared ambient capacity) := by
  simp [rawCallerPrefix,rawCallerFrame,rawCallerPrepared,rawCallerTypes,allocationInitType,uninitializedValue,
    eval,storageLive,evalRvalue,evalArgs,write,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem raw_caller_arguments (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    evalArgs (rawCallerPrepared ambient capacity) rawCallerArgs =
      some ([.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout],rawCallerMoved ambient capacity) := by
  simp [rawCallerArgs,rawCallerPrepared,rawCallerMoved,rawCallerTypes,layoutTypes,calleeEntryAmbient,allocationInitType,uninitializedValue,
    byteLayout,byteAlignment,alignmentDiscriminants,allocatorValue,evalArgs,evalOperand,NativeRecordLLBC.read,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem callee_initialized (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    initial (zeroCallee ambient).types 4 [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] ambient.world =
      some (layoutFrame (calleeEntryAmbient ambient) capacity) := by
  simp [zeroCallee,initial,layoutFrame,layoutTypes,calleeEntryAmbient,allocationInitType,uninitializedValue,
    allocatorValue,byteLayout,byteAlignment,alignmentDiscriminants,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits,List.replicate_succ]

theorem zero_callee_body (ambient : Frame) :
    eval (zeroCallee ambient).body (layoutFrame (calleeEntryAmbient ambient) 0) = .returned zeroResultValue ambient.world := by
  exact zero_capacity_return (calleeEntryAmbient ambient) rfl _ _ _ _

theorem zero_callee_invocation (ambient : Frame) :
    NativeRecordCallValues.invokeValues (zeroCallee ambient) ambient.world
      [.scalar (.usize 0),uninitializedValue,allocatorValue,byteLayout] = .returned zeroResultValue ambient.world := by
  rw [NativeRecordCallValues.invokeValues_initialized _ _ _ _ (callee_initialized ambient 0),zero_callee_body]
  rfl

theorem raw_caller_resumes (ambient : Frame) (unwind next : Body) :
    eval (rawCallerCall ambient unwind next) (rawCallerFrame ambient 0) =
      eval next (rawCallerReturned ambient 0) := by
  rw [rawCallerCall,raw_caller_prefix_exact,NativeRecordCallValues.eval_call,raw_caller_arguments]
  change NativeRecordCallValues.resume (rawCallerMoved ambient 0) 4 unwind next
    (NativeRecordCallValues.invokeValues (zeroCallee ambient) ambient.world
      [.scalar (.usize 0),uninitializedValue,allocatorValue,byteLayout]) = _
  rw [zero_callee_invocation]
  simp [NativeRecordCallValues.resume,write,rawCallerMoved,rawCallerReturned,rawCallerTypes,
    layoutTypes,calleeEntryAmbient,zeroResultValue,zeroRawValue,allocatorValue,alignmentDiscriminants,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem raw_caller_tail_exact (ambient : Frame) (error cold : Body) :
    eval (rawCallerTail error cold) (rawCallerReturned ambient 0) = .returned zeroRawValue ambient.world := by
  simp [rawCallerTail,rawCallerReturned,rawCallerTypes,layoutTypes,calleeEntryAmbient,zeroResultValue,zeroRawValue,
    allocatorValue,byteLayout,byteAlignment,alignmentDiscriminants,expr_wrappingSubtract,expr_greater,expr_logicalNot,
    eval,evalRvalue,evalArithmetic,evalBooleanOperand,evalArgs,evalOperand,selectChoice,storageLive,storageDead,
    NativeRecordLLBC.read,write,retag,NativeSliceLLBC.retagValue,NativeRecordValues.sideAt,NativeRecordValues.typeAt,
    NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits,NativeRecordArithmetic.eval]

theorem raw_caller_zero_return (ambient : Frame) (unwind error cold : Body) :
    eval (rawCallerCall ambient unwind (rawCallerTail error cold)) (rawCallerFrame ambient 0) =
      .returned zeroRawValue ambient.world := by
  rw [raw_caller_resumes,raw_caller_tail_exact]

theorem raw_zero_initialized (ambient : Frame) :
    initial (rawZeroFunction ambient).types 3 [.scalar (.usize 0),allocatorValue,byteLayout] ambient.world =
      some (rawCallerFrame (rawEntryAmbient ambient) 0) := by
  simp [rawZeroFunction,rawEntryAmbient,rawCallerFrame,rawCallerTypes,initial,layoutTypes,calleeEntryAmbient,
    allocatorValue,byteLayout,byteAlignment,alignmentDiscriminants,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits,List.replicate_succ]

theorem raw_zero_invocation (ambient : Frame) :
    NativeRecordCallValues.invokeValues (rawZeroFunction ambient) ambient.world
      [.scalar (.usize 0),allocatorValue,byteLayout] = .returned zeroRawValue ambient.world := by
  rw [NativeRecordCallValues.invokeValues_initialized _ _ _ _ (raw_zero_initialized ambient)]
  rw [show (rawZeroFunction ambient).body = rawCallerCall (rawEntryAmbient ambient)
    (.unsupported "source raw caller unwind") (rawCallerTail (.unsupported "source reservation error arm")
      (.unsupported "source cold helper")) from rfl,raw_caller_zero_return]
  rfl

theorem vec_caller_prefix_exact (ambient : Frame) (capacity : NativeWord64Memory.Word) (next : Body) :
    eval (vecCallerPrefix next) (vecCallerFrame ambient capacity) = eval next (vecCallerPrepared ambient capacity) := by
  simp [vecCallerPrefix,vecCallerFrame,vecCallerPrepared,vecCallerTypes,allocatorValue,eval,evalRvalue,
    evalArgs,storageLive,write,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem vec_caller_arguments (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    evalArgs (vecCallerPrepared ambient capacity) vecCallerArgs =
      some ([.scalar (.usize capacity),allocatorValue,byteLayout],vecCallerMoved ambient capacity) := by
  simp [vecCallerArgs,vecCallerPrepared,vecCallerMoved,vecCallerTypes,allocatorValue,byteLayout,byteAlignment,
    evalArgs,evalOperand,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.replace,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
    NativeSliceLLBC.fits]

theorem vec_caller_resumes (ambient : Frame) (unwind next : Body) :
    eval (vecCallerCall ambient unwind next) (vecCallerFrame ambient 0) = eval next (vecCallerReturned ambient 0) := by
  rw [vecCallerCall,vec_caller_prefix_exact,NativeRecordCallValues.eval_call,vec_caller_arguments]
  change NativeRecordCallValues.resume (vecCallerMoved ambient 0) 3 unwind next
    (NativeRecordCallValues.invokeValues (rawZeroFunction ambient) ambient.world [.scalar (.usize 0),allocatorValue,byteLayout]) = _
  rw [raw_zero_invocation]
  simp [NativeRecordCallValues.resume,write,vecCallerMoved,vecCallerReturned,vecCallerTypes,zeroRawValue,allocatorValue,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,layoutTypes,
    calleeEntryAmbient,alignmentDiscriminants]

theorem vec_caller_tail_exact (ambient : Frame) :
    eval vecCallerTail (vecCallerReturned ambient 0) = .returned zeroVecValue ambient.world := by
  simp [vecCallerTail,vecCallerReturned,vecCallerTypes,zeroVecValue,zeroRawValue,allocatorValue,layoutTypes,calleeEntryAmbient,
    alignmentDiscriminants,eval,evalRvalue,evalArgs,evalOperand,storageLive,storageDead,NativeRecordLLBC.read,write,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem vec_zero_initialized (ambient : Frame) :
    initial (vecZeroFunction ambient).types 1 [.scalar (.usize 0)] ambient.world = some (vecCallerFrame ambient 0) := by
  simp [vecZeroFunction,vecCallerFrame,vecCallerTypes,initial,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

/-- Source Global construction, argument moves, checked call entries, both
success returns and Vec field construction compose without an allocator premise. -/
theorem vec_zero_invocation (ambient : Frame) :
    NativeRecordCallValues.invokeValues (vecZeroFunction ambient) ambient.world [.scalar (.usize 0)] =
      .returned zeroVecValue ambient.world := by
  rw [NativeRecordCallValues.invokeValues_initialized _ _ _ _ (vec_zero_initialized ambient)]
  rw [show (vecZeroFunction ambient).body = vecCallerCall ambient (.unsupported "source Vec caller unwind") vecCallerTail from rfl,
    vec_caller_resumes,vec_caller_tail_exact]
  rfl

theorem capacity_root_prefix (ambient : Frame) (capacity : NativeWord64Memory.Word) (next : Body) :
    eval (capacityRootPrefix next) (capacityRootFrame ambient capacity) = eval next (capacityRootPrepared ambient capacity) := by
  simp [capacityRootPrefix,capacityRootFrame,capacityRootPrepared,capacityRootTypes,eval,evalRvalue,evalOperand,
    storageLive,NativeRecordLLBC.read,write,retag,NativeSliceLLBC.retagValue,NativeRecordValues.typeAt,
    NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
    NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem capacity_root_arguments (ambient : Frame) (capacity : NativeWord64Memory.Word) :
    evalArgs (capacityRootPrepared ambient capacity) [.move 2 []] =
      some ([.scalar (.usize capacity)],capacityRootMoved ambient capacity) := by
  simp [capacityRootPrepared,capacityRootMoved,capacityRootTypes,evalArgs,evalOperand,NativeRecordLLBC.read,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem capacity_root_resumes (ambient : Frame) (unwind next : Body) :
    eval (capacityRootCall ambient unwind next) (capacityRootFrame ambient 0) = eval next (capacityRootReturned ambient 0) := by
  rw [capacityRootCall,capacity_root_prefix,NativeRecordCallValues.eval_call,capacity_root_arguments]
  change NativeRecordCallValues.resume (capacityRootMoved ambient 0) 0 unwind next
    (NativeRecordCallValues.invokeValues (vecZeroFunction ambient) ambient.world [.scalar (.usize 0)]) = _
  rw [vec_zero_invocation]
  simp [NativeRecordCallValues.resume,write,capacityRootMoved,capacityRootReturned,capacityRootTypes,vecCallerTypes,
    layoutTypes,calleeEntryAmbient,zeroVecValue,zeroRawValue,allocatorValue,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem capacity_root_tail (ambient : Frame) :
    eval capacityRootTail (capacityRootReturned ambient 0) = .returned zeroVecValue ambient.world := by
  simp [capacityRootTail,capacityRootReturned,capacityRootTypes,vecCallerTypes,layoutTypes,calleeEntryAmbient,
    zeroVecValue,zeroRawValue,allocatorValue,eval,storageDead,NativeRecordLLBC.read,NativeRecordValues.typeAt,
    NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem capacity_root_initialized (ambient : Frame) :
    initial (capacityZeroRoot ambient).types 1 [.scalar (.usize 0)] ambient.world = some (capacityRootFrame ambient 0) := by
  simp [capacityZeroRoot,capacityRootTypes,capacityRootFrame,initial,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem capacity_root_values (ambient : Frame) :
    NativeRecordCallValues.invokeValues (capacityZeroRoot ambient) ambient.world [.scalar (.usize 0)] =
      .returned zeroVecValue ambient.world := by
  rw [NativeRecordCallValues.invokeValues_initialized _ _ _ _ (capacity_root_initialized ambient)]
  rw [show (capacityZeroRoot ambient).body = capacityRootCall ambient (.unsupported "source root unwind") capacityRootTail from rfl,
    capacity_root_resumes,capacity_root_tail]
  rfl

/-- The decoded source root constructs and passes Global itself, then executes
all four source bodies on the zero-capacity path over an arbitrary world. -/
theorem capacity_zero_root (ambient : Frame) :
    invoke (capacityZeroRoot ambient) ambient.world [.scalar (.usize 0)] = .returned zeroVecValue ambient.world := by
  rw [NativeRecordCallValues.invoke_eq]
  simpa [decodeArgs,decode,NativeSliceLLBC.decodeInput] using capacity_root_values ambient

end HasteBootsVecCapacityArithmetic
