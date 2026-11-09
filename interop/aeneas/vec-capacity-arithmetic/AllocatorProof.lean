namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

/-- The common implementation has an actual checked Layout/Boolean entry. -/
theorem implementation_initialized (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (zero positive : NativeAllocatorLLBC.Body) :
    initial (implementationFunction ambient zero positive).types 2 [capacityLayout capacity,.boolean zeroed] ambient.world =
      some (implementationFrame ambient capacity zeroed) := by
  simp [implementationFunction,implementationTypes,implementationFrame,initial,capacityLayout,byteAlignment,
    alignmentDiscriminants,layoutTypes,calleeEntryAmbient,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem implementation_prefix_exact (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool) (next : Body) :
    eval (implementationPrefix next) (implementationFrame ambient capacity zeroed) =
      eval next (implementationPrepared ambient capacity zeroed) := by
  simp [implementationPrefix,implementationFrame,implementationPrepared,implementationTypes,capacityLayout,
    byteAlignment,alignmentDiscriminants,layoutTypes,calleeEntryAmbient,eval,evalRvalue,evalOperand,
    storageLive,NativeRecordLLBC.read,write,retag,NativeSliceLLBC.retagValue,NativeRecordValues.typeAt,
    NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
    NativeRecordValues.copyable,NativeSliceLLBC.fits]

/-- Size dispatch reaches the positive source branch, preserving its outcome and
all following cleanup. No allocator success or shim result is assumed. -/
theorem implementation_positive (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (nonzero : capacity ≠ 0) (zero positive : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.eval (implementationFunction ambient zero positive).body (implementationFrame ambient capacity zeroed) =
      NativeAllocatorLLBC.continueWith (.legacy implementationTail .done)
        (NativeAllocatorLLBC.eval positive (implementationPrepared ambient capacity zeroed)) := by
  have selected : evalOperand (implementationPrepared ambient capacity zeroed) (.copy 3 []) =
      some (.scalar (.usize capacity),implementationPrepared ambient capacity zeroed) := by
    simp [evalOperand,implementationPrepared,implementationTypes,NativeRecordLLBC.read,NativeRecordValues.typeAt,
      NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
      NativeRecordValues.copyable,NativeSliceLLBC.fits]
  have prepared : eval (implementationPrefix .done) (implementationFrame ambient capacity zeroed) =
      .normal (implementationPrepared ambient capacity zeroed) := by
    rw [implementation_prefix_exact]
    rfl
  change NativeAllocatorLLBC.eval (.legacy (implementationPrefix .done)
    (.switchUsize (.copy 3 []) 0 zero positive (.legacy implementationTail .done)))
      (implementationFrame ambient capacity zeroed) = _
  rw [NativeAllocatorLLBC.legacy_normal _ prepared]
  exact NativeAllocatorLLBC.switch_usize_false 0 _ _ _ selected nonzero

theorem method_initialized (ambient : Frame) (reference : NativeReferenceMachine.Reference)
    (capacity : NativeWord64Memory.Word) (zeroed : Bool) (zero positive : NativeAllocatorLLBC.Body) :
    initial (allocationMethod ambient zeroed zero positive).types 2
      [.scalar (.reference false reference 0),capacityLayout capacity] ambient.world =
      some (allocationMethodFrame ambient reference capacity) := by
  simp [allocationMethod,allocationMethodTypes,allocationMethodFrame,initial,capacityLayout,byteAlignment,
    alignmentDiscriminants,layoutTypes,calleeEntryAmbient,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem method_arguments (ambient : Frame) (reference : NativeReferenceMachine.Reference)
    (capacity : NativeWord64Memory.Word) (zeroed : Bool) :
    evalArgs (allocationMethodPrepared ambient reference capacity) (allocationMethodArgs zeroed) =
      some ([capacityLayout capacity,.boolean zeroed],allocationMethodMoved ambient reference capacity) := by
  simp [allocationMethodPrepared,allocationMethodMoved,allocationMethodTypes,allocationMethodArgs,capacityLayout,byteAlignment,
    alignmentDiscriminants,layoutTypes,calleeEntryAmbient,evalArgs,evalOperand,NativeRecordLLBC.read,NativeRecordValues.typeAt,
    NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

/-- Both original wrappers forward the source Boolean into the common runtime
implementation. The equation covers every implementation outcome and heap change. -/
theorem method_body_forwarding (ambient : Frame) (reference : NativeReferenceMachine.Reference)
    (capacity : NativeWord64Memory.Word) (zeroed : Bool) (zero positive : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.eval (allocationMethod ambient zeroed zero positive).body (allocationMethodFrame ambient reference capacity) =
      NativeAllocatorLLBC.resume (allocationMethodMoved ambient reference capacity) 0
        (.legacy (.dead 2 (.dead 1 .resume)) .done) (.legacy (.dead 2 (.dead 1 .ret)) .done)
        (NativeAllocatorLLBC.invokeValues (implementationFunction ambient zero positive) ambient.world
          [capacityLayout capacity,.boolean zeroed]) := by
  have prepared : eval (.live 0 .done) (allocationMethodFrame ambient reference capacity) =
      .normal (allocationMethodPrepared ambient reference capacity) := by
    simp [eval,storageLive,allocationMethodFrame,allocationMethodPrepared]
  change NativeAllocatorLLBC.eval (.legacy (.live 0 .done)
    (.call (implementationFunction ambient zero positive).name (implementationFunction ambient zero positive).classification
      (implementationFunction ambient zero positive).types 2 0 (allocationMethodArgs zeroed)
      (implementationFunction ambient zero positive).body (.legacy (.dead 2 (.dead 1 .resume)) .done)
      (.legacy (.dead 2 (.dead 1 .ret)) .done))) (allocationMethodFrame ambient reference capacity) = _
  rw [NativeAllocatorLLBC.legacy_normal _ prepared]
  have called := NativeAllocatorLLBC.eval_call (implementationFunction ambient zero positive)
    (allocationMethodPrepared ambient reference capacity) 0 (allocationMethodArgs zeroed)
    (.legacy (.dead 2 (.dead 1 .resume)) .done) (.legacy (.dead 2 (.dead 1 .ret)) .done)
  rw [method_arguments] at called
  exact called

/-- An allocating implementation is forwarded without restricting its outcome. -/
theorem method_invocation_forwarding (ambient : Frame) (reference : NativeReferenceMachine.Reference)
    (capacity : NativeWord64Memory.Word) (zeroed : Bool) (zero positive : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.invokeValues (allocationMethod ambient zeroed zero positive) ambient.world
      [.scalar (.reference false reference 0),capacityLayout capacity] =
      settle ambient.world (NativeAllocatorLLBC.resume (allocationMethodMoved ambient reference capacity) 0
        (.legacy (.dead 2 (.dead 1 .resume)) .done) (.legacy (.dead 2 (.dead 1 .ret)) .done)
        (NativeAllocatorLLBC.invokeValues (implementationFunction ambient zero positive) ambient.world
          [capacityLayout capacity,.boolean zeroed])) := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (method_initialized ambient reference capacity zeroed zero positive),
    method_body_forwarding]
  rfl

theorem implementation_positive_invocation (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (nonzero : capacity ≠ 0) (zero positive : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.invokeValues (implementationFunction ambient zero positive) ambient.world
      [capacityLayout capacity,.boolean zeroed] =
      settle ambient.world (NativeAllocatorLLBC.continueWith (.legacy implementationTail .done)
        (NativeAllocatorLLBC.eval positive (implementationPrepared ambient capacity zeroed))) := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (implementation_initialized ambient capacity zeroed zero positive),
    implementation_positive _ _ _ nonzero]
  rfl

end HasteBootsVecCapacityArithmetic
