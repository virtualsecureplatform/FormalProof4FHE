namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example (ambient : Frame) (reference : NativeReferenceMachine.Reference) :
    NativeAllocatorLLBC.invokeValues (allocationMethod ambient false (.legacy (.unsupported "zero") .done)
      (.switchBoolean (.copy 2 []) (.legacy (.unsupported "zeroed allocation body") .done) (.legacy (.unsupported "ordinary allocation body") .done) .done)) ambient.world
      [.scalar (.reference false reference 0),capacityLayout 1] = .unsupported "ordinary allocation body" ambient.world := by
  rw [method_invocation_forwarding]
  rw [implementation_positive_invocation ambient 1 false (by decide)]
  rfl

example (ambient : Frame) (reference : NativeReferenceMachine.Reference) :
    NativeAllocatorLLBC.invokeValues (allocationMethod ambient true (.legacy (.unsupported "zero") .done)
      (.switchBoolean (.copy 2 []) (.legacy (.unsupported "zeroed allocation body") .done) (.legacy (.unsupported "ordinary allocation body") .done) .done)) ambient.world
      [.scalar (.reference false reference 0),capacityLayout ⟨9223372036854775807,by decide⟩] =
      .unsupported "zeroed allocation body" ambient.world := by
  rw [method_invocation_forwarding]
  rw [implementation_positive_invocation ambient ⟨9223372036854775807,by decide⟩ true (by decide)]
  rfl

example (ambient : Frame) (reference : NativeReferenceMachine.Reference) (zeroed : Bool) :
    NativeAllocatorLLBC.invokeValues (allocationMethod ambient zeroed (.legacy .abort .done) (.legacy .resume .done)) ambient.world
      [.scalar (.reference false reference 0),capacityLayout 1] = .unwind ambient.world := by
  rw [method_invocation_forwarding,implementation_positive_invocation ambient 1 zeroed (by decide)]
  rfl

example (ambient : Frame) (reference : NativeReferenceMachine.Reference) (zeroed : Bool) :
    NativeAllocatorLLBC.invokeValues (allocationMethod ambient zeroed (.legacy .resume .done) (.legacy .abort .done)) ambient.world
      [.scalar (.reference false reference 0),capacityLayout 1] = .invalid ambient.world := by
  rw [method_invocation_forwarding,implementation_positive_invocation ambient 1 zeroed (by decide)]
  rfl

example (ambient : Frame) (reference : NativeReferenceMachine.Reference) (capacity : NativeWord64Memory.Word) (zeroed : Bool) :
    evalArgs (allocationMethodPrepared ambient reference capacity) (allocationMethodArgs zeroed) =
      some ([capacityLayout capacity,.boolean zeroed],allocationMethodMoved ambient reference capacity) :=
  method_arguments ambient reference capacity zeroed

example (ambient : Frame) :
    NativeAllocatorLLBC.invokeValues (allocationMethod ambient false .done .done) ambient.world
      [.scalar (.reference true ⟨0⟩ 0),capacityLayout 1] = .invalid ambient.world := by
  simp [NativeAllocatorLLBC.invokeValues,allocationMethod,allocationMethodTypes,initial,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

example (ambient : Frame) :
    NativeAllocatorLLBC.invokeValues (allocationMethod ambient true .done .done) ambient.world [] = .invalid ambient.world := by
  simp [NativeAllocatorLLBC.invokeValues,allocationMethod,initial]

example (ambient : Frame) (zeroed : Bool) :
    NativeAllocatorLLBC.invokeValues (implementationFunction ambient (.legacy (.unsupported "size zero") .done) .done)
      ambient.world [capacityLayout 0,.boolean zeroed] = .unsupported "size zero" ambient.world := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (implementation_initialized ambient 0 zeroed _ _)]
  have prepared : eval (implementationPrefix .done) (implementationFrame ambient 0 zeroed) =
      .normal (implementationPrepared ambient 0 zeroed) := by rw [implementation_prefix_exact]; rfl
  change settle ambient.world (NativeAllocatorLLBC.eval (.legacy (implementationPrefix .done)
    (.switchUsize (.copy 3 []) 0 (.legacy (.unsupported "size zero") .done) .done (.legacy implementationTail .done)))
      (implementationFrame ambient 0 zeroed)) = _
  rw [NativeAllocatorLLBC.legacy_normal _ prepared]
  simp [NativeAllocatorLLBC.eval,evalOperand,implementationPrepared,implementationTypes,NativeRecordLLBC.read,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits,eval,settle]
end HasteBootsVecCapacityArithmetic
