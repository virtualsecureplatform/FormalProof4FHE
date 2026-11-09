namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) :
    evalArgs (runtimeAlignmentFrame ambient capacity zeroed world) (runtimeAllocatorArgs zeroed) =
      some ([.scalar (.usize capacity),byteAlignment],runtimeArgumentsFrame ambient capacity zeroed world) :=
  runtime_allocator_arguments ambient capacity zeroed world

example (ambient : Frame) (world : NativeReferenceMachine.State) (null nonnull : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.eval (runtimePointerDispatch null nonnull) (runtimeAllocatedFrame ambient 3 false world ⟨0,none⟩) =
      NativeAllocatorLLBC.eval null (runtimeInspectedFrame ambient 3 false world ⟨0,none⟩) := by
  rw [runtime_pointer_dispatch]; rfl

example (ambient : Frame) (world : NativeReferenceMachine.State) (null nonnull : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.eval (runtimePointerDispatch null nonnull) (runtimeAllocatedFrame ambient 3 true world ⟨8,some ⟨8,0⟩⟩) =
      NativeAllocatorLLBC.eval nonnull (runtimeInspectedFrame ambient 3 true world ⟨8,some ⟨8,0⟩⟩) := by
  rw [runtime_pointer_dispatch]; rfl

example (ambient : Frame) (world : NativeReferenceMachine.State) :
    (runtimeInspectedFrame ambient 3 false world ⟨8,some ⟨8,0⟩⟩).slots[6]? =
      some (.live (some (.scalar (.raw ⟨⟨8,some ⟨8,0⟩⟩,none⟩)))) := rfl

example (ambient : Frame) (world : NativeReferenceMachine.State) :
    (runtimeInspectedFrame ambient 3 true world ⟨8,some ⟨8,0⟩⟩).slots[23]? =
      some (.live (some (.scalar (.usize 8)))) := rfl

example (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (outcome : Option NativePointerStorage.Address) (shim null nonnull : NativeAllocatorLLBC.Body)
    (world : NativeReferenceMachine.State) (label : String)
    (blocked : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .unsupported label world) :
    NativeAllocatorLLBC.eval (runtimePositive outcome shim null nonnull) (implementationPrepared ambient capacity zeroed) =
      .unsupported label world := runtime_shim_unsupported ambient capacity zeroed outcome shim null nonnull label world blocked

example (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (world : NativeReferenceMachine.State)
    (unwound : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .unwind world) :
    NativeAllocatorLLBC.eval (runtimeCallBranch zeroed outcome shim) (implementationPrepared ambient capacity zeroed) =
      .invalid world := runtime_shim_unwind_aborts ambient capacity zeroed outcome shim world unwound

end HasteBootsVecCapacityArithmetic
