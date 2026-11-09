namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
private def sharedCallerBorrowed : NativeReferenceMachine.State := NativeZstBorrow.granted NativeReferenceMachine.empty 64
private def sharedCallerAllocated : NativeReferenceMachine.State := NativeAllocatorExecution.allocated sharedCallerBorrowed 8 ⟨3,1⟩

example (ambient : Frame) (shim : NativeAllocatorLLBC.Body)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) sharedCallerBorrowed [] = .returned (.scalar .unit) sharedCallerBorrowed) :
    NativeAllocatorLLBC.invoke (unifiedCapacityRoot {ambient with world := NativeReferenceMachine.empty} 64 (some 8) shim)
      NativeReferenceMachine.empty [.scalar (.usize 3)] = .returned (positiveVecValue ⟨8,some ⟨8,0⟩⟩ 3) sharedCallerAllocated :=
  unified_capacity_decoded _ 3 64 (by decide) (some 8) shim _ _ _ (by decide) (by decide) (by decide) returned (by decide)

example : NativeByteRange.loadRange sharedCallerAllocated.pointers.heap.memory ⟨8,some ⟨8,0⟩⟩ ⟨3,1⟩ = none := by decide

example (ambient : Frame) (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0) :
    eval (rawCallerTail (.unsupported "error") (.unsupported "cold")) (positiveRawCallerReturned ambient 3 world pointer) =
      .returned (positiveRawValue pointer 3) world := positive_raw_caller_tail ambient 3 world pointer nonnull _ _

example (ambient : Frame) (shim : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State)
    (value : NativeRecordValues.Value) (reachable : NativeReferenceMachine.Reachable ambient.world)
    (returned : NativeAllocatorLLBC.invoke (unifiedCapacityRoot ambient 64 (some 8) shim) ambient.world [.scalar (.usize 3)] =
      .returned value world) : NativeReferenceMachine.Reachable world :=
  unified_capacity_reachable ambient 3 64 (some 8) shim world value reachable returned

example (ambient : Frame) :
    NativeAllocatorLLBC.invoke (unifiedCapacityRoot ambient 0 (some 0) (.legacy (.unsupported "unused shim") .done))
      ambient.world [.scalar (.usize 0)] = .returned zeroVecValue ambient.world :=
  unified_capacity_zero_decoded ambient 0 (some 0) _

example (ambient : Frame) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.invokeValues (unifiedRawCallerFunction ambient address outcome shim) ambient.world
      [.scalar (.usize 0),allocatorValue,byteLayout] = .returned zeroRawValue ambient.world :=
  unified_raw_caller_zero ambient address outcome shim

example (ambient : Frame) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.invokeValues (unifiedVecCallerFunction ambient address outcome shim) ambient.world
      [.scalar (.usize 0)] = .returned zeroVecValue ambient.world :=
  unified_vec_caller_zero ambient address outcome shim

end HasteBootsVecCapacityArithmetic
