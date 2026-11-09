namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def inactiveUnwindFrame : Frame :=
  ⟨(List.replicate 54 (.scalar .unit)).set 21 .boolean,
    (List.replicate 54 .dead).set 21 (.live (some (.boolean false))),NativeReferenceMachine.empty⟩

example : NativeAllocatorLLBC.eval (constructorUnwind 0) inactiveUnwindFrame = .unwind NativeReferenceMachine.empty :=
  constructor_unwind_skip inactiveUnwindFrame 0 (by decide) (by decide)

private def unifiedBorrowed : NativeReferenceMachine.State := NativeZstBorrow.granted NativeReferenceMachine.empty 64
private def unifiedDropped : NativeReferenceMachine.State := NativeZstBorrow.grantedExclusive unifiedBorrowed 64

example (ambient : Frame) :
    NativeAllocatorLLBC.eval (constructorUnwind 64) (positiveMovedFrame {ambient with world := NativeReferenceMachine.empty} 3 false 64) =
      .unwind unifiedDropped :=
  positive_constructor_unwind_entry _ 3 false 64 (by decide) unifiedBorrowed
    (NativeReferenceMachine.reachable_wellFormed _ (NativeZstBorrow.granted_reachable _ 64 (by decide) .empty))

example (ambient : Frame) :
    NativeAllocatorLLBC.eval (constructorUnwind 64) (positiveMovedFrame {ambient with world := NativeReferenceMachine.empty} 3 true 64) =
      .unwind unifiedDropped :=
  positive_constructor_unwind_entry _ 3 true 64 (by decide) unifiedBorrowed
    (NativeReferenceMachine.reachable_wellFormed _ (NativeZstBorrow.granted_reachable _ 64 (by decide) .empty))

example : eval constructorUnwindTerminate inactiveUnwindFrame = .invalid NativeReferenceMachine.empty :=
  constructor_unwind_terminate inactiveUnwindFrame (by decide)

example : unifiedDropped.pointers.heap = NativeReferenceMachine.empty.pointers.heap := rfl

example (ambient : Frame) : NativeAllocatorLLBC.invokeValues
    (unifiedConstructorFunction ambient false 0 (some 0) (.legacy (.unsupported "unused shim") .done)) ambient.world
    [.scalar (.usize 0),allocationModeValue false,allocatorValue,byteLayout] = .returned zeroResultValue ambient.world :=
  unified_constructor_zero ambient false 0 (some 0) _

example (ambient : Frame) : NativeAllocatorLLBC.invokeValues
    (unifiedConstructorFunction ambient true 0 none (.legacy (.unsupported "unused shim") .done)) ambient.world
    [.scalar (.usize 0),allocationModeValue true,allocatorValue,byteLayout] = .returned zeroResultValue ambient.world :=
  unified_constructor_zero ambient true 0 none _

example (ambient : Frame) (shim : NativeAllocatorLLBC.Body)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) unifiedBorrowed [] = .returned (.scalar .unit) unifiedBorrowed) :
    NativeAllocatorLLBC.invokeValues
      (unifiedConstructorFunction {ambient with world := NativeReferenceMachine.empty} false 64 (some 8) shim)
      NativeReferenceMachine.empty [.scalar (.usize 3),allocationModeValue false,allocatorValue,byteLayout] =
      .returned (positiveResultValue ⟨8,some ⟨8,0⟩⟩ 3) (NativeAllocatorExecution.allocated unifiedBorrowed 8 ⟨3,1⟩) :=
  unified_constructor_success _ 3 false 64 (by decide) (some 8) shim _ _ _ (by decide) (by decide) (by decide)
    returned (by decide)

example (ambient : Frame) (shim : NativeAllocatorLLBC.Body)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) unifiedBorrowed [] = .returned (.scalar .unit) unifiedBorrowed) :
    NativeAllocatorLLBC.invokeValues
      (unifiedConstructorFunction {ambient with world := NativeReferenceMachine.empty} true 64 none shim)
      NativeReferenceMachine.empty [.scalar (.usize 3),allocationModeValue true,allocatorValue,byteLayout] =
      .returned (constructorErrorValue 3) unifiedDropped :=
  unified_constructor_failure _ 3 true 64 (by decide) shim _ (NativeReferenceMachine.reachable_wellFormed _ .empty)
    (by decide) (by decide) returned

example (ambient : Frame) : NativeAllocatorLLBC.invokeValues
    (unifiedConstructorFunction {ambient with world := NativeReferenceMachine.empty} false 64 (some 0) (.legacy (.unsupported "unused shim") .done))
    NativeReferenceMachine.empty [.scalar (.usize (2^63)),allocationModeValue false,allocatorValue,byteLayout] =
    .returned capacityOverflowValue (NativeZstBorrow.grantedExclusive NativeReferenceMachine.empty 64) :=
  unified_constructor_rejected _ (2^63) false 64 (by decide) (some 0) _ (by decide)
    (NativeReferenceMachine.reachable_wellFormed _ .empty)

end HasteBootsVecCapacityArithmetic
