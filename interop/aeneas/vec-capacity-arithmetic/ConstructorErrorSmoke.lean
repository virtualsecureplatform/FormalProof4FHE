namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (valid : NativeReferenceMachine.WellFormed world) :
    NativeAllocatorLLBC.invokeValues globalDropFunction world [.scalar (.reference true reference 0)] =
      .returned (.scalar .unit) world := global_drop_values world reference valid

example : NativeRecordValues.get (constructorErrorValue 3)
    [(.unwrap 8),(.active true),.left, (.unwrap 9),.left, (.unwrap 18),(.active true),.left, (.unwrap 4),.left] =
      some (.scalar (.usize 3)) := rfl

example (ambient : Frame) : NativeRecordValues.fits ((layoutTypes (positiveAmbient ambient false))[0]?.getD (.scalar .unit))
    (constructorErrorValue 3) = true := by
  simp [layoutTypes,positiveAmbient,constructorErrorValue,reservationErrorPayloadType,reservationErrorType,reservationKindType,
    capacityLayout,byteAlignment,alignmentDiscriminants,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

example (ambient : Frame) (world : NativeReferenceMachine.State) :
    (globalDropMovedFrame ambient 3 false 64 world).slots[41]? = some (.live (some .uninit)) := by
  simp [globalDropMovedFrame,globalDropBorrowedFrame,constructorErrorFrame,positiveFailureReturnedFrame,positiveMovedFrame,
    positiveBorrowFrame,positiveModeFrame,layoutAcceptedFrame,positiveAmbient]

private def errorBorrowed : NativeReferenceMachine.State := NativeZstBorrow.granted NativeReferenceMachine.empty 64
private def errorDropped : NativeReferenceMachine.State := NativeZstBorrow.grantedExclusive errorBorrowed 64

example (ambient : Frame) (shim : NativeAllocatorLLBC.Body)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) errorBorrowed [] = .returned (.scalar .unit) errorBorrowed) :
    NativeAllocatorLLBC.invokeValues (constructorWithDropFunction {ambient with world := NativeReferenceMachine.empty} false 64 shim)
      NativeReferenceMachine.empty [.scalar (.usize 3),allocationModeValue false,allocatorValue,byteLayout] =
      .returned (constructorErrorValue 3) errorDropped :=
  constructor_with_drop_failure _ 3 false 64 (by decide) shim _
    (NativeReferenceMachine.reachable_wellFormed _ .empty) (by decide) (by decide) returned

example (ambient : Frame) (shim : NativeAllocatorLLBC.Body)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) errorBorrowed [] = .returned (.scalar .unit) errorBorrowed) :
    NativeAllocatorLLBC.invokeValues (constructorWithDropFunction {ambient with world := NativeReferenceMachine.empty} true 64 shim)
      NativeReferenceMachine.empty [.scalar (.usize 3),allocationModeValue true,allocatorValue,byteLayout] =
      .returned (constructorErrorValue 3) errorDropped :=
  constructor_with_drop_failure _ 3 true 64 (by decide) shim _
    (NativeReferenceMachine.reachable_wellFormed _ .empty) (by decide) (by decide) returned

example : errorDropped.pointers.heap = NativeReferenceMachine.empty.pointers.heap := rfl

example : errorDropped.nextTag = 2 ∧ errorDropped.references.length = 2 := by decide

end HasteBootsVecCapacityArithmetic
