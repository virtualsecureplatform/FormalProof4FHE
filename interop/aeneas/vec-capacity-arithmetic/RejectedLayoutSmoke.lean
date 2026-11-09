namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example : NativeRecordValues.get capacityOverflowValue
    [(.unwrap 8),(.active true),.left, (.unwrap 9),.left, (.unwrap 18),(.active false)] = some (.scalar .unit) := rfl

example (ambient : Frame) : NativeRecordValues.fits ((layoutTypes (positiveAmbient ambient false))[0]?.getD (.scalar .unit))
    capacityOverflowValue = true := by
  simp [layoutTypes,positiveAmbient,capacityOverflowValue,reservationErrorPayloadType,reservationErrorType,reservationKindType,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

example (ambient : Frame) :
    NativeAllocatorLLBC.invokeValues (rejectedConstructorFunction {ambient with world := NativeReferenceMachine.empty} false 64)
      NativeReferenceMachine.empty [.scalar (.usize (2^63)),allocationModeValue false,allocatorValue,byteLayout] =
      .returned capacityOverflowValue (NativeZstBorrow.grantedExclusive NativeReferenceMachine.empty 64) :=
  rejected_constructor_invocation _ (2^63) false 64 (by decide) (by decide) (NativeReferenceMachine.reachable_wellFormed _ .empty)

example (ambient : Frame) :
    NativeAllocatorLLBC.invokeValues (rejectedConstructorFunction {ambient with world := NativeReferenceMachine.empty} true 64)
      NativeReferenceMachine.empty [.scalar (.usize (2^63)),allocationModeValue true,allocatorValue,byteLayout] =
      .returned capacityOverflowValue (NativeZstBorrow.grantedExclusive NativeReferenceMachine.empty 64) :=
  rejected_constructor_invocation _ (2^63) true 64 (by decide) (by decide) (NativeReferenceMachine.reachable_wellFormed _ .empty)

example (ambient : Frame) :
    NativeAllocatorLLBC.invokeValues (rejectedConstructorFunction {ambient with world := NativeReferenceMachine.empty} false 64)
      NativeReferenceMachine.empty [.scalar (.usize ⟨18446744073709551615,by decide⟩),allocationModeValue false,allocatorValue,byteLayout] =
      .returned capacityOverflowValue (NativeZstBorrow.grantedExclusive NativeReferenceMachine.empty 64) :=
  rejected_constructor_invocation _ ⟨18446744073709551615,by decide⟩ false 64 (by decide) (by decide)
    (NativeReferenceMachine.reachable_wellFormed _ .empty)

example : (NativeZstBorrow.grantedExclusive NativeReferenceMachine.empty 64).pointers.heap.memory.blocks = [] := rfl

example : (NativeZstBorrow.grantedExclusive NativeReferenceMachine.empty 64).nextTag = 1 := rfl

example (world : NativeReferenceMachine.State) :
    eval (dropDead [3,1] .ret) ⟨[.scalar .unit,.scalar .unit,.scalar .unit,.scalar .unit],
      [.live (some (.scalar .unit)),.dead,.dead,.dead],world⟩ = .returned (.scalar .unit) world :=
  drop_dead_returns _ [3,1] _ rfl (by
    change ∀ index ∈ ([3,1] : List Nat), index < 4 ∧ 0 ≠ index
    decide)

end HasteBootsVecCapacityArithmetic
