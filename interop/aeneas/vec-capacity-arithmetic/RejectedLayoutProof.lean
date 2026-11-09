namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem rejected_layout_prefix (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool) (next : Body) :
    eval (rejectedLayoutPrefix next) (layoutAfterFrame (positiveAmbient ambient zeroed) capacity) =
      eval next (rejectedLayoutFrame ambient capacity zeroed) := by
  cases zeroed <;>
    simp [rejectedLayoutPrefix,rejectedLayoutFrame,capacityOverflowValue,layoutAfterFrame,positiveAmbient,layoutTypes,
      reservationErrorPayloadType,reservationErrorType,reservationKindType,eval,evalRvalue,evalArgs,evalOperand,
      storageLive,storageDead,NativeRecordLLBC.read,write,retag,NativeSliceLLBC.retagValue,NativeRecordValues.typeAt,
      NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,NativeRecordValues.complete,
      NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem rejected_drop_returns (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (valid : NativeReferenceMachine.WellFormed ambient.world) :
    NativeAllocatorLLBC.eval (globalDropCall address (.legacy globalDropCleanup .done)) (rejectedLayoutFrame ambient capacity zeroed) =
      .returned capacityOverflowValue (NativeZstBorrow.grantedExclusive ambient.world address) := by
  apply drop_frame_returns _ address nonzero
  · simp [rejectedLayoutFrame,layoutAfterFrame,positiveAmbient]
  · simp [rejectedLayoutFrame,layoutAfterFrame,layoutTypes,positiveAmbient]
  · simp [rejectedLayoutFrame,layoutAfterFrame,layoutTypes,positiveAmbient]
  · cases zeroed <;>
      simp [rejectedLayoutFrame,layoutAfterFrame,positiveAmbient,layoutTypes,allocatorValue,NativeRecordLLBC.read,
        NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,
        NativeRecordValues.compatible,NativeSliceLLBC.fits]
  · cases zeroed <;>
      simp [rejectedLayoutFrame,layoutAfterFrame,positiveAmbient,layoutTypes,capacityOverflowValue,
        reservationErrorPayloadType,reservationErrorType,reservationKindType,NativeRecordLLBC.read,
        NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,
        NativeRecordValues.compatible,NativeSliceLLBC.fits]
  · exact valid

theorem rejected_constructor_initialized (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) :
    initial (rejectedConstructorFunction ambient zeroed address).types 4
      [.scalar (.usize capacity),allocationModeValue zeroed,allocatorValue,byteLayout] ambient.world =
      some (layoutFrame (positiveAmbient ambient zeroed) capacity) :=
  positive_constructor_initialized ambient capacity zeroed address none .done

theorem rejected_constructor_body (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (large : 2^63 ≤ capacity.val)
    (valid : NativeReferenceMachine.WellFormed ambient.world) :
    NativeAllocatorLLBC.eval (rejectedConstructorFunction ambient zeroed address).body
      (layoutFrame (positiveAmbient ambient zeroed) capacity) =
      .returned capacityOverflowValue (NativeZstBorrow.grantedExclusive ambient.world address) := by
  have rejected : ¬ capacity.val < 2^63 := by omega
  have prepared : eval
      (layoutPrefix (.unsupported "source byte multiplication overflow") (.unsupported "source accepted allocation layout")
        (rejectedLayoutPrefix .done) .done) (layoutFrame (positiveAmbient ambient zeroed) capacity) =
      .normal (rejectedLayoutFrame ambient capacity zeroed) := by
    rw [layout_prefix_exact,decide_eq_false rejected,false_branch_continuation,rejected_layout_prefix]
    rfl
  change NativeAllocatorLLBC.eval (.legacy _ _) _ = _
  rw [NativeAllocatorLLBC.legacy_normal _ prepared,rejected_drop_returns _ _ _ _ nonzero valid]

theorem rejected_constructor_invocation (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (large : 2^63 ≤ capacity.val)
    (valid : NativeReferenceMachine.WellFormed ambient.world) :
    NativeAllocatorLLBC.invokeValues (rejectedConstructorFunction ambient zeroed address) ambient.world
      [.scalar (.usize capacity),allocationModeValue zeroed,allocatorValue,byteLayout] =
      .returned capacityOverflowValue (NativeZstBorrow.grantedExclusive ambient.world address) := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (rejected_constructor_initialized ambient capacity zeroed address),
    rejected_constructor_body _ _ _ _ nonzero large valid]
  rfl

theorem rejected_constructor_heap (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (large : 2^63 ≤ capacity.val)
    (valid : NativeReferenceMachine.WellFormed ambient.world) :
    (NativeAllocatorLLBC.invokeValues (rejectedConstructorFunction ambient zeroed address) ambient.world
      [.scalar (.usize capacity),allocationModeValue zeroed,allocatorValue,byteLayout]).world.pointers.heap = ambient.world.pointers.heap := by
  rw [rejected_constructor_invocation _ _ _ _ nonzero large valid]
  rfl

end HasteBootsVecCapacityArithmetic
