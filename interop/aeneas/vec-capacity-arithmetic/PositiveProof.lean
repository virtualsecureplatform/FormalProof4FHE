namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

/-- Source mode dispatch and shared Global loan issuance, with explicit placement.
The unprocessed allocation call and following bodies remain arbitrary. -/
theorem positive_mode_exact (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (uninitialized initialized next : Body) :
    eval (positiveModePrefix address uninitialized initialized next)
      (layoutAcceptedFrame (positiveAmbient ambient zeroed) capacity) =
    eval (.constIf zeroed initialized uninitialized next) (positiveBorrowFrame ambient capacity zeroed address) := by
  cases zeroed <;>
    simp [positiveModePrefix,positiveBorrowPrefix,positiveBorrowFrame,positiveModeFrame,positiveAmbient,
      allocationModeValue,allocationInitType,layoutAcceptedFrame,layoutTypes,allocatorValue,
      eval,evalRvalue,evalZstBorrow,NativeZstBorrow.issue_complete _ _ nonzero,
      selectChoice,storageLive,storageDead,NativeRecordLLBC.read,write,NativeRecordValues.sideAt,
      NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,
      NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem positive_call_arguments (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) :
    evalArgs (positiveBorrowFrame ambient capacity zeroed address) (positiveCallArgs zeroed) =
      some ([.scalar (.reference false ⟨ambient.world.nextTag⟩ 0),capacityLayout capacity],
        positiveMovedFrame ambient capacity zeroed address) := by
  cases zeroed <;>
    simp [positiveCallArgs,positiveBorrowFrame,positiveMovedFrame,positiveModeFrame,positiveAmbient,
      layoutAcceptedFrame,layoutTypes,capacityLayout,byteAlignment,alignmentDiscriminants,evalArgs,evalOperand,
      NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits]

/-- The preceding original layout prefix reaches exactly the selected allocator
call preparation for every accepted positive byte capacity. -/
theorem positive_layout_entry (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (overflow rejected zero uninitialized initialized next : Body) :
    eval (layoutPrefix overflow
      (capacityDispatch zero (positiveModePrefix address uninitialized initialized .done) .done) rejected next)
      (layoutFrame (positiveAmbient ambient zeroed) capacity) =
    eval (.constIf zeroed initialized uninitialized next) (positiveBorrowFrame ambient capacity zeroed address) := by
  have distinct : capacity ≠ 0 := by
    intro same
    have equal := congrArg Fin.val same
    change capacity.val = 0 at equal
    omega
  rw [layout_capacity_dispatch _ _ bounded,decide_eq_false distinct,false_branch_continuation,
    positive_mode_exact _ _ _ _ nonzero,constant_branch_tail]

theorem positive_borrow_decoded (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) :
    NativeZstReference.decode (positiveBorrowFrame ambient capacity zeroed address).world 0 =
      some (.reference false ⟨ambient.world.nextTag⟩ 0) := NativeZstBorrow.granted_decoded ambient.world address

theorem positive_borrow_heap (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) :
    (positiveBorrowFrame ambient capacity zeroed address).world.pointers.heap = ambient.world.pointers.heap := rfl

theorem positive_borrow_reachable (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (reachable : NativeReferenceMachine.Reachable ambient.world) :
    NativeReferenceMachine.Reachable (positiveBorrowFrame ambient capacity zeroed address).world :=
  NativeZstBorrow.granted_reachable ambient.world address nonzero reachable

end HasteBootsVecCapacityArithmetic
