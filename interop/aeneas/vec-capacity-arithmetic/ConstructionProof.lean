namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem positive_result_pointer (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0) (next : Body) :
    eval (positiveResultPointerPrefix next) (positiveReturnedFrame ambient capacity zeroed address world pointer) =
      eval next (positivePointerFrame ambient capacity zeroed address world pointer) := by
  cases zeroed <;>
    simp [positiveResultPointerPrefix,positivePointerFrame,positiveReturnedFrame,runtimeSuccessValue,runtimeThinValue,
      positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes,
      eval,evalRvalue,evalRawThin,rawThinValue,evalOperand,storageLive,storageDead,NativeRecordLLBC.read,write,retag,nonnull,
      NativeSliceLLBC.retagValue,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,
      NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem positive_result_raw (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0) (next : Body) :
    eval (positiveResultRawPrefix next) (positivePointerFrame ambient capacity zeroed address world pointer) =
      eval next (positiveRawFrame ambient capacity zeroed address world pointer) := by
  cases zeroed <;>
    simp [positiveResultRawPrefix,positiveRawFrame,positiveRawValue,positivePointerFrame,positiveReturnedFrame,runtimeThinValue,
      positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes,
      allocatorValue,eval,evalRvalue,evalArgs,evalOperand,storageLive,storageDead,NativeRecordLLBC.read,write,retag,nonnull,
      NativeSliceLLBC.retagValue,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem positive_result_return (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0) :
    eval positiveResultReturn (positiveRawFrame ambient capacity zeroed address world pointer) =
      .returned (positiveResultValue pointer capacity) world := by
  cases zeroed <;>
    simp [positiveResultReturn,positiveResultValue,positiveRawFrame,positiveRawValue,positivePointerFrame,positiveReturnedFrame,
      runtimeThinValue,positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes,
      allocatorValue,eval,evalRvalue,evalArgs,evalOperand,storageDead,NativeRecordLLBC.read,write,nonnull,
      NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
      NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem positive_result_success (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0) :
    NativeAllocatorLLBC.eval positiveResultSuccess (positiveReturnedFrame ambient capacity zeroed address world pointer) =
      .returned (positiveResultValue pointer capacity) world := by
  rw [positiveResultSuccess,NativeAllocatorLLBC.legacy_done,positive_result_pointer _ _ _ _ _ _ nonnull,
    positive_result_raw _ _ _ _ _ _ nonnull,positive_result_return _ _ _ _ _ _ nonnull]

theorem positive_method_result (ambient calleeAmbient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim zero null unwind : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (returned : NativeAllocatorLLBC.invokeValues
      (allocationMethod calleeAmbient zeroed zero (runtimePositive outcome shim null runtimeSuccess))
      (NativeZstBorrow.granted ambient.world address)
      [.scalar (.reference false ⟨ambient.world.nextTag⟩ 0),capacityLayout capacity] =
        .returned (runtimeSuccessValue pointer capacity) world) :
    NativeAllocatorLLBC.eval (positiveMethodCall calleeAmbient zeroed outcome shim zero null unwind)
      (positiveBorrowFrame ambient capacity zeroed address) =
      .normal (positiveReturnedFrame ambient capacity zeroed address world pointer) := by
  have called := NativeAllocatorLLBC.eval_call
    (allocationMethod calleeAmbient zeroed zero (runtimePositive outcome shim null runtimeSuccess))
    (positiveBorrowFrame ambient capacity zeroed address) 10 (positiveCallArgs zeroed) unwind
    (.legacy (.dead (if zeroed then 12 else 11) .done) .done)
  rw [positive_call_arguments] at called
  simp only at called
  change NativeAllocatorLLBC.eval (positiveMethodCall calleeAmbient zeroed outcome shim zero null unwind)
      (positiveBorrowFrame ambient capacity zeroed address) = _
  rw [show (positiveMovedFrame ambient capacity zeroed address).world = NativeZstBorrow.granted ambient.world address from rfl,
    returned] at called
  rw [show NativeAllocatorLLBC.eval (positiveMethodCall calleeAmbient zeroed outcome shim zero null unwind)
      (positiveBorrowFrame ambient capacity zeroed address) = _ from called]
  cases zeroed <;>
    simp [NativeAllocatorLLBC.resume,write,positiveReturnedFrame,positiveMovedFrame,positiveBorrowFrame,
      positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes,runtimeSuccessValue,
      NativeAllocatorLLBC.legacy_done,eval,storageDead,NativeRecordValues.fits,NativeRecordValues.complete,
      NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem positive_constructor_selection (ambient calleeAmbient : Frame) (capacity : NativeWord64Memory.Word)
    (zeroed : Bool) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (outcome : Option NativePointerStorage.Address) (shim zero null unwind failure : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.eval (positiveConstructorBody calleeAmbient address outcome shim zero null unwind failure)
      (layoutAcceptedFrame (positiveAmbient ambient zeroed) capacity) =
      NativeAllocatorLLBC.continueWith (.matchChoice 10 [] 15 positiveResultSuccess failure .done)
        (NativeAllocatorLLBC.eval (positiveMethodCall calleeAmbient zeroed outcome shim zero null unwind)
          (positiveBorrowFrame ambient capacity zeroed address)) := by
  have prepared : eval (.dead 7 (.live 10 .done)) (layoutAcceptedFrame (positiveAmbient ambient zeroed) capacity) =
      .normal (positiveModeFrame ambient capacity zeroed) := by
    simp [eval,storageDead,storageLive,positiveModeFrame,layoutAcceptedFrame]
  have selected : selectChoice (positiveModeFrame ambient capacity zeroed) 2 [] 10 = some zeroed := by
    simp [selectChoice,positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes,allocationModeValue,allocationInitType,
      NativeRecordValues.sideAt,NativeRecordValues.typeAt]
  have borrow : eval (positiveBorrowPrefix zeroed address .done) (positiveModeFrame ambient capacity zeroed) =
      .normal (positiveBorrowFrame ambient capacity zeroed address) := by
    cases zeroed <;>
      simp [positiveBorrowPrefix,positiveBorrowFrame,positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes,
        allocatorValue,eval,evalRvalue,evalZstBorrow,NativeZstBorrow.issue_complete _ _ nonzero,storageLive,write,
        NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
        NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]
  rw [positiveConstructorBody,NativeAllocatorLLBC.legacy_normal _ prepared,NativeAllocatorLLBC.eval,selected]
  cases zeroed <;>
    change NativeAllocatorLLBC.continueWith _ (NativeAllocatorLLBC.eval (.legacy _ _) _) = _ <;>
    rw [NativeAllocatorLLBC.legacy_normal _ borrow]

theorem positive_constructor_after_method (ambient calleeAmbient : Frame) (capacity : NativeWord64Memory.Word)
    (zeroed : Bool) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (outcome : Option NativePointerStorage.Address) (shim zero null unwind failure : NativeAllocatorLLBC.Body)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues
      (allocationMethod calleeAmbient zeroed zero (runtimePositive outcome shim null runtimeSuccess))
      (NativeZstBorrow.granted ambient.world address)
      [.scalar (.reference false ⟨ambient.world.nextTag⟩ 0),capacityLayout capacity] =
        .returned (runtimeSuccessValue pointer capacity) world) :
    NativeAllocatorLLBC.eval (positiveConstructorBody calleeAmbient address outcome shim zero null unwind failure)
      (layoutAcceptedFrame (positiveAmbient ambient zeroed) capacity) =
      .returned (positiveResultValue pointer capacity) world := by
  have selected : selectChoice (positiveReturnedFrame ambient capacity zeroed address world pointer) 10 [] 15 = some false := by
    cases zeroed <;>
      simp [selectChoice,positiveReturnedFrame,positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,
        layoutAcceptedFrame,positiveAmbient,layoutTypes,runtimeSuccessValue,NativeRecordValues.typeAt,NativeRecordValues.sideAt]
  rw [positive_constructor_selection _ _ _ _ _ nonzero,positive_method_result _ _ _ _ _ _ _ _ _ _ _ _ returned]
  simp only [NativeAllocatorLLBC.continueWith]
  rw [NativeAllocatorLLBC.eval,selected]
  rw [positive_result_success _ _ _ _ _ _ nonnull]
  rfl

theorem positive_constructor_initialized (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    initial (positiveConstructorFunction ambient zeroed address outcome shim).types 4
      [.scalar (.usize capacity),allocationModeValue zeroed,allocatorValue,byteLayout] ambient.world =
      some (layoutFrame (positiveAmbient ambient zeroed) capacity) := by
  simp [positiveConstructorFunction,initial,layoutFrame,positiveAmbient,layoutTypes,allocationModeValue,allocationInitType,
    allocatorValue,byteLayout,byteAlignment,alignmentDiscriminants,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem positive_constructor_body_success (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld (if zeroed then .zeroed else .allocate) outcome capacity 1 =
      .value (.raw ⟨pointer,none⟩) resultWorld) :
    NativeAllocatorLLBC.eval (positiveConstructorFunction ambient zeroed address outcome shim).body
      (layoutFrame (positiveAmbient ambient zeroed) capacity) = .returned (positiveResultValue pointer capacity) resultWorld := by
  have distinct : capacity ≠ 0 := by intro same; subst capacity; simp at positive
  have pointerDistinct : pointer.address ≠ 0 := by
    intro same
    exact nonnull (congrArg Fin.val same)
  have preparedLayout : eval
      (layoutPrefix (.unsupported "source constructor overflow")
        (capacityDispatch zeroSizeBody .done .done) (.unsupported "source constructor layout rejection") .done)
      (layoutFrame (positiveAmbient ambient zeroed) capacity) =
      .normal (layoutAcceptedFrame (positiveAmbient ambient zeroed) capacity) := by
    rw [layout_capacity_dispatch _ _ bounded,decide_eq_false distinct,false_branch_continuation]
    rfl
  change NativeAllocatorLLBC.eval (.legacy _ _) _ = _
  rw [NativeAllocatorLLBC.legacy_normal _ preparedLayout]
  apply positive_constructor_after_method _ _ _ _ _ nonzero _ _ _ _ _ _ _ _ nonnull
  exact method_success_invocation {ambient with world := NativeZstBorrow.granted ambient.world address}
    ⟨ambient.world.nextTag⟩ capacity zeroed outcome shim _ runtimeNull shimWorld resultWorld pointer distinct returned allocated pointerDistinct

theorem positive_constructor_invocation (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld (if zeroed then .zeroed else .allocate) outcome capacity 1 =
      .value (.raw ⟨pointer,none⟩) resultWorld) :
    NativeAllocatorLLBC.invokeValues (positiveConstructorFunction ambient zeroed address outcome shim) ambient.world
      [.scalar (.usize capacity),allocationModeValue zeroed,allocatorValue,byteLayout] =
      .returned (positiveResultValue pointer capacity) resultWorld := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _
    (positive_constructor_initialized ambient capacity zeroed address outcome shim),
    positive_constructor_body_success _ _ _ _ nonzero _ _ _ _ _ positive bounded nonnull returned allocated]
  rfl

end HasteBootsVecCapacityArithmetic
