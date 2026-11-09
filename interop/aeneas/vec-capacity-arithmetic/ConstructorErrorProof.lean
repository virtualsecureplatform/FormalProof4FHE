namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem global_drop_initialized (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference) :
    initial globalDropFunction.types 1 [.scalar (.reference true reference 0)] world =
      some ⟨[.scalar .unit,.scalar (.reference true)],[.dead,.live (some (.scalar (.reference true reference 0)))],world⟩ := by
  simp [globalDropFunction,initial,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem global_drop_values (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (valid : NativeReferenceMachine.WellFormed world) :
    NativeAllocatorLLBC.invokeValues globalDropFunction world [.scalar (.reference true reference 0)] = .returned (.scalar .unit) world := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (global_drop_initialized world reference)]
  change settle world (NativeAllocatorLLBC.eval (.legacy (.live 0 (.assign 0 .unit (.dead 1 .ret))) .done) _) = _
  rw [NativeAllocatorLLBC.legacy_done]
  have body : eval (.live 0 (.assign 0 .unit (.dead 1 .ret)))
      ⟨[.scalar .unit,.scalar (.reference true)],[.dead,.live (some (.scalar (.reference true reference 0)))],world⟩ =
      .returned (.scalar .unit) world := by
    simp [eval,evalRvalue,storageLive,storageDead,write,NativeRecordLLBC.read,NativeRecordValues.typeAt,
      NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]
  rw [body,settle_same_unit world valid]

theorem constructor_error_prefix (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (world : NativeReferenceMachine.State) (next : Body) :
    eval (constructorErrorPrefix next) (positiveFailureReturnedFrame ambient capacity zeroed address world) =
      eval next (constructorErrorFrame ambient capacity zeroed address world) := by
  cases zeroed <;>
    simp [constructorErrorPrefix,constructorErrorFrame,constructorErrorValue,positiveFailureReturnedFrame,
      positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes,
      reservationErrorPayloadType,reservationErrorType,reservationKindType,capacityLayout,byteAlignment,alignmentDiscriminants,
      eval,evalRvalue,evalArgs,evalOperand,storageLive,storageDead,NativeRecordLLBC.read,write,
      NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
      NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem global_drop_borrow (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (world : NativeReferenceMachine.State) (next : Body) :
    eval (globalDropBorrowPrefix address next) (constructorErrorFrame ambient capacity zeroed address world) =
      eval next (globalDropBorrowedFrame ambient capacity zeroed address world) := by
  cases zeroed <;>
    simp [globalDropBorrowPrefix,globalDropBorrowedFrame,constructorErrorFrame,positiveFailureReturnedFrame,
      positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes,allocatorValue,
      eval,evalRvalue,evalZstMutBorrow,NativeZstBorrow.issue_exclusive_complete _ _ nonzero,storageLive,
      NativeRecordLLBC.read,write,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,
      NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem global_drop_arguments (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (world : NativeReferenceMachine.State) :
    evalArgs (globalDropBorrowedFrame ambient capacity zeroed address world) [.move 41 []] =
      some ([.scalar (.reference true ⟨world.nextTag⟩ 0)],globalDropMovedFrame ambient capacity zeroed address world) := by
  cases zeroed <;>
    simp [globalDropBorrowedFrame,globalDropMovedFrame,constructorErrorFrame,positiveFailureReturnedFrame,positiveMovedFrame,
      positiveBorrowFrame,positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes,evalArgs,evalOperand,
      NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem global_drop_resumes (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (world : NativeReferenceMachine.State)
    (valid : NativeReferenceMachine.WellFormed world) (next : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.eval (globalDropCall address next) (constructorErrorFrame ambient capacity zeroed address world) =
      NativeAllocatorLLBC.eval next (globalDropReturnedFrame ambient capacity zeroed address world) := by
  have prepared : eval (globalDropBorrowPrefix address .done) (constructorErrorFrame ambient capacity zeroed address world) =
      .normal (globalDropBorrowedFrame ambient capacity zeroed address world) := by
    rw [global_drop_borrow _ _ _ _ nonzero]; rfl
  rw [globalDropCall,NativeAllocatorLLBC.legacy_normal _ prepared]
  have called := NativeAllocatorLLBC.eval_call globalDropFunction (globalDropBorrowedFrame ambient capacity zeroed address world)
    42 [.move 41 []] (.legacy globalDropUnwind .done) next
  rw [global_drop_arguments] at called
  simp only at called
  have validBorrowed := NativeZstBorrow.granted_exclusive_wellFormed world address nonzero valid
  rw [show (globalDropMovedFrame ambient capacity zeroed address world).world = NativeZstBorrow.grantedExclusive world address from rfl,
    global_drop_values _ _ validBorrowed] at called
  rw [called]
  cases zeroed <;>
    simp [NativeAllocatorLLBC.resume,write,globalDropReturnedFrame,globalDropMovedFrame,globalDropBorrowedFrame,
      constructorErrorFrame,positiveFailureReturnedFrame,positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,
      layoutAcceptedFrame,positiveAmbient,layoutTypes,NativeRecordValues.fits,NativeRecordValues.complete,
      NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem global_drop_cleanup (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (world : NativeReferenceMachine.State) :
    eval globalDropCleanup (globalDropReturnedFrame ambient capacity zeroed address world) =
      .returned (constructorErrorValue capacity) (NativeZstBorrow.grantedExclusive world address) := by
  cases zeroed <;>
    simp [globalDropCleanup,globalDropReturnedFrame,globalDropMovedFrame,globalDropBorrowedFrame,constructorErrorFrame,
      constructorErrorValue,positiveFailureReturnedFrame,positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,
      layoutAcceptedFrame,positiveAmbient,layoutTypes,reservationErrorPayloadType,reservationErrorType,reservationKindType,
      capacityLayout,byteAlignment,alignmentDiscriminants,eval,storageDead,NativeRecordLLBC.read,NativeRecordValues.typeAt,
      NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem constructor_error_with_drop (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (world : NativeReferenceMachine.State)
    (valid : NativeReferenceMachine.WellFormed world) :
    NativeAllocatorLLBC.eval (constructorFailureContinuation address) (positiveFailureReturnedFrame ambient capacity zeroed address world) =
      .returned (constructorErrorValue capacity) (NativeZstBorrow.grantedExclusive world address) := by
  have prepared : eval (constructorErrorPrefix .done) (positiveFailureReturnedFrame ambient capacity zeroed address world) =
      .normal (constructorErrorFrame ambient capacity zeroed address world) := by rw [constructor_error_prefix]; rfl
  rw [constructorFailureContinuation,NativeAllocatorLLBC.legacy_normal _ prepared,
    global_drop_resumes _ _ _ _ nonzero _ valid,NativeAllocatorLLBC.legacy_done,global_drop_cleanup]

theorem positive_method_failure_result (ambient calleeAmbient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (shim zero unwind : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State)
    (returned : NativeAllocatorLLBC.invokeValues
      (allocationMethod calleeAmbient zeroed zero (runtimePositive none shim runtimeNull runtimeSuccess))
      (NativeZstBorrow.granted ambient.world address)
      [.scalar (.reference false ⟨ambient.world.nextTag⟩ 0),capacityLayout capacity] = .returned runtimeFailureValue world) :
    NativeAllocatorLLBC.eval (positiveMethodCall calleeAmbient zeroed none shim zero runtimeNull unwind)
      (positiveBorrowFrame ambient capacity zeroed address) = .normal (positiveFailureReturnedFrame ambient capacity zeroed address world) := by
  have called := NativeAllocatorLLBC.eval_call
    (allocationMethod calleeAmbient zeroed zero (runtimePositive none shim runtimeNull runtimeSuccess))
    (positiveBorrowFrame ambient capacity zeroed address) 10 (positiveCallArgs zeroed) unwind
    (.legacy (.dead (if zeroed then 12 else 11) .done) .done)
  rw [positive_call_arguments] at called
  simp only at called
  rw [show (positiveMovedFrame ambient capacity zeroed address).world = NativeZstBorrow.granted ambient.world address from rfl,
    returned] at called
  rw [show NativeAllocatorLLBC.eval (positiveMethodCall calleeAmbient zeroed none shim zero runtimeNull unwind)
      (positiveBorrowFrame ambient capacity zeroed address) = _ from called]
  cases zeroed <;>
    simp [NativeAllocatorLLBC.resume,write,positiveFailureReturnedFrame,positiveMovedFrame,positiveBorrowFrame,
      positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes,runtimeFailureValue,
      NativeAllocatorLLBC.legacy_done,eval,storageDead,NativeRecordValues.fits,NativeRecordValues.complete,
      NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem positive_constructor_failure (ambient calleeAmbient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (shim zero unwind : NativeAllocatorLLBC.Body)
    (world : NativeReferenceMachine.State) (valid : NativeReferenceMachine.WellFormed world)
    (returned : NativeAllocatorLLBC.invokeValues
      (allocationMethod calleeAmbient zeroed zero (runtimePositive none shim runtimeNull runtimeSuccess))
      (NativeZstBorrow.granted ambient.world address)
      [.scalar (.reference false ⟨ambient.world.nextTag⟩ 0),capacityLayout capacity] = .returned runtimeFailureValue world) :
    NativeAllocatorLLBC.eval (positiveConstructorBody calleeAmbient address none shim zero runtimeNull unwind (constructorFailureContinuation address))
      (layoutAcceptedFrame (positiveAmbient ambient zeroed) capacity) =
      .returned (constructorErrorValue capacity) (NativeZstBorrow.grantedExclusive world address) := by
  have selected : selectChoice (positiveFailureReturnedFrame ambient capacity zeroed address world) 10 [] 15 = some true := by
    cases zeroed <;>
      simp [selectChoice,positiveFailureReturnedFrame,positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,
        layoutAcceptedFrame,positiveAmbient,layoutTypes,runtimeFailureValue,NativeRecordValues.typeAt,NativeRecordValues.sideAt]
  rw [positive_constructor_selection _ _ _ _ _ nonzero,positive_method_failure_result _ _ _ _ _ _ _ _ _ returned]
  simp only [NativeAllocatorLLBC.continueWith]
  rw [NativeAllocatorLLBC.eval,selected,constructor_error_with_drop _ _ _ _ nonzero _ valid]
  rfl

theorem constructor_with_drop_initialized (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (shim : NativeAllocatorLLBC.Body) :
    initial (constructorWithDropFunction ambient zeroed address shim).types 4
      [.scalar (.usize capacity),allocationModeValue zeroed,allocatorValue,byteLayout] ambient.world =
      some (layoutFrame (positiveAmbient ambient zeroed) capacity) :=
  positive_constructor_initialized ambient capacity zeroed address none shim

theorem constructor_with_drop_failure (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (shim : NativeAllocatorLLBC.Body)
    (world : NativeReferenceMachine.State) (valid : NativeReferenceMachine.WellFormed ambient.world)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) world) :
    NativeAllocatorLLBC.invokeValues (constructorWithDropFunction ambient zeroed address shim) ambient.world
      [.scalar (.usize capacity),allocationModeValue zeroed,allocatorValue,byteLayout] =
      .returned (constructorErrorValue capacity) (NativeZstBorrow.grantedExclusive world address) := by
  have distinct : capacity ≠ 0 := by intro same; subst capacity; simp at positive
  have preparedLayout : eval
      (layoutPrefix (.unsupported "source constructor overflow") (capacityDispatch zeroSizeBody .done .done)
        (.unsupported "source constructor layout rejection") .done) (layoutFrame (positiveAmbient ambient zeroed) capacity) =
      .normal (layoutAcceptedFrame (positiveAmbient ambient zeroed) capacity) := by
    rw [layout_capacity_dispatch _ _ bounded,decide_eq_false distinct,false_branch_continuation]; rfl
  have validLayout : (NativeAllocatorExecution.request capacity 1).Valid := by
    refine ⟨?_,?_⟩
    · change 1 ∈ (List.range 64).map (fun exponent => 2 ^ exponent)
      decide
    · change capacity.val + (1-1) ≤ 2^63-1
      omega
  have validBorrowed : NativeReferenceMachine.WellFormed (NativeZstBorrow.granted ambient.world address) :=
    NativeReferenceMachine.execute_wellFormed _ _
      (NativeReferenceMachine.execute_wellFormed _ _ valid _ (NativeZstBorrow.placement_step ambient.world address)) _
      (NativeZstBorrow.grant_step ambient.world address nonzero)
  have validResult := NativeSliceLLBC.reference_runs_wellFormed _ _ validBorrowed
    (NativeAllocatorLLBC.invokeValues_projects (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [])
  rw [returned] at validResult
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (constructor_with_drop_initialized ambient capacity zeroed address shim)]
  change settle ambient.world (NativeAllocatorLLBC.eval (.legacy _ _) _) = _
  rw [NativeAllocatorLLBC.legacy_normal _ preparedLayout]
  rw [positive_constructor_failure _ _ _ _ _ nonzero _ _ _ _ validResult
    (method_failure_invocation {ambient with world := NativeZstBorrow.granted ambient.world address} ⟨ambient.world.nextTag⟩
      capacity zeroed shim _ runtimeSuccess world returned validLayout positive)]
  rfl

end HasteBootsVecCapacityArithmetic
