namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem allocator_boolean_dispatch (frame caller : Frame) (test : Operand) (condition : Bool)
    (yes no next : NativeAllocatorLLBC.Body)
    (selected : evalBooleanOperand frame test = some (condition,caller)) :
    NativeAllocatorLLBC.eval (.switchBoolean test yes no next) frame = NativeAllocatorLLBC.continueWith next
      (if condition then NativeAllocatorLLBC.eval yes caller else NativeAllocatorLLBC.eval no caller) := by
  rw [NativeAllocatorLLBC.eval,selected]
  rfl

theorem allocator_usize_dispatch (frame caller : Frame) (test : Operand) (word expected : NativeWord64Memory.Word)
    (yes no next : NativeAllocatorLLBC.Body)
    (selected : evalOperand frame test = some (.scalar (.usize word),caller)) :
    NativeAllocatorLLBC.eval (.switchUsize test expected yes no next) frame = NativeAllocatorLLBC.continueWith next
      (if word = expected then NativeAllocatorLLBC.eval yes caller else NativeAllocatorLLBC.eval no caller) := by
  rw [NativeAllocatorLLBC.eval,selected]
  rfl

theorem unified_constructor_initialized (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    initial (unifiedConstructorFunction ambient zeroed address outcome shim).types 4
      [.scalar (.usize capacity),allocationModeValue zeroed,allocatorValue,byteLayout] ambient.world =
      some (layoutFrame (positiveAmbient ambient zeroed) capacity) :=
  positive_constructor_initialized ambient capacity zeroed address outcome shim

theorem unified_constructor_dispatch (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.eval (unifiedConstructorFunction ambient zeroed address outcome shim).body
      (layoutFrame (positiveAmbient ambient zeroed) capacity) =
      if capacity.val < 2^63 then NativeAllocatorLLBC.eval (unifiedAcceptedBody ambient address outcome shim)
        (layoutAfterFrame (positiveAmbient ambient zeroed) capacity)
      else NativeAllocatorLLBC.eval (unifiedRejectedBody address) (layoutAfterFrame (positiveAmbient ambient zeroed) capacity) := by
  have initialPrefix : eval (layoutInitialPrefix .done) (layoutFrame (positiveAmbient ambient zeroed) capacity) =
      .normal (layoutProductFrame (positiveAmbient ambient zeroed) capacity) := by rw [layout_initial_exact]; rfl
  have noOverflow : evalBooleanOperand (layoutProductFrame (positiveAmbient ambient zeroed) capacity) (.copy 24 []) =
      some (false,layoutProductFrame (positiveAmbient ambient zeroed) capacity) := by
    simp [evalBooleanOperand,evalOperand,layoutProductFrame,layoutTypes,NativeRecordLLBC.read,NativeRecordValues.typeAt,
      NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable]
  have checkPrefix : eval (layoutCheckPrefix .done) (layoutProductFrame (positiveAmbient ambient zeroed) capacity) =
      .normal (layoutComparedFrame (positiveAmbient ambient zeroed) capacity) := by rw [layout_check_exact]; rfl
  have selected : evalBooleanOperand (layoutComparedFrame (positiveAmbient ambient zeroed) capacity) (.move 30 []) =
      some (decide (capacity.val < 2^63),layoutAfterFrame (positiveAmbient ambient zeroed) capacity) := by
    simp [evalBooleanOperand,evalOperand,layoutComparedFrame,layoutAfterFrame,layoutTypes,NativeRecordLLBC.read,
      NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
      NativeRecordValues.complete,NativeRecordValues.compatible]
  change NativeAllocatorLLBC.eval (.legacy (layoutInitialPrefix .done)
    (.switchBoolean (.copy 24 []) (.legacy (.unsupported "source byte multiplication overflow") .done)
      (.legacy (layoutCheckPrefix .done) (.switchBoolean (.move 30 [])
        (unifiedAcceptedBody ambient address outcome shim) (unifiedRejectedBody address) .done)) .done)) _ = _
  rw [NativeAllocatorLLBC.legacy_normal _ initialPrefix,allocator_boolean_dispatch _ _ _ _ _ _ _ noOverflow,
    NativeAllocatorLLBC.continue_done]
  simp only [Bool.false_eq_true,ite_false]
  rw [NativeAllocatorLLBC.legacy_normal _ checkPrefix,allocator_boolean_dispatch _ _ _ _ _ _ _ selected,
    NativeAllocatorLLBC.continue_done]
  simp only [decide_eq_true_eq]

theorem unified_accepted_dispatch (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.eval (unifiedAcceptedBody ambient address outcome shim) (layoutAfterFrame (positiveAmbient ambient zeroed) capacity) =
      if capacity = 0 then eval zeroSizeBody (layoutAcceptedFrame (positiveAmbient ambient zeroed) capacity)
      else NativeAllocatorLLBC.eval (unifiedPositiveBody ambient address outcome shim) (layoutAcceptedFrame (positiveAmbient ambient zeroed) capacity) := by
  have prepared : eval (acceptedLayoutPrefix .done) (layoutAfterFrame (positiveAmbient ambient zeroed) capacity) =
      .normal (layoutAcceptedFrame (positiveAmbient ambient zeroed) capacity) := by rw [accepted_layout_exact]; rfl
  have selected : evalOperand (layoutAcceptedFrame (positiveAmbient ambient zeroed) capacity) (.copy 7 []) =
      some (.scalar (.usize capacity),layoutAcceptedFrame (positiveAmbient ambient zeroed) capacity) := by
    simp [evalOperand,layoutAcceptedFrame,layoutTypes,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits]
  rw [unifiedAcceptedBody,NativeAllocatorLLBC.legacy_normal _ prepared,
    allocator_usize_dispatch _ _ _ _ _ _ _ _ selected,NativeAllocatorLLBC.continue_done,NativeAllocatorLLBC.legacy_done]

theorem unified_constructor_zero (ambient : Frame) (zeroed : Bool) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.invokeValues (unifiedConstructorFunction ambient zeroed address outcome shim) ambient.world
      [.scalar (.usize 0),allocationModeValue zeroed,allocatorValue,byteLayout] = .returned zeroResultValue ambient.world := by
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (unified_constructor_initialized ambient 0 zeroed address outcome shim),
    unified_constructor_dispatch,ite_eq_left (by decide),unified_accepted_dispatch,ite_eq_left rfl]
  rw [zero_size_exact _ (by cases zeroed <;> rfl)]
  rfl

theorem unified_constructor_rejected (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (large : 2^63 ≤ capacity.val) (valid : NativeReferenceMachine.WellFormed ambient.world) :
    NativeAllocatorLLBC.invokeValues (unifiedConstructorFunction ambient zeroed address outcome shim) ambient.world
      [.scalar (.usize capacity),allocationModeValue zeroed,allocatorValue,byteLayout] =
      .returned capacityOverflowValue (NativeZstBorrow.grantedExclusive ambient.world address) := by
  have rejected : ¬ capacity.val < 2^63 := by omega
  have prepared : eval (rejectedLayoutPrefix .done) (layoutAfterFrame (positiveAmbient ambient zeroed) capacity) =
      .normal (rejectedLayoutFrame ambient capacity zeroed) := by rw [rejected_layout_prefix]; rfl
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (unified_constructor_initialized ambient capacity zeroed address outcome shim),
    unified_constructor_dispatch,ite_eq_right rejected,unifiedRejectedBody,NativeAllocatorLLBC.legacy_normal _ prepared,
    rejected_drop_returns _ _ _ _ nonzero valid]
  rfl

theorem unified_constructor_success (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld (if zeroed then .zeroed else .allocate) outcome capacity 1 =
      .value (.raw ⟨pointer,none⟩) resultWorld) :
    NativeAllocatorLLBC.invokeValues (unifiedConstructorFunction ambient zeroed address outcome shim) ambient.world
      [.scalar (.usize capacity),allocationModeValue zeroed,allocatorValue,byteLayout] =
      .returned (positiveResultValue pointer capacity) resultWorld := by
  have distinct : capacity ≠ 0 := by intro same; subst capacity; simp at positive
  have pointerDistinct : pointer.address ≠ 0 := by intro same; exact nonnull (congrArg Fin.val same)
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (unified_constructor_initialized ambient capacity zeroed address outcome shim),
    unified_constructor_dispatch,ite_eq_left bounded,unified_accepted_dispatch,ite_eq_right distinct,unifiedPositiveBody]
  rw [positive_constructor_after_method _ _ _ _ _ nonzero _ _ _ _ _ _ _ _ nonnull
    (method_success_invocation {ambient with world := NativeZstBorrow.granted ambient.world address} ⟨ambient.world.nextTag⟩
      capacity zeroed outcome shim _ runtimeNull shimWorld resultWorld pointer distinct returned allocated pointerDistinct)]
  rfl

theorem unified_constructor_failure (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (shim : NativeAllocatorLLBC.Body)
    (world : NativeReferenceMachine.State) (valid : NativeReferenceMachine.WellFormed ambient.world)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted ambient.world address) [] =
      .returned (.scalar .unit) world) :
    NativeAllocatorLLBC.invokeValues (unifiedConstructorFunction ambient zeroed address none shim) ambient.world
      [.scalar (.usize capacity),allocationModeValue zeroed,allocatorValue,byteLayout] =
      .returned (constructorErrorValue capacity) (NativeZstBorrow.grantedExclusive world address) := by
  have distinct : capacity ≠ 0 := by intro same; subst capacity; simp at positive
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
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (unified_constructor_initialized ambient capacity zeroed address none shim),
    unified_constructor_dispatch,ite_eq_left bounded,unified_accepted_dispatch,ite_eq_right distinct,unifiedPositiveBody]
  rw [positive_constructor_failure _ _ _ _ _ nonzero _ _ _ _ validResult
    (method_failure_invocation {ambient with world := NativeZstBorrow.granted ambient.world address} ⟨ambient.world.nextTag⟩
      capacity zeroed shim _ runtimeSuccess world returned validLayout positive)]
  rfl

theorem unified_constructor_unwind (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State) (positive : 0 < capacity.val)
    (bounded : capacity.val < 2^63) (valid : NativeReferenceMachine.WellFormed world)
    (unwound : NativeAllocatorLLBC.invokeValues
      (allocationMethod {ambient with world := NativeZstBorrow.granted ambient.world address} zeroed
        (.legacy (.unsupported "source runtime zero size") .done) (runtimePositive outcome shim runtimeNull runtimeSuccess))
      (NativeZstBorrow.granted ambient.world address)
      [.scalar (.reference false ⟨ambient.world.nextTag⟩ 0),capacityLayout capacity] = .unwind world) :
    NativeAllocatorLLBC.invokeValues (unifiedConstructorFunction ambient zeroed address outcome shim) ambient.world
      [.scalar (.usize capacity),allocationModeValue zeroed,allocatorValue,byteLayout] =
      .unwind (NativeZstBorrow.grantedExclusive world address) := by
  have distinct : capacity ≠ 0 := by intro same; subst capacity; simp at positive
  rw [NativeAllocatorLLBC.invokeValues_initialized _ _ _ _ (unified_constructor_initialized ambient capacity zeroed address outcome shim),
    unified_constructor_dispatch,ite_eq_left bounded,unified_accepted_dispatch,ite_eq_right distinct,unifiedPositiveBody,
    positive_body_unwind _ _ _ _ _ nonzero _ _ _ _ _ _ valid unwound]
  rfl

end HasteBootsVecCapacityArithmetic
