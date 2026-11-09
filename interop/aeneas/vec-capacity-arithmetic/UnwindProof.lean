namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

def unwindFrameBorrowed (frame : Frame) (address : NativeWord64Memory.Word) : Frame :=
  let opened := frame.slots.set 43 (.live none)
  let stored := opened.set 43 (.live (some (.scalar (.reference true ⟨frame.world.nextTag⟩ 0))))
  {frame with slots := stored.set 44 (.live none),world := NativeZstBorrow.grantedExclusive frame.world address}

def unwindFrameMoved (frame : Frame) (address : NativeWord64Memory.Word) : Frame :=
  let base := unwindFrameBorrowed frame address
  {base with slots := base.slots.set 43 (.live (some .uninit))}

def unwindFrameReturned (frame : Frame) (address : NativeWord64Memory.Word) : Frame :=
  let base := unwindFrameMoved frame address
  {base with slots := base.slots.set 44 (.live (some (.scalar .unit)))}

theorem unwind_storage_live_present (frame : Frame) (index : Nat) (bound : index < frame.slots.length) :
    storageLive frame index = some {frame with slots := frame.slots.set index (.live none)} := by
  simp only [storageLive,List.getElem?_eq_getElem bound,Option.map_some]

theorem unwind_frame_borrow (frame : Frame) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (length : 54 ≤ frame.slots.length) (type : frame.types[43]? = some (.scalar (.reference true)))
    (global : NativeRecordLLBC.read frame 3 [] = some allocatorValue) (next : Body) :
    eval (constructorUnwindBorrowPrefix address next) frame = eval next (unwindFrameBorrowed frame address) := by
  have bound43 : 43 < frame.slots.length := by omega
  have bound44 : 44 < frame.slots.length := by omega
  have selected : NativeRecordLLBC.read {frame with slots := frame.slots.set 43 (.live none)} 3 [] = some allocatorValue := by
    rw [read_other_slot_set _ _ _ _ _ (by decide)]
    exact global
  simp only [constructorUnwindBorrowPrefix,eval,unwind_storage_live_present frame 43 bound43]
  simp only [evalRvalue,evalZstMutBorrow,selected,allocatorValue,ite_true,
    NativeZstBorrow.issue_exclusive_complete frame.world address nonzero]
  simp [write,type,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,
    bound43,unwind_storage_live_present,List.length_set,bound44,unwindFrameBorrowed]

theorem unwind_frame_arguments (frame : Frame) (address : NativeWord64Memory.Word)
    (length : 54 ≤ frame.slots.length) (type : frame.types[43]? = some (.scalar (.reference true))) :
    evalArgs (unwindFrameBorrowed frame address) [.move 43 []] =
      some ([.scalar (.reference true ⟨frame.world.nextTag⟩ 0)],unwindFrameMoved frame address) := by
  have bound43 : 43 < frame.slots.length := by omega
  simp [unwindFrameBorrowed,unwindFrameMoved,evalArgs,evalOperand,NativeRecordLLBC.read,type,
    List.length_set,bound43,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem unwind_frame_drop (frame : Frame) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (length : 54 ≤ frame.slots.length) (referenceType : frame.types[43]? = some (.scalar (.reference true)))
    (unitType : frame.types[44]? = some (.scalar .unit))
    (global : NativeRecordLLBC.read frame 3 [] = some allocatorValue)
    (valid : NativeReferenceMachine.WellFormed frame.world) (next : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.eval (NativeAllocatorLLBC.Body.legacy (constructorUnwindBorrowPrefix address .done)
      (.call globalDropFunction.name globalDropFunction.classification globalDropFunction.types globalDropFunction.argCount
        44 [.move 43 []] globalDropFunction.body (.legacy constructorUnwindTerminate .done) next)) frame = NativeAllocatorLLBC.eval next (unwindFrameReturned frame address) := by
  have prepared : eval (constructorUnwindBorrowPrefix address .done) frame = .normal (unwindFrameBorrowed frame address) := by
    rw [unwind_frame_borrow frame address nonzero length referenceType global]; rfl
  rw [NativeAllocatorLLBC.legacy_normal _ prepared]
  have called := NativeAllocatorLLBC.eval_call globalDropFunction (unwindFrameBorrowed frame address)
    44 [.move 43 []] (.legacy constructorUnwindTerminate .done) next
  rw [unwind_frame_arguments frame address length referenceType] at called
  simp only at called
  have actual := global_drop_values (NativeZstBorrow.grantedExclusive frame.world address) ⟨frame.world.nextTag⟩
    (NativeZstBorrow.granted_exclusive_wellFormed frame.world address nonzero valid)
  rw [show (unwindFrameMoved frame address).world = NativeZstBorrow.grantedExclusive frame.world address from rfl,actual] at called
  rw [called]
  have bound44 : 44 < frame.slots.length := by omega
  simp [NativeAllocatorLLBC.resume,unwindFrameReturned,unwindFrameMoved,unwindFrameBorrowed,write,unitType,
    List.length_set,bound44,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]


theorem drop_dead_resume (frame : Frame) (indices : List Nat)
    (valid : ∀ index ∈ indices, index < frame.slots.length) :
    eval (dropDead indices .resume) frame = .unwind frame.world := by
  induction indices generalizing frame with
  | nil => rfl
  | cons index rest ih =>
    have bound := valid index List.mem_cons_self
    have killed : storageDead frame index = some {frame with slots := frame.slots.set index .dead} := by
      simp only [storageDead,List.getElem?_eq_getElem bound,Option.map_some]
    simp only [dropDead,List.foldr_cons,eval,killed]
    apply ih
    intro other member
    simpa only [List.length_set] using valid other (List.mem_cons_of_mem index member)

theorem drop_dead_abort (frame : Frame) (indices : List Nat)
    (valid : ∀ index ∈ indices, index < frame.slots.length) :
    eval (dropDead indices .abort) frame = .invalid frame.world := by
  induction indices generalizing frame with
  | nil => rfl
  | cons index rest ih =>
    have bound := valid index List.mem_cons_self
    have killed : storageDead frame index = some {frame with slots := frame.slots.set index .dead} := by
      simp only [storageDead,List.getElem?_eq_getElem bound,Option.map_some]
    simp only [dropDead,List.foldr_cons,eval,killed]
    apply ih
    intro other member
    simpa only [List.length_set] using valid other (List.mem_cons_of_mem index member)

theorem constructor_unwind_cleanup (frame : Frame) (length : 54 ≤ frame.slots.length) :
    eval constructorUnwindCleanup frame = .unwind frame.world := by
  change eval (dropDead constructorUnwindIndices .resume) frame = _
  apply drop_dead_resume
  intro index member
  have bounded := of_decide_eq_true (List.all_eq_true.mp
    (by decide : constructorUnwindIndices.all (fun i => decide (i < 54)) = true) index member)
  omega

theorem constructor_unwind_terminate (frame : Frame) (length : 54 ≤ frame.slots.length) :
    eval constructorUnwindTerminate frame = .invalid frame.world := by
  change eval (dropDead globalDropCleanupIndices .abort) frame = _
  apply drop_dead_abort
  intro index member
  have bounded := of_decide_eq_true (List.all_eq_true.mp
    (by decide : globalDropCleanupIndices.all (fun i => decide (i < 54)) = true) index member)
  omega

theorem constructor_unwind_skip (frame : Frame) (address : NativeWord64Memory.Word) (length : 54 ≤ frame.slots.length)
    (flag : evalBooleanOperand frame (.copy 21 []) = some (false,frame)) :
    NativeAllocatorLLBC.eval (constructorUnwind address) frame = .unwind frame.world := by
  rw [constructorUnwind,NativeAllocatorLLBC.eval,flag]
  change NativeAllocatorLLBC.eval (.legacy constructorUnwindCleanup .done) frame = _
  rw [NativeAllocatorLLBC.legacy_done,constructor_unwind_cleanup frame length]

theorem constructor_unwind_drop (frame : Frame) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (length : 54 ≤ frame.slots.length) (referenceType : frame.types[43]? = some (.scalar (.reference true)))
    (unitType : frame.types[44]? = some (.scalar .unit))
    (global : NativeRecordLLBC.read frame 3 [] = some allocatorValue) (valid : NativeReferenceMachine.WellFormed frame.world)
    (flag : evalBooleanOperand frame (.copy 21 []) = some (true,frame)) :
    NativeAllocatorLLBC.eval (constructorUnwind address) frame = .unwind (NativeZstBorrow.grantedExclusive frame.world address) := by
  rw [constructorUnwind,NativeAllocatorLLBC.eval,flag]
  have dropResult : NativeAllocatorLLBC.eval (constructorUnwindDrop address) frame = .normal (unwindFrameReturned frame address) := by
    rw [constructorUnwindDrop,unwind_frame_drop frame address nonzero length referenceType unitType global valid]
    rfl
  change NativeAllocatorLLBC.continueWith (.legacy constructorUnwindCleanup .done)
    (NativeAllocatorLLBC.eval (constructorUnwindDrop address) frame) = _
  rw [dropResult]
  change NativeAllocatorLLBC.eval (.legacy constructorUnwindCleanup .done) (unwindFrameReturned frame address) = _
  rw [NativeAllocatorLLBC.legacy_done,constructor_unwind_cleanup]
  · rfl
  · simpa only [unwindFrameReturned,unwindFrameMoved,unwindFrameBorrowed,List.length_set] using length

theorem positive_constructor_unwind_entry (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (world : NativeReferenceMachine.State)
    (valid : NativeReferenceMachine.WellFormed world) :
    NativeAllocatorLLBC.eval (constructorUnwind address) {positiveMovedFrame ambient capacity zeroed address with world} =
      .unwind (NativeZstBorrow.grantedExclusive world address) := by
  apply constructor_unwind_drop _ address nonzero
  · cases zeroed <;> simp [positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,layoutAcceptedFrame,positiveAmbient]
  · cases zeroed <;> simp [positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes]
  · cases zeroed <;> simp [positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes]
  · cases zeroed <;>
      simp [positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes,allocatorValue,
        NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,
        NativeRecordValues.compatible,NativeSliceLLBC.fits]
  · exact valid
  · cases zeroed <;>
      simp [positiveMovedFrame,positiveBorrowFrame,positiveModeFrame,layoutAcceptedFrame,positiveAmbient,layoutTypes,
        evalBooleanOperand,evalOperand,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
        NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable]

theorem positive_method_unwind (ambient calleeAmbient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim zero null : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State) (valid : NativeReferenceMachine.WellFormed world)
    (unwound : NativeAllocatorLLBC.invokeValues
      (allocationMethod calleeAmbient zeroed zero (runtimePositive outcome shim null runtimeSuccess))
      (NativeZstBorrow.granted ambient.world address)
      [.scalar (.reference false ⟨ambient.world.nextTag⟩ 0),capacityLayout capacity] = .unwind world) :
    NativeAllocatorLLBC.eval (positiveMethodCall calleeAmbient zeroed outcome shim zero null (constructorUnwind address))
      (positiveBorrowFrame ambient capacity zeroed address) = .unwind (NativeZstBorrow.grantedExclusive world address) := by
  have called := NativeAllocatorLLBC.eval_call
    (allocationMethod calleeAmbient zeroed zero (runtimePositive outcome shim null runtimeSuccess))
    (positiveBorrowFrame ambient capacity zeroed address) 10 (positiveCallArgs zeroed) (constructorUnwind address)
    (.legacy (.dead (if zeroed then 12 else 11) .done) .done)
  rw [positive_call_arguments] at called
  simp only at called
  rw [show (positiveMovedFrame ambient capacity zeroed address).world = NativeZstBorrow.granted ambient.world address from rfl,unwound] at called
  rw [show NativeAllocatorLLBC.eval (positiveMethodCall calleeAmbient zeroed outcome shim zero null (constructorUnwind address))
    (positiveBorrowFrame ambient capacity zeroed address) = _ from called]
  change NativeAllocatorLLBC.eval (constructorUnwind address) {positiveMovedFrame ambient capacity zeroed address with world} = _
  exact positive_constructor_unwind_entry ambient capacity zeroed address nonzero world valid

theorem positive_body_unwind (ambient calleeAmbient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim zero null failure : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State) (valid : NativeReferenceMachine.WellFormed world)
    (unwound : NativeAllocatorLLBC.invokeValues
      (allocationMethod calleeAmbient zeroed zero (runtimePositive outcome shim null runtimeSuccess))
      (NativeZstBorrow.granted ambient.world address)
      [.scalar (.reference false ⟨ambient.world.nextTag⟩ 0),capacityLayout capacity] = .unwind world) :
    NativeAllocatorLLBC.eval (positiveConstructorBody calleeAmbient address outcome shim zero null (constructorUnwind address) failure)
      (layoutAcceptedFrame (positiveAmbient ambient zeroed) capacity) = .unwind (NativeZstBorrow.grantedExclusive world address) := by
  rw [positive_constructor_selection _ _ _ _ _ nonzero,
    positive_method_unwind _ _ _ _ _ nonzero _ _ _ _ _ valid unwound]
  rfl

end HasteBootsVecCapacityArithmetic
