namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

def dropDead (indices : List Nat) (next : Body) : Body := indices.foldr Body.dead next

theorem read_other_slot_set (frame : Frame) (index selected : Nat) (slot : Slot) (path : NativeRecordValues.Path)
    (different : selected ≠ index) :
    NativeRecordLLBC.read {frame with slots := frame.slots.set index slot} selected path = NativeRecordLLBC.read frame selected path := by
  simp only [NativeRecordLLBC.read,List.getElem?_set_ne (Ne.symm different)]

theorem drop_dead_returns (frame : Frame) (indices : List Nat) (value : NativeRecordValues.Value)
    (result : NativeRecordLLBC.read frame 0 [] = some value)
    (valid : ∀ index ∈ indices, index < frame.slots.length ∧ 0 ≠ index) :
    eval (dropDead indices .ret) frame = .returned value frame.world := by
  induction indices generalizing frame with
  | nil => simp only [dropDead,List.foldr_nil,eval,result]
  | cons index rest ih =>
    have bound := (valid index List.mem_cons_self).1
    have different := (valid index List.mem_cons_self).2
    have killed : storageDead frame index = some {frame with slots := frame.slots.set index .dead} := by
      simp only [storageDead,List.getElem?_eq_getElem bound,Option.map_some]
    simp only [dropDead,List.foldr_cons,eval,killed]
    apply ih
    · rw [read_other_slot_set _ _ _ _ _ different]
      exact result
    · intro other member
      simpa only [List.length_set] using valid other (List.mem_cons_of_mem index member)

def dropFrameBorrowed (frame : Frame) (address : NativeWord64Memory.Word) : Frame :=
  let opened := frame.slots.set 41 (.live none)
  let stored := opened.set 41 (.live (some (.scalar (.reference true ⟨frame.world.nextTag⟩ 0))))
  {frame with slots := stored.set 42 (.live none),world := NativeZstBorrow.grantedExclusive frame.world address}

def dropFrameMoved (frame : Frame) (address : NativeWord64Memory.Word) : Frame :=
  let base := dropFrameBorrowed frame address
  {base with slots := base.slots.set 41 (.live (some .uninit))}

def dropFrameReturned (frame : Frame) (address : NativeWord64Memory.Word) : Frame :=
  let base := dropFrameMoved frame address
  {base with slots := base.slots.set 42 (.live (some (.scalar .unit)))}

theorem storage_live_present (frame : Frame) (index : Nat) (bound : index < frame.slots.length) :
    storageLive frame index = some {frame with slots := frame.slots.set index (.live none)} := by
  simp only [storageLive,List.getElem?_eq_getElem bound,Option.map_some]

theorem drop_frame_borrow (frame : Frame) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (length : 54 ≤ frame.slots.length) (type : frame.types[41]? = some (.scalar (.reference true)))
    (global : NativeRecordLLBC.read frame 3 [] = some allocatorValue) (next : Body) :
    eval (globalDropBorrowPrefix address next) frame = eval next (dropFrameBorrowed frame address) := by
  have bound41 : 41 < frame.slots.length := by omega
  have bound42 : 42 < frame.slots.length := by omega
  have selected : NativeRecordLLBC.read {frame with slots := frame.slots.set 41 (.live none)} 3 [] = some allocatorValue := by
    rw [read_other_slot_set _ _ _ _ _ (by decide)]
    exact global
  simp only [globalDropBorrowPrefix,eval,storage_live_present frame 41 bound41]
  simp only [evalRvalue,evalZstMutBorrow,selected,allocatorValue,ite_true,
    NativeZstBorrow.issue_exclusive_complete frame.world address nonzero]
  simp [write,type,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,
    bound41,storage_live_present,List.length_set,bound42,dropFrameBorrowed]

theorem drop_frame_arguments (frame : Frame) (address : NativeWord64Memory.Word)
    (length : 54 ≤ frame.slots.length) (type : frame.types[41]? = some (.scalar (.reference true))) :
    evalArgs (dropFrameBorrowed frame address) [.move 41 []] =
      some ([.scalar (.reference true ⟨frame.world.nextTag⟩ 0)],dropFrameMoved frame address) := by
  have bound41 : 41 < frame.slots.length := by omega
  simp [dropFrameBorrowed,dropFrameMoved,evalArgs,evalOperand,NativeRecordLLBC.read,type,
    List.length_set,bound41,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem drop_frame_resumes (frame : Frame) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (length : 54 ≤ frame.slots.length) (referenceType : frame.types[41]? = some (.scalar (.reference true)))
    (unitType : frame.types[42]? = some (.scalar .unit))
    (global : NativeRecordLLBC.read frame 3 [] = some allocatorValue)
    (valid : NativeReferenceMachine.WellFormed frame.world) (next : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.eval (globalDropCall address next) frame = NativeAllocatorLLBC.eval next (dropFrameReturned frame address) := by
  have prepared : eval (globalDropBorrowPrefix address .done) frame = .normal (dropFrameBorrowed frame address) := by
    rw [drop_frame_borrow frame address nonzero length referenceType global]; rfl
  rw [globalDropCall,NativeAllocatorLLBC.legacy_normal _ prepared]
  have called := NativeAllocatorLLBC.eval_call globalDropFunction (dropFrameBorrowed frame address)
    42 [.move 41 []] (.legacy globalDropUnwind .done) next
  rw [drop_frame_arguments frame address length referenceType] at called
  simp only at called
  have actual := global_drop_values (NativeZstBorrow.grantedExclusive frame.world address) ⟨frame.world.nextTag⟩
    (NativeZstBorrow.granted_exclusive_wellFormed frame.world address nonzero valid)
  rw [show (dropFrameMoved frame address).world = NativeZstBorrow.grantedExclusive frame.world address from rfl,actual] at called
  rw [called]
  have bound42 : 42 < frame.slots.length := by omega
  simp [NativeAllocatorLLBC.resume,dropFrameReturned,dropFrameMoved,dropFrameBorrowed,write,unitType,
    List.length_set,bound42,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem drop_frame_cleanup (frame : Frame) (address : NativeWord64Memory.Word) (value : NativeRecordValues.Value)
    (length : 54 ≤ frame.slots.length) (result : NativeRecordLLBC.read frame 0 [] = some value) :
    eval globalDropCleanup (dropFrameReturned frame address) = .returned value (NativeZstBorrow.grantedExclusive frame.world address) := by
  have resultAfter : NativeRecordLLBC.read (dropFrameReturned frame address) 0 [] = some value := by
    simpa only [dropFrameReturned,dropFrameMoved,dropFrameBorrowed,NativeRecordLLBC.read,
      List.getElem?_set_ne (by decide : 41 ≠ 0),List.getElem?_set_ne (by decide : 42 ≠ 0)] using result
  change eval (dropDead globalDropCleanupIndices .ret) (dropFrameReturned frame address) = _
  apply drop_dead_returns _ _ _ resultAfter
  intro index member
  have checked := List.all_eq_true.mp (by decide : globalDropCleanupIndices.all (fun i => decide (i < 54 ∧ 0 ≠ i)) = true) index member
  have bounded := of_decide_eq_true checked
  simp only [dropFrameReturned,dropFrameMoved,dropFrameBorrowed,List.length_set]
  exact ⟨lt_of_lt_of_le bounded.1 length,bounded.2⟩

theorem drop_frame_returns (frame : Frame) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (length : 54 ≤ frame.slots.length) (referenceType : frame.types[41]? = some (.scalar (.reference true)))
    (unitType : frame.types[42]? = some (.scalar .unit))
    (global : NativeRecordLLBC.read frame 3 [] = some allocatorValue)
    (value : NativeRecordValues.Value) (result : NativeRecordLLBC.read frame 0 [] = some value)
    (valid : NativeReferenceMachine.WellFormed frame.world) :
    NativeAllocatorLLBC.eval (globalDropCall address (.legacy globalDropCleanup .done)) frame =
      .returned value (NativeZstBorrow.grantedExclusive frame.world address) := by
  rw [drop_frame_resumes frame address nonzero length referenceType unitType global valid,
    NativeAllocatorLLBC.legacy_done,drop_frame_cleanup frame address value length result]

end HasteBootsVecCapacityArithmetic
