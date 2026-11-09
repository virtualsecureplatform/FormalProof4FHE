namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeRecordDropCalls (Code)
open NativeReferenceMachine (State Reference)
open NativeResidentVec (Descriptor InitializedElements OwnsBuffer)
open NativeVecBytePrefix (Available)
open NativeRecordCallValues

/-- The first retained scope prepares and calls the original byte method. -/
def vecByteBody : Code := .native vecRootParts.1 vecByteCall

theorem vec_byte_resume_unit (entered current : State) (reference : Reference)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger entered))
    (loans : current.leases = entered.leases) :
    NativeRecordDropCalls.resumeCall entered (vecRootFrame entered reference (.live none)) 3
      (.returned (.scalar .unit) current) = .next (vecRootFrame current reference (.live (some (.scalar .unit)))) := by
  simp only [NativeRecordDropCalls.resumeCall,settle_unit_same_loans entered current valid loans]
  simp [vecRootFrame,f1,write,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

/-- The byte-call body completes at the original element extent. Its fresh
whole-object loan remains for the enclosing source scope to close. -/
theorem vec_byte_body_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world) (initialized : InitializedElements descriptor)
    (available : Available world descriptor.buffer descriptor.capacity.val)
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    ∃ current, evalCode vecByteBody (vecGlueEntry world descriptor.reference) =
        some (.normal (vecRootFrame current descriptor.reference (.live (some (.scalar .unit))))) ∧
      NativeReferenceMachine.Reachable current ∧ NativeScopeRestoration.Extends world current ∧
      current.pointers.heap = world.pointers.heap ∧ NativeIncomingReference.Preserves world current := by
  obtain ⟨entered,after,created,capacityEq,lengthEq,bufferEq,enteredReach,enteredFrontier,enteredHeap⟩ :=
    NativeVecDestructionCompleteness.whole_descriptor_complete descriptor reachable frontier
  have enteredInitialized : InitializedElements after := by
    obtain ⟨bytes,loaded⟩ := initialized
    refine ⟨bytes,?_⟩
    rw [lengthEq,bufferEq,enteredHeap]
    exact loaded
  have enteredAvailable : Available entered after.buffer after.capacity.val := by
    rw [bufferEq,capacityEq]
    exact NativeVecDestructionCompleteness.available_reborrow world entered descriptor.buffer descriptor.capacity.val
      _ _ .whole available created
  obtain ⟨current,called,reached,loans,heap⟩ := byte_method_complete after enteredReach enteredInitialized enteredAvailable enteredFrontier
  have calledEntry : evalCode f2.code (vecByteEntry entered after.reference) = some (.returned (.scalar .unit) current) := called
  have preserved := evalCode_incoming f2.code (vecByteEntry entered after.reference) (.returned (.scalar .unit) current) calledEntry
  have first := NativeVecDestructionCompleteness.reborrow_extends world (.reference true descriptor.reference 3) .whole
  rw [created] at first
  have second : NativeScopeRestoration.Extends entered current :=
    ⟨preserved.counter,[],by simpa only [List.nil_append] using loans,by simp⟩
  have incoming := NativeVecReference.reborrow_incoming_projects world (.reference true descriptor.reference 3) .whole
  rw [created] at incoming
  refine ⟨current,?_,reached,first.trans second,heap.trans enteredHeap,incoming.trans preserved⟩
  rw [vecByteBody,evalCode.eq_2,vec_root_prefix_value world entered descriptor.reference after.reference created]
  change evalCode vecByteCall (vecByteCaller entered descriptor.reference after.reference) = _
  rw [vecByteCall,evalCode.eq_4,vec_byte_call_prepared]
  have entryWorld : (vecByteEntry entered after.reference).world = entered := rfl
  simp only [calledEntry,entryWorld,vec_byte_resume_unit entered current descriptor.reference
    (NativeReferenceMachine.reachable_wellFormed entered enteredReach).2.1 loans,evalCode.eq_1]

def vecRawReturned (world : State) (reference : Reference) : Frame :=
  ⟨f1.types,[.live (some (.scalar .unit)),.live (some (.scalar (.reference true reference 3))),
    .live (some .uninit),.live (some (.scalar .unit)),.dead,.dead,.live (some .uninit),.live (some (.scalar .unit))],world⟩

theorem vec_raw_resume_unit (entered current : State) (reference child : Reference) (flow : Flow)
    (settled : settle entered flow = .returned (.scalar .unit) current) :
    NativeRecordDropCalls.resumeCall entered
      (vecRawConsumed false entered reference child (.live (some (.scalar .unit)))) 7 flow =
      .next (vecRawReturned current reference) := by
  cases flow with
  | normal frame => cases settled
  | unwind world => cases settled
  | invalid world => cases settled
  | unsupported source world => cases settled
  | returned value world =>
    simp only [NativeRecordDropCalls.resumeCall,settled]
    simp [vecRawConsumed,vecRawCaller,vecRawLocal,vecRawReturned,f1,write,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem vec_raw_finish_unit (world : State) (reference : Reference) :
    eval (vecRawBodies false).2.2 (vecRawReturned world reference) = .returned (.scalar .unit) world := by
  simp [vecRawBodies,vecRawStageBodies,vecRawStage,vecRootParts,vecRootStages,vecRawReturned,f1,
    eval,storageDead,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

/-- The normal RawVec scope calls the proved glue and closes its own field loan. -/
theorem vec_raw_stage_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world)
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease)
    (available : Available world descriptor.buffer descriptor.capacity.val)
    (owned : descriptor.capacity = 0 ∨ ∃ block ∈ world.pointers.heap.memory.blocks,
      block.pointer = descriptor.buffer ∧ block.layout = ⟨descriptor.capacity.val,1⟩) :
    ∃ final, evalCode (vecRawStage false)
        (vecRootFrame world descriptor.reference (.live (some (.scalar .unit)))) = some (.returned (.scalar .unit) final) ∧
      NativeReferenceMachine.Reachable final ∧ final.leases = world.leases ∧
      (if descriptor.capacity = 0 then final.pointers.heap = world.pointers.heap else
        NativePointerByteMemory.deallocate world.pointers.heap descriptor.buffer ⟨descriptor.capacity.val,1⟩ = some final.pointers.heap) := by
  obtain ⟨entered,created,⟨ready⟩,enteredHeap⟩ := NativeVecDestructionCompleteness.rawvec_ready_complete descriptor reachable frontier
  have enteredAvailable := NativeVecDestructionCompleteness.available_reborrow world entered descriptor.buffer descriptor.capacity.val
    _ _ .rawVec available created
  have enteredOwned : descriptor.capacity = 0 ∨ ∃ block ∈ entered.pointers.heap.memory.blocks,
      block.pointer = descriptor.buffer ∧ block.layout = ⟨descriptor.capacity.val,1⟩ := by
    rcases owned with zero | ⟨block,member,base,extent⟩
    · exact Or.inl zero
    · exact Or.inr ⟨block,by rw [enteredHeap]; exact member,base,extent⟩
  obtain ⟨current,called,loans,reached,effect⟩ := rawvec_glue_complete entered ⟨world.nextTag⟩ descriptor.capacity descriptor.length descriptor.buffer
    ready enteredAvailable enteredOwned
  have incoming := NativeRecordLLBC.invoke_incoming_projects HasteBootsRawVecDrop.f4 entered
    [.rawVecExclusiveReference (entered.references.idxOf ⟨world.nextTag⟩)]
  rw [← rawvec_values_eq HasteBootsRawVecDrop.f4 entered ⟨world.nextTag⟩ ready.lease.pointer descriptor.buffer
    descriptor.capacity descriptor.length ready.resident,called] at incoming
  have first := NativeVecDestructionCompleteness.reborrow_extends world (.reference true descriptor.reference 3) .rawVec
  rw [created] at first
  have second : NativeScopeRestoration.Extends entered current :=
    ⟨incoming.counter,[],by simpa only [List.nil_append] using loans,by simp⟩
  have restored := NativeScopeRestoration.closeScope_reachable_restores world current (first.trans second)
    (NativeReferenceMachine.reachable_wellFormed world reachable).2.1 reached
  let final := (NativeReferenceCleanup.closeScope world current).world
  have heap : final.pointers.heap = current.pointers.heap :=
    (NativeReferenceCleanup.closeScope_heap_projects world current).heap_eq
  have settled : settle entered (eval HasteBootsRawVecDrop.f4.body (rawvecGlueEntry entered ⟨world.nextTag⟩)) =
      .returned (.scalar .unit) current := by
    rw [invokeValues_initialized HasteBootsRawVecDrop.f4 entered _ (rawvecGlueEntry entered ⟨world.nextTag⟩)
      (rawvec_glue_initial entered ⟨world.nextTag⟩)] at called
    exact called
  have body : evalCode (.native (vecRawBodies false).1 (vecRawCall false))
      (vecRootFrame world descriptor.reference (.live (some (.scalar .unit)))) =
      some (.normal (vecRawReturned current descriptor.reference)) := by
    rw [evalCode.eq_2,vec_raw_prefix_value false world entered descriptor.reference ⟨world.nextTag⟩ _ created]
    change evalCode (vecRawCall false) (vecRawCaller false entered descriptor.reference ⟨world.nextTag⟩
      (.live (some (.scalar .unit)))) = _
    rw [vecRawCall,evalCode.eq_4,vec_raw_call_prepared]
    have entryWorld : (rawvecGlueEntry entered ⟨world.nextTag⟩).world = entered := rfl
    have resumed : NativeRecordDropCalls.resumeCall entered
        (vecRawConsumed false entered descriptor.reference ⟨world.nextTag⟩ (.live (some (.scalar .unit))))
        (vecRawLocal false + 1) (eval HasteBootsRawVecDrop.f4.body (rawvecGlueEntry entered ⟨world.nextTag⟩)) =
        .next (vecRawReturned current descriptor.reference) :=
      vec_raw_resume_unit entered current descriptor.reference ⟨world.nextTag⟩ _ settled
    simp only [rawvec_glue_code_eval,entryWorld,resumed,evalCode.eq_1]
  refine ⟨final,?_,NativeReferenceCleanup.closeScope_reachable world current reached,restored.2,?_⟩
  · rw [vec_raw_stage_code false,evalCode.eq_3]
    change (match evalCode (.native (vecRawBodies false).1 (vecRawCall false))
      (vecRootFrame world descriptor.reference (.live (some (.scalar .unit)))) with
      | none => none
      | some returned => match NativeRecordDropCalls.resumeScope world returned with
        | .normal changed => evalCode (.native (vecRawBodies false).2.2 .done) changed
        | flow => some flow) = _
    rw [body]
    have currentWorld : (vecRawReturned current descriptor.reference).world = current := rfl
    simp only [NativeRecordDropCalls.resumeScope,currentWorld,restored.1,List.isEmpty_nil,ite_true]
    change evalCode (.native (vecRawBodies false).2.2 .done) (vecRawReturned final descriptor.reference) = _
    simp only [native_done_eval,vec_raw_finish_unit]
  · by_cases zero : descriptor.capacity = 0
    · rw [ite_eq_left zero] at effect ⊢
      exact heap.trans (effect.trans enteredHeap)
    · rw [ite_eq_right zero] at effect ⊢
      rw [heap]
      rw [enteredHeap] at effect
      exact effect

/-- Full retained outer Vec destruction under explicit resident Vec conditions. -/
theorem vec_glue_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world) (initialized : InitializedElements descriptor)
    (available : Available world descriptor.buffer descriptor.capacity.val)
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease)
    (owned : OwnsBuffer descriptor) :
    ∃ final, evalCode f1.code (vecGlueEntry world descriptor.reference) = some (.returned (.scalar .unit) final) ∧
      NativeReferenceMachine.Reachable final ∧ final.leases = world.leases ∧
      (if descriptor.capacity = 0 then final.pointers.heap = world.pointers.heap else
        NativePointerByteMemory.deallocate world.pointers.heap descriptor.buffer ⟨descriptor.capacity.val,1⟩ = some final.pointers.heap) := by
  obtain ⟨current,body,reached,extended,heap,preserved⟩ :=
    vec_byte_body_complete descriptor reachable initialized available frontier
  have restored := NativeScopeRestoration.closeScope_reachable_restores world current extended
    (NativeReferenceMachine.reachable_wellFormed world reachable).2.1 reached
  let middle := (NativeReferenceCleanup.closeScope world current).world
  have middleHeap : middle.pointers.heap = world.pointers.heap :=
    (NativeReferenceCleanup.closeScope_heap_projects world current).heap_eq.trans heap
  have middleIncoming := NativeIncomingReference.closeScope world current preserved
  have registered : NativeByteBorrow.lookup middle.leases descriptor.reference.tag = some descriptor.lease := by
    rw [restored.2]; exact descriptor.registered
  let after := NativeVecDestructionCompleteness.reframe descriptor middle middleHeap registered
    (middleIncoming.references descriptor.reference (List.mem_of_getElem? descriptor.resident))
    (middleIncoming.registers descriptor.lease.pointer (List.mem_of_getElem? descriptor.baseResident))
  have middleFrontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger middle) after.lease :=
    NativeBorrowFrontier.frontier_transport _ _ descriptor.lease frontier restored.2
  have middleAvailable : Available middle after.buffer after.capacity.val :=
    NativeRawVecDeallocationCompleteness.available_same_loans world middle descriptor.buffer descriptor.capacity.val available restored.2
  have middleOwned : after.capacity = 0 ∨ ∃ block ∈ middle.pointers.heap.memory.blocks,
      block.pointer = after.buffer ∧ block.layout = ⟨after.capacity.val,1⟩ := by
    rcases owned with zero | ⟨_,block,member,base,extent⟩
    · exact Or.inl (Fin.ext zero)
    · right
      exact ⟨block,by rw [middleHeap]; exact member,base,extent⟩
  obtain ⟨final,tail,finalReach,finalLoans,effect⟩ := vec_raw_stage_complete after
    (NativeReferenceCleanup.closeScope_reachable world current reached) middleFrontier middleAvailable middleOwned
  refine ⟨final,?_,finalReach,finalLoans.trans restored.2,?_⟩
  · rw [vec_root_code,evalCode.eq_3]
    change (match evalCode vecByteBody (vecGlueEntry world descriptor.reference) with
      | none => none
      | some returned => match NativeRecordDropCalls.resumeScope world returned with
        | .normal changed => evalCode (vecRawStage false) changed
        | flow => some flow) = _
    rw [body]
    have currentWorld : (vecRootFrame current descriptor.reference (.live (some (.scalar .unit)))).world = current := rfl
    simp only [NativeRecordDropCalls.resumeScope,currentWorld,restored.1,List.isEmpty_nil,ite_true]
    exact tail
  · change (if descriptor.capacity = 0 then final.pointers.heap = middle.pointers.heap else
      NativePointerByteMemory.deallocate middle.pointers.heap descriptor.buffer ⟨descriptor.capacity.val,1⟩ = some final.pointers.heap) at effect
    rw [middleHeap] at effect
    exact effect

theorem vec_glue_invokes_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world) (initialized : InitializedElements descriptor)
    (available : Available world descriptor.buffer descriptor.capacity.val)
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease)
    (owned : OwnsBuffer descriptor) :
    ∃ final, NativeRecordDropCalls.Invokes f1 world [.vectorExclusiveReference (world.references.idxOf descriptor.reference)]
        (.returned (.scalar .unit) final) ∧ NativeReferenceMachine.Reachable final ∧ final.leases = world.leases ∧
      (if descriptor.capacity = 0 then final.pointers.heap = world.pointers.heap else
        NativePointerByteMemory.deallocate world.pointers.heap descriptor.buffer ⟨descriptor.capacity.val,1⟩ = some final.pointers.heap) := by
  obtain ⟨final,computed,reached,loans,effect⟩ := vec_glue_complete descriptor reachable initialized available frontier owned
  have decoded := vec_resident_decode world descriptor.reference descriptor.lease.pointer descriptor.buffer
    descriptor.capacity descriptor.length (NativeResidentVecBorrow.descriptor_resident descriptor)
  have invoked : invokeCode f1 world [.vectorExclusiveReference (world.references.idxOf descriptor.reference)] =
      some (.returned (.scalar .unit) final) := by
    simp only [invokeCode,decodeArgs,decode,decoded,Option.map_some,Option.bind_eq_bind',Option.bind_some,pure,
      vec_glue_initial,computed,settle_unit_same_loans world final
        (NativeReferenceMachine.reachable_wellFormed world reachable).2.1 loans]
  exact ⟨final,invokeCode_sound f1 world _ _ invoked,reached,loans,effect⟩

theorem vec_glue_invokes_unit {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world) (initialized : InitializedElements descriptor)
    (available : Available world descriptor.buffer descriptor.capacity.val)
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease)
    (owned : OwnsBuffer descriptor)
    (flow : Flow) (invoked : NativeRecordDropCalls.Invokes f1 world
      [.vectorExclusiveReference (world.references.idxOf descriptor.reference)] flow) :
    ∃ final, flow = .returned (.scalar .unit) final ∧ NativeReferenceMachine.Reachable final ∧ final.leases = world.leases ∧
      (if descriptor.capacity = 0 then final.pointers.heap = world.pointers.heap else
        NativePointerByteMemory.deallocate world.pointers.heap descriptor.buffer ⟨descriptor.capacity.val,1⟩ = some final.pointers.heap) := by
  obtain ⟨final,expected,reached,loans,effect⟩ := vec_glue_invokes_complete descriptor reachable initialized available frontier owned
  exact ⟨final,NativeRecordDropCalls.invokes_deterministic f1 world _ _ _ invoked expected,reached,loans,effect⟩

theorem vec_execute_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world) (initialized : InitializedElements descriptor)
    (available : Available world descriptor.buffer descriptor.capacity.val)
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease)
    (owned : OwnsBuffer descriptor) :
    ∃ final, execute world [.vectorExclusiveReference (world.references.idxOf descriptor.reference)] =
        .returned (.scalar .unit) final ∧ NativeReferenceMachine.Reachable final ∧ final.leases = world.leases ∧
      (if descriptor.capacity = 0 then final.pointers.heap = world.pointers.heap else
        NativePointerByteMemory.deallocate world.pointers.heap descriptor.buffer ⟨descriptor.capacity.val,1⟩ = some final.pointers.heap) := by
  obtain ⟨final,invoked,reached,loans,effect⟩ := vec_glue_invokes_complete descriptor reachable initialized available frontier owned
  exact ⟨final,((invocation_iff_execute world _ _).mp invoked).symm,reached,loans,effect⟩

end HasteBootsVecDrop
