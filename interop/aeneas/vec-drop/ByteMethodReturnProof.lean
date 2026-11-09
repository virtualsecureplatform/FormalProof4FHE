namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeRecordDropCalls (Code)
open NativeReferenceMachine (State Reference)
open NativeByteSliceIndex (Slice)
open NativeResidentVec (Descriptor InitializedElements)
open NativeVecBytePrefix

/-- An already restored incoming loan list makes unit-return cleanup inert. -/
theorem close_scope_same_loans (entered current : State)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger entered)) (same : current.leases = entered.leases) :
    NativeReferenceCleanup.closeScope entered current = ⟨current,[],[]⟩ := by
  have none : entered.leases.filter (fun lease => decide (entered.nextTag ≤ lease.tag)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro lease member
    have age : lease.tag < entered.nextTag := (valid.1 lease member).1
    simpa only [decide_eq_true_eq] using (show ¬ entered.nextTag ≤ lease.tag by omega)
  simp only [NativeReferenceCleanup.closeScope,NativeReferenceCleanup.scopeTags,same,none,List.map_nil,NativeReferenceCleanup.release]

theorem settle_unit_same_loans (entered current : State)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger entered)) (same : current.leases = entered.leases) :
    settle entered (.returned (.scalar .unit) current) = .returned (.scalar .unit) current := by
  simp only [settle,NativeReferenceCleanup.settleUnit,close_scope_same_loans entered current valid same,List.isEmpty_nil,ite_true]

theorem extends_same_loans (before after : State) (counter : before.nextTag ≤ after.nextTag) (same : after.leases = before.leases) :
    NativeScopeRestoration.Extends before after := ⟨counter,[],by simpa only [List.nil_append] using same,by simp⟩

def sliceHelperStages : Code → Option (Body × Body)
  | .scope (.native prepare (.call _ _ _ _ _ _ _ _ .done)) (.native finish .done) => some (prepare,finish)
  | _ => none

def sliceHelperPieces : Body × Body := (sliceHelperStages f3.code).get (by decide)

theorem slice_helper_code : f3.code =
    .scope (.native sliceHelperPieces.1
      (.call f6.name f6.classification f6.types f6.argCount 3 [.move 2 []] f6.code
        (.native (.dead 1 .resume) .done) .done)) (.native sliceHelperPieces.2 .done) := by rfl

def sliceHelperEntry (world : State) (slice : Slice) : Frame :=
  ⟨f3.types,[.dead,.live (some (.scalar (.reference true slice.reference slice.length))),.dead,.dead],world⟩
def sliceHelperCaller (world : State) (slice : Slice) (child : Reference) : Frame :=
  ⟨f3.types,[.live (some (.scalar .unit)),.live (some (.scalar (.reference true slice.reference slice.length))),
    .live (some (.scalar (.reference true child slice.length))),.live none],world⟩
def sliceHelperConsumed (world : State) (slice : Slice) : Frame :=
  ⟨f3.types,[.live (some (.scalar .unit)),.live (some (.scalar (.reference true slice.reference slice.length))),
    .live (some .uninit),.live none],world⟩
def sliceHelperReturned (world : State) (slice : Slice) : Frame :=
  ⟨f3.types,[.live (some (.scalar .unit)),.live (some (.scalar (.reference true slice.reference slice.length))),
    .live (some .uninit),.live (some (.scalar .unit))],world⟩
def sliceLoopEntry (world : State) (slice : Slice) : Frame :=
  ⟨f6.types,[.dead,.live (some (.scalar (.reference true slice.reference slice.length)))],world⟩

theorem slice_helper_prepare (world next : State) (slice : Slice)
    (issued : NativeSliceLLBC.issue world true (.reference true slice.reference slice.length) .byte =
      some (.reference true ⟨world.nextTag⟩ slice.length,next)) :
    eval sliceHelperPieces.1 (sliceHelperEntry world slice) = .normal (sliceHelperCaller next slice ⟨world.nextTag⟩) := by
  simp [sliceHelperPieces,sliceHelperStages,f3,sliceHelperEntry,sliceHelperCaller,eval,evalRvalue,evalArgs,
    evalBorrowSlice,storageLive,write,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,issued]

theorem slice_loop_prepared (world : State) (slice : Slice) (child : Reference) :
    NativeRecordDropCalls.prepareCall (sliceHelperCaller world slice child) f6.types f6.argCount [.move 2 []] =
      some (sliceHelperConsumed world slice,sliceLoopEntry world ⟨child,slice.length⟩) := by
  simp [NativeRecordDropCalls.prepareCall,sliceHelperCaller,sliceHelperConsumed,sliceLoopEntry,f3,f6,evalArgs,evalOperand,
    NativeRecordValues.replace,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,initial]

theorem slice_loop_eval (world : State) (slice : Slice) (ready : NativeByteTraversalCompleteness.Ready world slice) :
    evalCode f6.code (sliceLoopEntry world slice) = some (.returned (.scalar .unit) (NativeByteDropTraversal.run world slice).world) := by
  have argument : NativeRecordDropCalls.loopArgument (sliceLoopEntry world slice) = some slice := by
    simp [NativeRecordDropCalls.loopArgument,sliceLoopEntry,f6,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]
  change evalCode (.loop .transparent HasteBootsVecByteLoop.f6) (sliceLoopEntry world slice) = _
  simpa only [(loopOutcome_complete_ready world slice ready).1] using
    (show evalCode (.loop .transparent HasteBootsVecByteLoop.f6) (sliceLoopEntry world slice) = some (loopOutcome world slice) by
      simp only [evalCode,ite_true,argument]
      rfl)

theorem slice_loop_resume (entered final : State) (slice : Slice)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger entered)) (same : final.leases = entered.leases) :
    NativeRecordDropCalls.resumeCall entered (sliceHelperConsumed entered slice) 3 (.returned (.scalar .unit) final) =
      .next (sliceHelperReturned final slice) := by
  simp only [NativeRecordDropCalls.resumeCall,settle_unit_same_loans entered final valid same]
  simp [sliceHelperConsumed,sliceHelperReturned,f3,write,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem slice_helper_finish (world : State) (slice : Slice) :
    eval sliceHelperPieces.2 (sliceHelperReturned world slice) = .returned (.scalar .unit) world := by
  simp [sliceHelperPieces,sliceHelperStages,sliceHelperReturned,f3,eval,storageDead,NativeRecordLLBC.read,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

/-- The retained helper returns unit and restores all incoming loans after its
actual nested loop call. No successful cleanup or callee outcome is assumed. -/
theorem slice_helper_complete (world : State) (slice : Slice) (ready : NativeByteTraversalCompleteness.Ready world slice) :
    ∃ final, evalCode f3.code (sliceHelperEntry world slice) = some (.returned (.scalar .unit) final) ∧
      NativeReferenceMachine.Reachable final ∧ final.leases = world.leases ∧ final.pointers.heap = world.pointers.heap := by
  obtain ⟨next,issued,nextReady⟩ := NativeByteTraversalCompleteness.issue_complete world slice ready
  let child : Slice := ⟨⟨world.nextTag⟩,slice.length⟩
  let loopFinal := (NativeByteDropTraversal.run next child).world
  have run := NativeByteTraversalCompleteness.run_complete next child nextReady
  have loopReachable : NativeReferenceMachine.Reachable loopFinal := run.2.1.1
  have counter := (NativeIncomingReference.run next child).counter
  have extended := (NativeScopeRestoration.issue world next true _ _ .byte issued).trans
    (extends_same_loans next loopFinal counter run.2.2.1)
  have restored := NativeScopeRestoration.closeScope_reachable_restores world loopFinal extended
    (NativeReferenceMachine.reachable_wellFormed world ready.1).2.1 loopReachable
  let final := (NativeReferenceCleanup.closeScope world loopFinal).world
  have evaluated : evalCode f3.code (sliceHelperEntry world slice) = some (.returned (.scalar .unit) final) := by
    rw [slice_helper_code,evalCode.eq_3]
    have body : evalCode (.native sliceHelperPieces.1
        (.call f6.name f6.classification f6.types f6.argCount 3 [.move 2 []] f6.code (.native (.dead 1 .resume) .done) .done))
        (sliceHelperEntry world slice) = some (.normal (sliceHelperReturned loopFinal slice)) := by
      rw [evalCode.eq_2,slice_helper_prepare world next slice issued]
      have called : evalCode f6.code (sliceLoopEntry next ⟨⟨world.nextTag⟩,slice.length⟩) =
          some (.returned (.scalar .unit) loopFinal) := slice_loop_eval next child nextReady
      have entryWorld : (sliceLoopEntry next ⟨⟨world.nextTag⟩,slice.length⟩).world = next := rfl
      have resumed := slice_loop_resume next loopFinal slice (NativeReferenceMachine.reachable_wellFormed next nextReady.1).2.1 run.2.2.1
      simp only [evalCode.eq_4,slice_loop_prepared,called,entryWorld,resumed,evalCode.eq_1]
    rw [body]
    simp only [NativeRecordDropCalls.resumeScope,sliceHelperEntry,sliceHelperReturned,restored.1,List.isEmpty_nil,ite_true]
    change evalCode (.native sliceHelperPieces.2 .done) (sliceHelperReturned final slice) = some (.returned (.scalar .unit) final)
    simp only [evalCode.eq_2,slice_helper_finish]
  refine ⟨final,evaluated,NativeReferenceCleanup.closeScope_reachable world loopFinal loopReachable,restored.2,?_⟩
  exact (NativeReferenceCleanup.closeScope_heap_projects world loopFinal).heap_eq.trans
    ((NativeByteDropTraversal.run_heap_frame next child).trans (NativeSliceLLBC.issue_heap_projects world next true _ _ issued).heap_eq)

theorem byte_borrow_from_issue {world : State} {index : Nat} (descriptor : Descriptor world index) (next : State)
    (issued : NativeSliceLLBC.issue (lengthWorld descriptor) true (.raw ⟨descriptor.buffer,some descriptor.length⟩) .byte =
      some (.reference true ⟨world.nextTag⟩ descriptor.length,next)) :
    eval byteBorrowBody (bytePartsFrame descriptor) = .normal (byteBorrowCaller descriptor next) := by
  simp [byteBorrowBody,byteMethodPieces,byteMethodStages,f2,bytePartsFrame,byteFieldsFrame,byteBorrowCaller,
    eval,evalRvalue,evalBorrowSlice,storageLive,storageDead,write,NativeRecordLLBC.read,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits,issued]

def byteReturnedFrame {world : State} {index : Nat} (descriptor : Descriptor world index) (entered final : State) : Frame :=
  {byteCallConsumed descriptor entered with world := final}

theorem byte_call_resume {world : State} {index : Nat} (descriptor : Descriptor world index) (entered final : State)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger entered)) (same : final.leases = entered.leases) :
    NativeRecordDropCalls.resumeCall entered (byteCallConsumed descriptor entered) 0 (.returned (.scalar .unit) final) =
      .next (byteReturnedFrame descriptor entered final) := by
  simp only [NativeRecordDropCalls.resumeCall,settle_unit_same_loans entered final valid same]
  simp [byteCallConsumed,byteBorrowCaller,byteReturnedFrame,f2,write,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem byte_after_finish {world : State} {index : Nat} (descriptor : Descriptor world index) (entered final : State) :
    evalCode byteAfterCode (byteReturnedFrame descriptor entered final) = some (.returned (.scalar .unit) final) := by
  simp [byteAfterCode,byteMethodPieces,byteMethodStages,byteReturnedFrame,byteCallConsumed,byteBorrowCaller,f2,
    evalCode,eval,storageDead,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

/-- The actual byte-method body returns unit under resident, initialized and
alias-available Vec conditions, restoring its incoming loans and full heap. -/
theorem byte_method_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world) (initialized : InitializedElements descriptor)
    (available : Available world descriptor.buffer descriptor.capacity.val)
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    ∃ final, evalCode f2.code (byteMethodEntry world descriptor.reference) = some (.returned (.scalar .unit) final) ∧
      NativeReferenceMachine.Reachable final ∧ final.leases = world.leases ∧ final.pointers.heap = world.pointers.heap := by
  obtain ⟨next,issued,nextReady⟩ := fields_issue_ready descriptor reachable initialized available frontier
  obtain ⟨helperFinal,helperRun,helperReachable,helperLoans,helperHeap⟩ :=
    slice_helper_complete next ⟨⟨world.nextTag⟩,descriptor.length⟩ nextReady
  have helperCode : evalCode f3.code (byteForeignEntry descriptor next) = some (.returned (.scalar .unit) helperFinal) := helperRun
  have helperCounter : next.nextTag ≤ helperFinal.nextTag :=
    (evalCode_incoming f3.code (byteForeignEntry descriptor next) (.returned (.scalar .unit) helperFinal) helperCode).counter
  have extended := (NativeScopeRestoration.issue (lengthWorld descriptor) next true _ _ .byte issued).trans
    (extends_same_loans next helperFinal helperCounter helperLoans)
  have valid := NativeReferenceMachine.reachable_wellFormed world reachable
  have restored := NativeScopeRestoration.closeScope_reachable_restores (lengthWorld descriptor) helperFinal extended valid.2.1 helperReachable
  let final := (NativeReferenceCleanup.closeScope (lengthWorld descriptor) helperFinal).world
  have called : evalCode byteCallCode (byteBorrowCaller descriptor next) = some (.normal (byteReturnedFrame descriptor next helperFinal)) := by
    rw [byte_call_code,evalCode.eq_4,byte_call_prepared]
    have entryWorld : (byteForeignEntry descriptor next).world = next := rfl
    simp only [helperCode,entryWorld,byte_call_resume descriptor next helperFinal
      (NativeReferenceMachine.reachable_wellFormed next nextReady.1).2.1 helperLoans,evalCode.eq_1]
  have evaluated : evalCode f2.code (byteMethodEntry world descriptor.reference) = some (.returned (.scalar .unit) final) := by
    rw [byte_method_prefix descriptor valid.2.1 frontier,evalCode.eq_3]
    have body : evalCode (.native byteBorrowBody byteCallCode) (bytePartsFrame descriptor) =
        some (.normal (byteReturnedFrame descriptor next helperFinal)) := by
      simp only [evalCode.eq_2,byte_borrow_from_issue descriptor next issued,called]
    rw [body]
    have before : (bytePartsFrame descriptor).world = lengthWorld descriptor := rfl
    have after : (byteReturnedFrame descriptor next helperFinal).world = helperFinal := rfl
    simp only [NativeRecordDropCalls.resumeScope,before,after,restored.1,List.isEmpty_nil,ite_true]
    change evalCode byteAfterCode (byteReturnedFrame descriptor next final) = some (.returned (.scalar .unit) final)
    exact byte_after_finish descriptor next final
  refine ⟨final,evaluated,NativeReferenceCleanup.closeScope_reachable _ _ helperReachable,restored.2,?_⟩
  exact (NativeReferenceCleanup.closeScope_heap_projects (lengthWorld descriptor) helperFinal).heap_eq.trans
    (helperHeap.trans (NativeSliceLLBC.issue_heap_projects (lengthWorld descriptor) next true _ _ issued).heap_eq)

theorem byte_method_invocation_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world) (initialized : InitializedElements descriptor)
    (available : Available world descriptor.buffer descriptor.capacity.val)
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    ∃ final, NativeRecordDropCalls.Invokes f2 world [.vectorExclusiveReference (world.references.idxOf descriptor.reference)]
        (.returned (.scalar .unit) final) ∧ NativeReferenceMachine.Reachable final ∧
      final.leases = world.leases ∧ final.pointers.heap = world.pointers.heap := by
  obtain ⟨final,computed,finalReachable,loans,heap⟩ := byte_method_complete descriptor reachable initialized available frontier
  have decoded : NativeVecReference.decodeExclusive world (world.references.idxOf descriptor.reference) =
      some (.reference true descriptor.reference 3) := by
    simp only [NativeVecReference.decodeExclusive,List.getElem?_idxOf (List.mem_of_getElem? descriptor.resident),
      descriptor.registered,Option.bind_eq_bind',Option.bind_some,descriptor.exclusive,descriptor.extent,and_self,ite_true]
  have invoked : invokeCode f2 world [.vectorExclusiveReference (world.references.idxOf descriptor.reference)] =
      some (.returned (.scalar .unit) final) := by
    simp only [invokeCode,decodeArgs,decode,decoded,Option.map_some,Option.bind_eq_bind',Option.bind_some,pure,
      byte_method_initial,computed,settle_unit_same_loans world final
        (NativeReferenceMachine.reachable_wellFormed world reachable).2.1 loans]
  exact ⟨final,invokeCode_sound f2 world _ _ invoked,finalReachable,loans,heap⟩


theorem byte_method_invokes_unit {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world) (initialized : InitializedElements descriptor)
    (available : Available world descriptor.buffer descriptor.capacity.val)
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease)
    (flow : Flow) (invoked : NativeRecordDropCalls.Invokes f2 world
      [.vectorExclusiveReference (world.references.idxOf descriptor.reference)] flow) :
    ∃ final, flow = .returned (.scalar .unit) final ∧ final.leases = world.leases ∧ final.pointers.heap = world.pointers.heap := by
  obtain ⟨final,accepted,_,loans,heap⟩ := byte_method_invocation_complete descriptor reachable initialized available frontier
  exact ⟨final,NativeRecordDropCalls.invokes_deterministic f2 world _ _ _ invoked accepted,loans,heap⟩

/-- The successful byte method leaves the original resident header available
for the following RawVec destructor path. -/
theorem byte_method_return_resident {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world) (initialized : InitializedElements descriptor)
    (available : Available world descriptor.buffer descriptor.capacity.val)
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    ∃ final, evalCode f2.code (byteMethodEntry world descriptor.reference) = some (.returned (.scalar .unit) final) ∧
      NativeResidentVecBorrow.Resident final (.reference true descriptor.reference 3) descriptor.lease.pointer
        descriptor.capacity descriptor.length descriptor.buffer := by
  obtain ⟨final,computed,_,_,heap⟩ := byte_method_complete descriptor reachable initialized available frontier
  have preserved : NativeIncomingReference.Preserves world final :=
    evalCode_incoming f2.code (byteMethodEntry world descriptor.reference) (.returned (.scalar .unit) final) computed
  obtain ⟨member,tag⟩ := NativeByteBorrow.lookup_selected _ _ _ descriptor.registered
  have age : descriptor.lease.tag < world.nextTag :=
    ((NativeReferenceMachine.reachable_wellFormed world reachable).2.1.1 descriptor.lease member).1
  have older : descriptor.reference.tag < world.nextTag := by rw [← tag]; exact age
  exact ⟨final,computed,NativeIncomingReference.resident preserved (NativeResidentVecBorrow.descriptor_resident descriptor) older heap⟩

end HasteBootsVecDrop
