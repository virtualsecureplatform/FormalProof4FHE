namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeResidentVecBorrow
open NativeRecordCallValues

/-- Source successors of the adjacent reservation/activation call. -/
def rawvecMethodCallTail : Body → Option (Body × Body)
  | .live _ next | .dead _ next | .assign _ _ next => rawvecMethodCallTail next
  | .twoPhaseRawVecCall _ _ _ _ _ _ _ _ _ _ unwind next => some (unwind,next)
  | _ => none

def rawvecMethodTail : Body × Body := (rawvecMethodCallTail HasteBootsRawVecDrop.f5.body).get (by decide)

theorem rawvec_method_body : HasteBootsRawVecDrop.f5.body =
    .live 0 (.assign 0 (.aggregate none none []) (.live 2
      (.twoPhaseRawVecCall 1 [] 2 HasteBootsRawVecDrop.f7.name HasteBootsRawVecDrop.f7.classification
        HasteBootsRawVecDrop.f7.types HasteBootsRawVecDrop.f7.argCount 0 [.layoutLiteral 1 1 9 11 12]
        HasteBootsRawVecDrop.f7.body rawvecMethodTail.1 rawvecMethodTail.2))) := by rfl

def rawvecMethodEntry (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference) : Frame :=
  ⟨HasteBootsRawVecDrop.f5.types,[.dead,.live (some (.scalar (.reference true reference 2))),.dead],world⟩
def rawvecMethodCaller (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference) : Frame :=
  ⟨HasteBootsRawVecDrop.f5.types,[.live (some (.scalar .unit)),.live (some (.scalar (.reference true reference 2))),.live (some .uninit)],world⟩

theorem rawvec_method_initial (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference) :
    initial HasteBootsRawVecDrop.f5.types HasteBootsRawVecDrop.f5.argCount [.scalar (.reference true reference 2)] world =
      some (rawvecMethodEntry world reference) := by
  simp [initial,HasteBootsRawVecDrop.f5,rawvecMethodEntry,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem rawvec_method_reserve_invalid (world failed : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (reserved : NativeRawVecMutBorrow.reserve world (.reference true reference 2) = .invalid failed) :
    invokeValues HasteBootsRawVecDrop.f5 world [.scalar (.reference true reference 2)] = .invalid failed := by
  rw [invokeValues_initialized HasteBootsRawVecDrop.f5 world _ (rawvecMethodEntry world reference)
    (rawvec_method_initial world reference),rawvec_method_body]
  simp [rawvecMethodEntry,HasteBootsRawVecDrop.f5,eval.eq_6,eval.eq_8,
    NativeRecordCallValues.eval_twoPhase_call HasteBootsRawVecDrop.f7,evalRvalue,evalArgs,storageLive,write,
    pendingMutableSlot,reserveRawVec,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.compatible,NativeRecordValues.complete,NativeSliceLLBC.fits,reserved,settle]

theorem rawvec_method_activate_invalid (world prepared failed : NativeReferenceMachine.State)
    (reference : NativeReferenceMachine.Reference) (reservation : NativeRawVecMutBorrow.Reservation)
    (reserved : NativeRawVecMutBorrow.reserve world (.reference true reference 2) = .value reservation prepared)
    (activated : NativeRawVecMutBorrow.activate prepared reservation = .invalid failed) :
    invokeValues HasteBootsRawVecDrop.f5 world [.scalar (.reference true reference 2)] = .invalid failed := by
  rw [invokeValues_initialized HasteBootsRawVecDrop.f5 world _ (rawvecMethodEntry world reference)
    (rawvec_method_initial world reference),rawvec_method_body]
  simp [rawvecMethodEntry,HasteBootsRawVecDrop.f5,eval.eq_6,eval.eq_8,
    NativeRecordCallValues.eval_twoPhase_call HasteBootsRawVecDrop.f7,evalRvalue,evalArgs,evalOperand,storageLive,write,
    pendingMutableSlot,reserveRawVec,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.compatible,NativeRecordValues.complete,NativeSliceLLBC.fits,reserved,activated,settle]

theorem rawvec_method_prefix (world prepared entered : NativeReferenceMachine.State)
    (reference child : NativeReferenceMachine.Reference) (reservation : NativeRawVecMutBorrow.Reservation)
    (reserved : NativeRawVecMutBorrow.reserve world (.reference true reference 2) = .value reservation prepared)
    (activated : NativeRawVecMutBorrow.activate prepared reservation = .value (.reference true child 2) entered) :
    invokeValues HasteBootsRawVecDrop.f5 world [.scalar (.reference true reference 2)] =
      settle world (resume (rawvecMethodCaller entered reference) 0 rawvecMethodTail.1 rawvecMethodTail.2
        (invokeValues HasteBootsRawVecDrop.f7 entered [.scalar (.reference true child 2),currentMemoryLayoutValue])) := by
  rw [invokeValues_initialized HasteBootsRawVecDrop.f5 world _ (rawvecMethodEntry world reference)
    (rawvec_method_initial world reference),rawvec_method_body]
  simp [rawvecMethodEntry,rawvecMethodCaller,HasteBootsRawVecDrop.f5,eval.eq_6,eval.eq_8,
    NativeRecordCallValues.eval_twoPhase_call HasteBootsRawVecDrop.f7,evalRvalue,evalArgs,evalOperand,storageLive,write,
    pendingMutableSlot,reserveRawVec,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
    NativeRecordValues.fits,NativeRecordValues.compatible,NativeRecordValues.complete,NativeSliceLLBC.fits,reserved,activated,currentMemoryLayoutValue]

/-- The wrapper either stops before the callee, or retains exactly its heap
outcome after passing a resident child at the original buffer/header. -/
theorem rawvec_method_heap_cases (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer) :
    (invokeValues HasteBootsRawVecDrop.f5 world [.scalar (.reference true reference 2)]).world.pointers.heap = world.pointers.heap ∨
      ∃ entered child, Resident entered (.reference true child 2) base capacity length buffer ∧
        entered.pointers.heap = world.pointers.heap ∧
        (invokeValues HasteBootsRawVecDrop.f5 world [.scalar (.reference true reference 2)]).world.pointers.heap =
          (invokeValues HasteBootsRawVecDrop.f7 entered [.scalar (.reference true child 2),currentMemoryLayoutValue]).world.pointers.heap := by
  have reserveFrame := (NativeRawVecMutBorrow.reserve_heap_projects world (.reference true reference 2)).heap_eq
  cases reserved : NativeRawVecMutBorrow.reserve world (.reference true reference 2) with
  | invalid failed =>
    left
    rw [rawvec_method_reserve_invalid world failed reference reserved]
    simpa only [reserved,NativeRawVecFields.Result.world,Flow.world] using reserveFrame
  | value reservation prepared =>
    obtain ⟨pointerEq,preparedResident⟩ := rawvec_reserve resident reservation reserved
    have preparedHeap : prepared.pointers.heap = world.pointers.heap := by simpa only [reserved,NativeRawVecFields.Result.world] using reserveFrame
    have activateFrame := (NativeRawVecMutBorrow.activate_heap_projects prepared reservation).heap_eq
    cases activated : NativeRawVecMutBorrow.activate prepared reservation with
    | invalid failed =>
      left
      rw [rawvec_method_activate_invalid world prepared failed reference reservation reserved activated]
      have failedHeap : failed.pointers.heap = prepared.pointers.heap := by simpa only [activated,NativeRawVecFields.Result.world] using activateFrame
      exact failedHeap.trans preparedHeap
    | value value entered =>
      have enteredResident := rawvec_activate preparedResident reservation pointerEq activated
      have valueEq := (NativeRawVecMutBorrow.activate_success prepared entered reservation value activated).2
      subst value
      right
      refine ⟨entered,⟨prepared.nextTag⟩,enteredResident,?_,?_⟩
      · have enteredHeap : entered.pointers.heap = prepared.pointers.heap := by simpa only [activated,NativeRawVecFields.Result.world] using activateFrame
        exact enteredHeap.trans preparedHeap
      · rw [rawvec_method_prefix world prepared entered reference ⟨prepared.nextTag⟩ reservation reserved activated]
        exact (settle_heap_projects world _).heap_eq.trans
          (resume_heap (rawvecMethodCaller entered reference) 0 rawvecMethodTail.1 rawvecMethodTail.2 _ (by decide) (by decide)).heap_eq

theorem rawvec_method_values (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer) :
    DeallocationPost world buffer capacity (invokeValues HasteBootsRawVecDrop.f5 world [.scalar (.reference true reference 2)]) := by
  rcases rawvec_method_heap_cases world reference base buffer capacity length resident with same | ⟨entered,child,carried,before,after⟩
  · exact Or.inl same
  · have checked := deallocation_values entered child base buffer capacity length carried
    simpa only [DeallocationPost,after,before] using checked

theorem rawvec_method_zero (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base 0 length buffer) :
    (invokeValues HasteBootsRawVecDrop.f5 world [.scalar (.reference true reference 2)]).world.pointers.heap = world.pointers.heap := by
  rcases rawvec_method_heap_cases world reference base buffer 0 length resident with same | ⟨entered,child,carried,before,after⟩
  · exact same
  · exact after.trans ((deallocation_values_zero entered child base buffer length carried).trans before)
def rawvecGlueTail : Body × Body := (memoryCallTail HasteBootsRawVecDrop.f4.body).get (by decide)

theorem rawvec_glue_body : HasteBootsRawVecDrop.f4.body =
    .live 0 (.live 2 (.live 3 (.assign 0 (.aggregate none none []) (.assign 2 (.borrowRawVecMut 1 [])
      (.call HasteBootsRawVecDrop.f5.name HasteBootsRawVecDrop.f5.classification HasteBootsRawVecDrop.f5.types
        HasteBootsRawVecDrop.f5.argCount 3 [.move 2 []] HasteBootsRawVecDrop.f5.body rawvecGlueTail.1 rawvecGlueTail.2))))) := by rfl

def rawvecGlueEntry (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference) : Frame :=
  ⟨HasteBootsRawVecDrop.f4.types,[.dead,.live (some (.scalar (.reference true reference 2))),.dead,.dead],world⟩
def rawvecGlueBorrow (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference) : Frame :=
  ⟨HasteBootsRawVecDrop.f4.types,[.live (some (.scalar .unit)),.live (some (.scalar (.reference true reference 2))),.live none,.live none],world⟩
def rawvecGlueCaller (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference) : Frame :=
  ⟨HasteBootsRawVecDrop.f4.types,[.live (some (.scalar .unit)),.live (some (.scalar (.reference true reference 2))),.live (some .uninit),.live none],world⟩

theorem rawvec_glue_initial (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference) :
    initial HasteBootsRawVecDrop.f4.types HasteBootsRawVecDrop.f4.argCount [.scalar (.reference true reference 2)] world =
      some (rawvecGlueEntry world reference) := by
  simp [initial,HasteBootsRawVecDrop.f4,rawvecGlueEntry,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem rawvec_glue_borrow (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference) :
    evalRawVecMutBorrow (rawvecGlueBorrow world reference) 1 [] =
      match NativeRawVecMutBorrow.immediate world (.reference true reference 2) with
      | .invalid failed => .invalid failed
      | .value output entered => .value (.scalar output) {rawvecGlueBorrow world reference with world := entered} := by
  apply eval_mut_borrow
  simp [rawvecGlueBorrow,HasteBootsRawVecDrop.f4,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem rawvec_glue_borrow_invalid (world failed : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (created : NativeRawVecMutBorrow.immediate world (.reference true reference 2) = .invalid failed) :
    invokeValues HasteBootsRawVecDrop.f4 world [.scalar (.reference true reference 2)] = .invalid failed := by
  rw [invokeValues_initialized HasteBootsRawVecDrop.f4 world _ (rawvecGlueEntry world reference)
    (rawvec_glue_initial world reference),rawvec_glue_body]
  have step := rawvec_glue_borrow world reference
  dsimp only [rawvecGlueBorrow,HasteBootsRawVecDrop.f4] at step
  simp [rawvecGlueEntry,HasteBootsRawVecDrop.f4,eval.eq_6,eval.eq_8,evalRvalue,evalArgs,storageLive,write,
    step,created,
    NativeRecordValues.fits,NativeRecordValues.compatible,NativeRecordValues.complete,NativeSliceLLBC.fits,settle]

theorem rawvec_glue_prefix (world entered : NativeReferenceMachine.State) (reference child : NativeReferenceMachine.Reference)
    (created : NativeRawVecMutBorrow.immediate world (.reference true reference 2) = .value (.reference true child 2) entered) :
    invokeValues HasteBootsRawVecDrop.f4 world [.scalar (.reference true reference 2)] =
      settle world (resume (rawvecGlueCaller entered reference) 3 rawvecGlueTail.1 rawvecGlueTail.2
        (invokeValues HasteBootsRawVecDrop.f5 entered [.scalar (.reference true child 2)])) := by
  rw [invokeValues_initialized HasteBootsRawVecDrop.f4 world _ (rawvecGlueEntry world reference)
    (rawvec_glue_initial world reference),rawvec_glue_body]
  have step := rawvec_glue_borrow world reference
  dsimp only [rawvecGlueBorrow,HasteBootsRawVecDrop.f4] at step
  simp [rawvecGlueEntry,rawvecGlueCaller,HasteBootsRawVecDrop.f4,eval.eq_6,eval.eq_8,evalRvalue,evalArgs,evalOperand,storageLive,write,
    step,created,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.replace,NativeRecordValues.fits,NativeRecordValues.compatible,
    NativeRecordValues.complete,NativeSliceLLBC.fits,NativeRecordCallValues.eval_call HasteBootsRawVecDrop.f5]

theorem immediate_reference (world next : NativeReferenceMachine.State) (input output : NativeSliceLLBC.Value)
    (created : NativeRawVecMutBorrow.immediate world input = .value output next) :
    ∃ child, output = .reference true child 2 := by
  cases reserved : NativeRawVecMutBorrow.reserve world input with
  | invalid failed => simp only [NativeRawVecMutBorrow.immediate,reserved] at created; cases created
  | value reservation prepared =>
    have activated : NativeRawVecMutBorrow.activate prepared reservation = .value output next := by
      simpa only [NativeRawVecMutBorrow.immediate,reserved] using created
    exact ⟨⟨prepared.nextTag⟩,(NativeRawVecMutBorrow.activate_success prepared next reservation output activated).2⟩

theorem rawvec_glue_heap_cases (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer) :
    (invokeValues HasteBootsRawVecDrop.f4 world [.scalar (.reference true reference 2)]).world.pointers.heap = world.pointers.heap ∨
      ∃ entered child, Resident entered (.reference true child 2) base capacity length buffer ∧
        entered.pointers.heap = world.pointers.heap ∧
        (invokeValues HasteBootsRawVecDrop.f4 world [.scalar (.reference true reference 2)]).world.pointers.heap =
          (invokeValues HasteBootsRawVecDrop.f5 entered [.scalar (.reference true child 2)]).world.pointers.heap := by
  have frame := (NativeRawVecMutBorrow.immediate_heap_projects world (.reference true reference 2)).heap_eq
  cases created : NativeRawVecMutBorrow.immediate world (.reference true reference 2) with
  | invalid failed =>
    left
    rw [rawvec_glue_borrow_invalid world failed reference created]
    simpa only [created,NativeRawVecFields.Result.world,Flow.world] using frame
  | value value entered =>
    have carried := rawvec_immediate resident created
    obtain ⟨child,valueEq⟩ := immediate_reference world entered _ _ created
    subst value
    right
    refine ⟨entered,child,carried,?_,?_⟩
    · simpa only [created,NativeRawVecFields.Result.world] using frame
    · rw [rawvec_glue_prefix world entered reference child created]
      exact (settle_heap_projects world _).heap_eq.trans
        (resume_heap (rawvecGlueCaller entered reference) 3 rawvecGlueTail.1 rawvecGlueTail.2 _ (by decide) (by decide)).heap_eq

theorem rawvec_glue_values (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer) :
    DeallocationPost world buffer capacity (invokeValues HasteBootsRawVecDrop.f4 world [.scalar (.reference true reference 2)]) := by
  rcases rawvec_glue_heap_cases world reference base buffer capacity length resident with same | ⟨entered,child,carried,before,after⟩
  · exact Or.inl same
  · have checked := rawvec_method_values entered child base buffer capacity length carried
    simpa only [DeallocationPost,after,before] using checked

theorem rawvec_glue_zero (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base 0 length buffer) :
    (invokeValues HasteBootsRawVecDrop.f4 world [.scalar (.reference true reference 2)]).world.pointers.heap = world.pointers.heap := by
  rcases rawvec_glue_heap_cases world reference base buffer 0 length resident with same | ⟨entered,child,carried,before,after⟩
  · exact same
  · exact after.trans ((rawvec_method_zero entered child base buffer length carried).trans before)
theorem rawvec_values_eq (function : Function) (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer) :
    invokeValues function world [.scalar (.reference true reference 2)] =
      invoke function world [.rawVecExclusiveReference (world.references.idxOf reference)] := by
  obtain ⟨mutable,ref,count,lease,same,member,registered,_,mode,shape,_,_⟩ := resident
  cases same
  have layout : lease.layout = ⟨16,8⟩ := by
    rcases shape with ⟨impossible,_⟩ | ⟨_,layout⟩
    · exact False.elim ((by decide : (2 : NativeWord64Memory.Word) ≠ 3) impossible)
    · exact layout
  have decoded : NativeRawVecBorrow.decodeExclusive world (world.references.idxOf reference) = some (.reference true reference 2) := by
    simp only [NativeRawVecBorrow.decodeExclusive,List.getElem?_idxOf member,registered,Option.bind_eq_bind',Option.bind_some,
      mode,layout,NativeSliceLLBC.mode,and_self,ite_true]
  simp only [NativeRecordCallValues.invoke_eq,decodeArgs,decode,decoded,Option.map_some,Option.bind_eq_bind',Option.bind_some,pure]

theorem rawvec_method_invocation (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer) :
    DeallocationPost world buffer capacity (invoke HasteBootsRawVecDrop.f5 world
      [.rawVecExclusiveReference (world.references.idxOf reference)]) := by
  rw [← rawvec_values_eq HasteBootsRawVecDrop.f5 world reference base buffer capacity length resident]
  exact rawvec_method_values world reference base buffer capacity length resident

theorem rawvec_glue_invocation (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer) :
    DeallocationPost world buffer capacity (invoke HasteBootsRawVecDrop.f4 world
      [.rawVecExclusiveReference (world.references.idxOf reference)]) := by
  rw [← rawvec_values_eq HasteBootsRawVecDrop.f4 world reference base buffer capacity length resident]
  exact rawvec_glue_values world reference base buffer capacity length resident

def nativeDefinition (function : Function) : NativeRecordDropCalls.Definition :=
  ⟨function.name,function.classification,function.types,function.argCount,.native function.body .done⟩

theorem native_definition_invoke (function : Function) (world : NativeReferenceMachine.State) (args : List Input) :
    invokeCode (nativeDefinition function) world args = some (invoke function world args) := by
  cases decoded : decodeArgs world args with
  | none => simp only [invokeCode,invoke,decoded]
  | some values =>
    cases initialized : initial function.types function.argCount values world with
    | none => simp only [invokeCode,nativeDefinition,invoke,decoded,initialized]
    | some entered =>
      simp only [invokeCode,nativeDefinition,invoke,decoded,initialized]
      cases actual : eval function.body entered <;> simp only [evalCode,actual,Option.map_some]

theorem native_definition_invokes_eq (function : Function) (world : NativeReferenceMachine.State) (args : List Input) (flow : Flow)
    (invoked : NativeRecordDropCalls.Invokes (nativeDefinition function) world args flow) : flow = invoke function world args := by
  have expected := invokeCode_sound (nativeDefinition function) world args _ (native_definition_invoke function world args)
  exact NativeRecordDropCalls.invokes_deterministic (nativeDefinition function) world args _ _ invoked expected

theorem rawvec_glue_definition : f4 = nativeDefinition HasteBootsRawVecDrop.f4 := by rfl

theorem rawvec_glue_invokes (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer) (flow : Flow)
    (invoked : NativeRecordDropCalls.Invokes f4 world [.rawVecExclusiveReference (world.references.idxOf reference)] flow) :
    DeallocationPost world buffer capacity flow := by
  rw [rawvec_glue_definition] at invoked
  rw [native_definition_invokes_eq HasteBootsRawVecDrop.f4 world _ _ invoked]
  exact rawvec_glue_invocation world reference base buffer capacity length resident

theorem rawvec_glue_invokes_zero (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base 0 length buffer) (flow : Flow)
    (invoked : NativeRecordDropCalls.Invokes f4 world [.rawVecExclusiveReference (world.references.idxOf reference)] flow) :
    flow.world.pointers.heap = world.pointers.heap := by
  rw [rawvec_glue_definition] at invoked
  rw [native_definition_invokes_eq HasteBootsRawVecDrop.f4 world _ _ invoked]
  rw [← rawvec_values_eq HasteBootsRawVecDrop.f4 world reference base buffer 0 length resident]
  exact rawvec_glue_zero world reference base buffer length resident

theorem rawvec_glue_changed_block (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer) (flow : Flow)
    (invoked : NativeRecordDropCalls.Invokes f4 world [.rawVecExclusiveReference (world.references.idxOf reference)] flow)
    (changed : flow.world.pointers.heap ≠ world.pointers.heap) :
    0 < capacity.val ∧ ∃ block ∈ world.pointers.heap.memory.blocks,
      block.pointer = buffer ∧ block.layout = ⟨capacity.val,1⟩ ∧
      NativePointerByteMemory.deallocate world.pointers.heap block.pointer block.layout = some flow.world.pointers.heap := by
  have nonzero : capacity ≠ 0 := by
    intro zero
    subst capacity
    exact changed (rawvec_glue_invokes_zero world reference base buffer length resident flow invoked)
  have positive : 0 < capacity.val := by
    have valNonzero : capacity.val ≠ 0 := fun zero => nonzero (Fin.ext zero)
    omega
  have freed : NativePointerByteMemory.deallocate world.pointers.heap buffer ⟨capacity.val,1⟩ = some flow.world.pointers.heap := by
    rcases rawvec_glue_invokes world reference base buffer capacity length resident flow invoked with same | freed
    · exact False.elim (changed same)
    · exact freed
  obtain ⟨_,_,memory,_⟩ := NativePointerByteMemory.deallocate_success _ _ _ _ freed
  simp only [NativeByteMemory.deallocate,Option.map_eq_some_iff] at memory
  obtain ⟨blocks,released,_⟩ := memory
  obtain ⟨block,member,pointerEq,layoutEq⟩ := NativeByteMemory.release_selected _ _ _ blocks released
  exact ⟨positive,block,member,pointerEq.symm,layoutEq.symm,by rw [← pointerEq,← layoutEq]; exact freed⟩
/-- The retained method reaches its deallocation callee from initialized
resident RawVec fields and the logical alias condition. -/
theorem rawvec_method_ready_prefix (world : NativeReferenceMachine.State)
    (reference : NativeReferenceMachine.Reference) (lease : NativeByteBorrow.Lease)
    (valid : NativeByteBorrow.WellFormed (NativeReferenceMachine.ledger world))
    (frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) lease)
    (tag : reference.tag = lease.tag) (shape : lease.layout = ⟨16,8⟩)
    (referenceResident : reference ∈ world.references) (pointerResident : lease.pointer ∈ world.pointers.registers)
    (bytes : List NativeByteMemory.Byte)
    (initialized : NativeByteRange.loadRange world.pointers.heap.memory lease.pointer ⟨16,8⟩ = some bytes) :
    ∃ entered, invokeValues HasteBootsRawVecDrop.f5 world [.scalar (.reference true reference 2)] =
        settle world (resume (rawvecMethodCaller entered reference) 0 rawvecMethodTail.1 rawvecMethodTail.2
          (invokeValues HasteBootsRawVecDrop.f7 entered
            [.scalar (.reference true ⟨world.nextTag⟩ 2),currentMemoryLayoutValue])) ∧
      NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger entered)
        ⟨world.nextTag,some lease.tag,lease.pointer,⟨16,8⟩,.exclusive⟩ := by
  have reserved := NativeRawVecBorrowCompleteness.reserve_complete world reference lease valid.2 frontier
    tag shape referenceResident pointerResident
  obtain ⟨entered,activated,available⟩ := NativeRawVecBorrowCompleteness.activate_complete world reference lease
    valid frontier tag shape referenceResident bytes initialized
  exact ⟨entered,rawvec_method_prefix world (NativeRawVecBorrowCompleteness.prepared world lease) entered
    reference ⟨world.nextTag⟩ ⟨reference,lease.pointer⟩ reserved activated,available⟩

end HasteBootsVecDrop

