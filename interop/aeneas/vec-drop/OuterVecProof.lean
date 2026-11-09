namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeRecordDropCalls (Code heapBudget)
open NativeReferenceMachine (State Reference)
open NativeResidentVecBorrow
open NativeRecordCallValues

/-- Every actual free has a positive capacity; zero capacity frames the heap. -/
def VecDeallocationPost (world : State) (buffer : NativePointerStorage.Pointer)
    (capacity : NativeWord64Memory.Word) (flow : Flow) : Prop :=
  flow.world.pointers.heap = world.pointers.heap ∨
    (0 < capacity.val ∧ NativePointerByteMemory.deallocate world.pointers.heap buffer ⟨capacity.val,1⟩ =
      some flow.world.pointers.heap)

/-- Retain both source successors of the byte destructor call. -/
def vecRootStages : Code → Option (Body × Code × Code)
  | .scope (.native prelude (.call _ _ _ _ _ _ _ unwind .done)) next => some (prelude,unwind,next)
  | _ => none

def vecRootParts : Body × Code × Code := (vecRootStages f1.code).get (by decide)

theorem vec_root_code : f1.code =
    .scope (.native vecRootParts.1
      (.call f2.name f2.classification f2.types f2.argCount 3 [.move 2 []] f2.code vecRootParts.2.1 .done))
      vecRootParts.2.2 := by rfl

def vecRawStage (unwinding : Bool) : Code := if unwinding then vecRootParts.2.1 else vecRootParts.2.2

def vecRawStageBodies : Code → Option (Body × Body × Body)
  | .scope (.native prelude (.call _ _ _ _ _ _ _ (.native failed .done) .done)) (.native next .done) =>
    some (prelude,failed,next)
  | _ => none

def vecRawBodies (unwinding : Bool) : Body × Body × Body :=
  (vecRawStageBodies (vecRawStage unwinding)).get (by cases unwinding <;> decide)

def vecRawLocal (unwinding : Bool) : Nat := if unwinding then 4 else 6

theorem vec_raw_stage_code (unwinding : Bool) : vecRawStage unwinding =
    .scope (.native (vecRawBodies unwinding).1
      (.call f4.name f4.classification f4.types f4.argCount (vecRawLocal unwinding + 1)
        [.move (vecRawLocal unwinding) []] f4.code
        (.native (vecRawBodies unwinding).2.1 .done) .done))
      (.native (vecRawBodies unwinding).2.2 .done) := by cases unwinding <;> rfl

theorem vec_raw_prefix_body (unwinding : Bool) : (vecRawBodies unwinding).1 =
    .live (vecRawLocal unwinding) (.assign (vecRawLocal unwinding) (.vec (.borrow .rawVec) 1 [])
      (.live (vecRawLocal unwinding + 1) .done)) := by cases unwinding <;> rfl

theorem vec_raw_failed_budget (unwinding : Bool) :
    deallocationBudget (vecRawBodies unwinding).2.1 = 0 := by cases unwinding <;> decide

theorem vec_raw_next_budget (unwinding : Bool) :
    deallocationBudget (vecRawBodies unwinding).2.2 = 0 := by cases unwinding <;> decide

def vecRootFrame (world : State) (reference : Reference) (returned : Slot) : Frame :=
  ⟨f1.types,[.live (some (.scalar .unit)),.live (some (.scalar (.reference true reference 3))),
    .live (some .uninit),returned,.dead,.dead,.dead,.dead],world⟩

theorem eval_vec_borrow (frame : Frame) (index : Nat) (path : NativeRecordValues.Path)
    (value : NativeSliceLLBC.Value) (target : NativeVecReference.Target)
    (selected : read frame index path = some (.scalar value)) :
    evalVec frame index path (.borrow target) =
      match NativeVecReference.reborrow frame.world value target with
      | .invalid world => .invalid world
      | .value output world => .value (.scalar output) {frame with world} := by
  simp only [evalVec,selected,NativeVecReference.eval]
  rfl

/-- Actual post-prelude caller slots, before moving the RawVec child. -/
def vecRawCaller (unwinding : Bool) (world : State) (reference child : Reference) (returned : Slot) : Frame :=
  if unwinding then
    ⟨f1.types,[.live (some (.scalar .unit)),.live (some (.scalar (.reference true reference 3))),
      .live (some .uninit),returned,.live (some (.scalar (.reference true child 2))),.live none,.dead,.dead],world⟩
  else
    ⟨f1.types,[.live (some (.scalar .unit)),.live (some (.scalar (.reference true reference 3))),
      .live (some .uninit),returned,.dead,.dead,.live (some (.scalar (.reference true child 2))),.live none],world⟩

theorem vec_raw_prefix_invalid (unwinding : Bool) (world failed : State) (reference : Reference) (returned : Slot)
    (borrowed : NativeVecReference.reborrow world (.reference true reference 3) .rawVec = .invalid failed) :
    eval (vecRawBodies unwinding).1 (vecRootFrame world reference returned) = .invalid failed := by
  rw [vec_raw_prefix_body]
  cases unwinding <;>
    simp [vecRootFrame,vecRawLocal,eval,evalRvalue,evalVec,NativeVecReference.eval,storageLive,
      NativeRecordLLBC.read,f1,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,
      NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,borrowed]

theorem vec_raw_prefix_value (unwinding : Bool) (world entered : State) (reference child : Reference) (returned : Slot)
    (borrowed : NativeVecReference.reborrow world (.reference true reference 3) .rawVec =
      .value (.reference true child 2) entered) :
    eval (vecRawBodies unwinding).1 (vecRootFrame world reference returned) =
      .normal (vecRawCaller unwinding entered reference child returned) := by
  rw [vec_raw_prefix_body]
  cases unwinding <;>
    simp [vecRootFrame,vecRawCaller,vecRawLocal,eval,evalRvalue,evalVec,NativeVecReference.eval,storageLive,write,
      NativeRecordLLBC.read,f1,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,
      NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,borrowed]

def vecRawConsumed (unwinding : Bool) (world : State) (reference child : Reference) (returned : Slot) : Frame :=
  let caller := vecRawCaller unwinding world reference child returned
  {caller with slots := caller.slots.set (vecRawLocal unwinding) (.live (some .uninit))}

theorem vec_raw_call_prepared (unwinding : Bool) (world : State) (reference child : Reference) (returned : Slot) :
    NativeRecordDropCalls.prepareCall (vecRawCaller unwinding world reference child returned)
      f4.types f4.argCount [.move (vecRawLocal unwinding) []] =
      some (vecRawConsumed unwinding world reference child returned,rawvecGlueEntry world child) := by
  cases unwinding <;>
    simp [NativeRecordDropCalls.prepareCall,vecRawCaller,vecRawConsumed,vecRawLocal,f1,f4,
      evalArgs,evalOperand,NativeRecordValues.replace,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,
      rawvecGlueEntry,initial,HasteBootsRawVecDrop.f4]

theorem native_done_eval (body : Body) (frame : Frame) :
    evalCode (.native body .done) frame = some (eval body frame) := by
  cases actual : eval body frame <;> simp only [evalCode,actual]

theorem rawvec_glue_code_eval (world : State) (reference : Reference) :
    evalCode f4.code (rawvecGlueEntry world reference) =
      some (eval HasteBootsRawVecDrop.f4.body (rawvecGlueEntry world reference)) := by
  rw [rawvec_glue_definition]
  exact native_done_eval _ _

theorem rawvec_glue_eval_post (world : State) (reference : Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer) :
    VecDeallocationPost world buffer capacity (eval HasteBootsRawVecDrop.f4.body (rawvecGlueEntry world reference)) := by
  by_cases zero : capacity = 0
  · subst capacity
    have checked := rawvec_glue_zero world reference base buffer length resident
    rw [invokeValues_initialized HasteBootsRawVecDrop.f4 world _ (rawvecGlueEntry world reference)
      (rawvec_glue_initial world reference)] at checked
    left
    simpa only [(settle_heap_projects (rawvecGlueEntry world reference).world _).heap_eq] using checked
  · have checked := rawvec_glue_values world reference base buffer capacity length resident
    rw [invokeValues_initialized HasteBootsRawVecDrop.f4 world _ (rawvecGlueEntry world reference)
      (rawvec_glue_initial world reference)] at checked
    have result : DeallocationPost world buffer capacity (eval HasteBootsRawVecDrop.f4.body (rawvecGlueEntry world reference)) := by
      simpa only [DeallocationPost,(settle_heap_projects (rawvecGlueEntry world reference).world _).heap_eq] using checked
    rcases result with same | freed
    · exact Or.inl same
    · right
      refine ⟨?_,freed⟩
      have nonzero : capacity.val ≠ 0 := fun h => zero (Fin.ext h)
      omega

theorem deallocation_post_heap_eq (world : State) (buffer : NativePointerStorage.Pointer)
    (capacity : NativeWord64Memory.Word) (before after : Flow)
    (same : after.world.pointers.heap = before.world.pointers.heap)
    (checked : VecDeallocationPost world buffer capacity before) : VecDeallocationPost world buffer capacity after := by
  simpa only [VecDeallocationPost,same] using checked


def vecRawCall (unwinding : Bool) : Code :=
  .call f4.name f4.classification f4.types f4.argCount (vecRawLocal unwinding + 1)
    [.move (vecRawLocal unwinding) []] f4.code (.native (vecRawBodies unwinding).2.1 .done) .done

theorem vec_raw_call_post (unwinding : Bool) (world : State) (reference child : Reference) (returned : Slot)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true child 2) base capacity length buffer) (flow : Flow)
    (computed : evalCode (vecRawCall unwinding) (vecRawCaller unwinding world reference child returned) = some flow) :
    VecDeallocationPost world buffer capacity flow := by
  have prepared := vec_raw_call_prepared unwinding world reference child returned
  have checked := rawvec_glue_eval_post world child base buffer capacity length resident
  have resumedHeap := NativeRecordDropCalls.resumeCall_heap_projects world
    (vecRawConsumed unwinding world reference child returned) (vecRawLocal unwinding + 1)
    (eval HasteBootsRawVecDrop.f4.body (rawvecGlueEntry world child))
  rw [vecRawCall,evalCode.eq_4,prepared] at computed
  simp only [rawvec_glue_code_eval,show (rawvecGlueEntry world child).world = world from rfl] at computed
  cases resumed : NativeRecordDropCalls.resumeCall world (vecRawConsumed unwinding world reference child returned)
      (vecRawLocal unwinding + 1) (eval HasteBootsRawVecDrop.f4.body (rawvecGlueEntry world child)) with
  | next changed =>
    simp only [resumed,evalCode,Option.some.injEq] at computed
    subst flow
    rw [resumed] at resumedHeap
    exact deallocation_post_heap_eq world buffer capacity _ _ resumedHeap.heap_eq checked
  | unwind changed =>
    simp only [resumed,native_done_eval,Option.some.injEq] at computed
    subst flow
    rw [resumed] at resumedHeap
    have suffixHeap := body_zero_heap (vecRawBodies unwinding).2.1 changed (vec_raw_failed_budget unwinding)
    exact deallocation_post_heap_eq world buffer capacity _ _ (suffixHeap.heap_eq.trans resumedHeap.heap_eq) checked
  | invalid final =>
    simp only [resumed,Option.some.injEq] at computed
    subst flow
    rw [resumed] at resumedHeap
    exact deallocation_post_heap_eq world buffer capacity _ _ resumedHeap.heap_eq checked
  | unsupported source final =>
    simp only [resumed,Option.some.injEq] at computed
    subst flow
    rw [resumed] at resumedHeap
    exact deallocation_post_heap_eq world buffer capacity _ _ resumedHeap.heap_eq checked


theorem evalCode_zero_heap (code : Code) (frame : Frame) (flow : Flow)
    (budget : (heapBudget code).total = 0) (computed : evalCode code frame = some flow) :
    flow.world.pointers.heap = frame.world.pointers.heap := by
  have loss := (evalCode_loss code frame flow computed).mono (heapBudget code).total
    ((heapBudget code).limit_le_total flow)
  rw [budget] at loss
  apply loss.unchanged
  have bounded := loss.bounded
  have noGrowth := loss.no_growth
  omega

theorem scope_deallocation_post (world : State) (buffer : NativePointerStorage.Pointer)
    (capacity : NativeWord64Memory.Word) (body next : Code) (frame : Frame) (flow : Flow)
    (bodyPost : ∀ returned, evalCode body frame = some returned → VecDeallocationPost world buffer capacity returned)
    (nextBudget : (heapBudget next).total = 0)
    (computed : evalCode (.scope body next) frame = some flow) : VecDeallocationPost world buffer capacity flow := by
  cases actual : evalCode body frame with
  | none => simp only [evalCode,actual] at computed; cases computed
  | some returned =>
    have checked := bodyPost returned actual
    have cleanup := NativeRecordDropCalls.resumeScope_heap_projects frame.world returned
    cases settled : NativeRecordDropCalls.resumeScope frame.world returned with
    | normal changed =>
      have later : evalCode next changed = some flow := by simpa only [evalCode.eq_3,actual,settled] using computed
      rw [settled] at cleanup
      exact deallocation_post_heap_eq world buffer capacity _ _
        ((evalCode_zero_heap next changed flow nextBudget later).trans cleanup.heap_eq) checked
    | returned value final | unwind final | invalid final | unsupported source final =>
      simp only [evalCode.eq_3,actual,settled,Option.some.injEq] at computed
      subst flow
      rw [settled] at cleanup
      exact deallocation_post_heap_eq world buffer capacity _ _ cleanup.heap_eq checked

theorem vec_raw_stage_post (unwinding : Bool) (world : State) (reference : Reference) (returned : Slot)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 3) base capacity length buffer) (flow : Flow)
    (computed : evalCode (vecRawStage unwinding) (vecRootFrame world reference returned) = some flow) :
    VecDeallocationPost world buffer capacity flow := by
  rw [vec_raw_stage_code] at computed
  apply scope_deallocation_post world buffer capacity _ _ _ flow ?_ ?_ computed
  · intro result actual
    have borrowedHeap := NativeVecReference.reborrow_heap_projects world (.reference true reference 3) .rawVec
    cases borrowed : NativeVecReference.reborrow world (.reference true reference 3) .rawVec with
    | invalid failed =>
      have prefixRun := vec_raw_prefix_invalid unwinding world failed reference returned borrowed
      simp only [evalCode.eq_2,prefixRun,Option.some.injEq] at actual
      subst result
      left
      simpa only [borrowed,NativeRawVecFields.Result.world,Flow.world] using borrowedHeap.heap_eq
    | value output entered =>
      have childResident := vec_reborrow resident .rawVec borrowed
      obtain ⟨_,_,_,_,prepared,_,_,_,_,outputEq⟩ := NativeVecReference.reborrow_success world entered _ output .rawVec borrowed
      subst output
      have prefixRun := vec_raw_prefix_value unwinding world entered reference ⟨prepared.nextTag⟩ returned borrowed
      have called : evalCode (vecRawCall unwinding) (vecRawCaller unwinding entered reference ⟨prepared.nextTag⟩ returned) = some result := by
        simpa only [evalCode.eq_2,prefixRun,vecRawCall] using actual
      have checked := vec_raw_call_post unwinding entered reference ⟨prepared.nextTag⟩ returned base buffer capacity length childResident result called
      have before : entered.pointers.heap = world.pointers.heap := by
        simpa only [borrowed,NativeRawVecFields.Result.world,Flow.world] using borrowedHeap.heap_eq
      simpa only [VecDeallocationPost,before] using checked
  · cases unwinding <;> decide


def vecByteCaller (world : State) (reference child : Reference) : Frame :=
  ⟨f1.types,[.live (some (.scalar .unit)),.live (some (.scalar (.reference true reference 3))),
    .live (some (.scalar (.reference true child 3))),.live none,.dead,.dead,.dead,.dead],world⟩

def vecByteEntry (world : State) (child : Reference) : Frame :=
  ⟨f2.types,[.dead,.live (some (.scalar (.reference true child 3))),.dead,.dead,.dead,.dead,.dead],world⟩

theorem vec_byte_call_prepared (world : State) (reference child : Reference) :
    NativeRecordDropCalls.prepareCall (vecByteCaller world reference child) f2.types f2.argCount [.move 2 []] =
      some (vecRootFrame world reference (.live none),vecByteEntry world child) := by
  simp [NativeRecordDropCalls.prepareCall,vecByteCaller,vecRootFrame,vecByteEntry,f1,f2,
    evalArgs,evalOperand,NativeRecordValues.replace,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,initial]

theorem vec_root_write_return (world : State) (reference : Reference) (value : NativeRecordValues.Value) (changed : Frame)
    (written : write (vecRootFrame world reference (.live none)) 3 value = some changed) :
    changed = vecRootFrame world reference (.live (some value)) := by
  simp only [write,vecRootFrame,f1,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.bind_some] at written
  split at written
  · cases written; rfl
  · cases written

theorem vec_byte_resume_next (world : State) (reference : Reference) (flow : Flow) (changed : Frame)
    (resumed : NativeRecordDropCalls.resumeCall world (vecRootFrame world reference (.live none)) 3 flow =
      .next changed) : ∃ returned, changed = vecRootFrame changed.world reference returned := by
  cases flow with
  | normal frame => cases resumed
  | unwind final => cases resumed
  | invalid final => cases resumed
  | unsupported source final => cases resumed
  | returned value final =>
    cases settled : settle world (.returned value final) with
    | normal frame => simp only [NativeRecordDropCalls.resumeCall,settled] at resumed; cases resumed
    | invalid final => simp only [NativeRecordDropCalls.resumeCall,settled] at resumed; cases resumed
    | unwind final => simp only [NativeRecordDropCalls.resumeCall,settled] at resumed; cases resumed
    | unsupported source final => simp only [NativeRecordDropCalls.resumeCall,settled] at resumed; cases resumed
    | returned value final =>
      cases written : write (vecRootFrame final reference (.live none)) 3 value with
      | none =>
        have actual : write {vecRootFrame world reference (.live none) with world := final} 3 value = none := written
        simp only [NativeRecordDropCalls.resumeCall,settled,actual] at resumed
        cases resumed
      | some caller =>
        have actual : write {vecRootFrame world reference (.live none) with world := final} 3 value = some caller := written
        simp only [NativeRecordDropCalls.resumeCall,settled,actual,NativeRecordDropCalls.Resume.next.injEq] at resumed
        subst caller
        have same := vec_root_write_return final reference value changed written
        refine ⟨.live (some value),?_⟩
        rw [same]
        rfl

def vecByteCall : Code :=
  .call f2.name f2.classification f2.types f2.argCount 3 [.move 2 []] f2.code vecRootParts.2.1 .done

/-- A normal byte-call result preserves the original header and caller shape;
an unwind follows the source RawVec path and retains its original-buffer effect. -/
def VecBytePost (world : State) (reference : Reference) (buffer : NativePointerStorage.Pointer)
    (capacity : NativeWord64Memory.Word) (flow : Flow) : Prop :=
  match flow with
  | .normal frame => ∃ returned, frame = vecRootFrame frame.world reference returned ∧
      frame.world.pointers.heap = world.pointers.heap
  | _ => VecDeallocationPost world buffer capacity flow

theorem vec_byte_call_post (world : State) (reference child : Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 3) base capacity length buffer)
    (older : reference.tag < world.nextTag) (flow : Flow)
    (computed : evalCode vecByteCall (vecByteCaller world reference child) = some flow) :
    VecBytePost world reference buffer capacity flow := by
  rw [vecByteCall,evalCode.eq_4,vec_byte_call_prepared] at computed
  cases actual : evalCode f2.code (vecByteEntry world child) with
  | none => simp only [actual] at computed; cases computed
  | some returned =>
    have heapSame := evalCode_zero_heap f2.code (vecByteEntry world child) returned byte_method_zero_budget actual
    have preserved := evalCode_incoming f2.code (vecByteEntry world child) returned actual
    have resumedHeap := NativeRecordDropCalls.resumeCall_heap_projects world
      (vecRootFrame world reference (.live none)) 3 returned
    simp only [actual,show (vecByteEntry world child).world = world from rfl] at computed
    cases resumed : NativeRecordDropCalls.resumeCall world (vecRootFrame world reference (.live none)) 3 returned with
    | next changed =>
      simp only [resumed,evalCode,Option.some.injEq] at computed
      subst flow
      obtain ⟨slot,shape⟩ := vec_byte_resume_next world reference returned changed resumed
      rw [resumed] at resumedHeap
      exact ⟨slot,shape,resumedHeap.heap_eq.trans heapSame⟩
    | unwind changed =>
      have unwindEq : ∃ final, returned = .unwind final ∧ changed = vecRootFrame final reference (.live none) := by
        cases returned with
        | unwind final => simp only [NativeRecordDropCalls.resumeCall,NativeRecordDropCalls.Resume.unwind.injEq] at resumed; exact ⟨final,rfl,resumed.symm⟩
        | normal frame | invalid final | unsupported source final => cases resumed
        | returned value final =>
          simp only [NativeRecordDropCalls.resumeCall] at resumed
          split at resumed <;> try cases resumed
          split at resumed <;> cases resumed
      obtain ⟨final,returnedEq,changedEq⟩ := unwindEq
      subst returned
      subst changed
      have carried := NativeIncomingReference.resident preserved resident older heapSame
      have called : evalCode (vecRawStage true) (vecRootFrame final reference (.live none)) = some flow := by
        simpa only [resumed,vecRawStage,ite_true] using computed
      have checked := vec_raw_stage_post true final reference (.live none) base buffer capacity length carried flow called
      have before : final.pointers.heap = world.pointers.heap := heapSame
      cases flow with
      | normal changed =>
        have continued := evalCode_normal_budget (vecRawStage true) _ changed called
        have stopped : (heapBudget (vecRawStage true)).canContinue = false := by decide
        rw [stopped] at continued
        cases continued
      | returned value final | unwind final | invalid final | unsupported source final =>
        simpa only [VecBytePost,VecDeallocationPost,before] using checked
    | invalid final =>
      simp only [resumed,Option.some.injEq] at computed
      subst flow
      rw [resumed] at resumedHeap
      exact Or.inl (resumedHeap.heap_eq.trans heapSame)
    | unsupported source final =>
      simp only [resumed,Option.some.injEq] at computed
      subst flow
      rw [resumed] at resumedHeap
      exact Or.inl (resumedHeap.heap_eq.trans heapSame)


def vecGlueEntry (world : State) (reference : Reference) : Frame :=
  ⟨f1.types,[.dead,.live (some (.scalar (.reference true reference 3))),.dead,.dead,.dead,.dead,.dead,.dead],world⟩

theorem vec_glue_initial (world : State) (reference : Reference) :
    initial f1.types f1.argCount [.scalar (.reference true reference 3)] world = some (vecGlueEntry world reference) := by
  simp [initial,f1,vecGlueEntry,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem vec_root_prefix_body : vecRootParts.1 =
    .live 0 (.live 2 (.live 3 (.assign 0 (.aggregate none none [])
      (.assign 2 (.vec (.borrow .whole) 1 []) .done)))) := by rfl

theorem vec_root_prefix_invalid (world failed : State) (reference : Reference)
    (borrowed : NativeVecReference.reborrow world (.reference true reference 3) .whole = .invalid failed) :
    eval vecRootParts.1 (vecGlueEntry world reference) = .invalid failed := by
  rw [vec_root_prefix_body]
  simp [vecGlueEntry,f1,eval,evalRvalue,evalArgs,evalVec,NativeVecReference.eval,storageLive,write,
    NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,borrowed]

theorem vec_root_prefix_value (world entered : State) (reference child : Reference)
    (borrowed : NativeVecReference.reborrow world (.reference true reference 3) .whole =
      .value (.reference true child 3) entered) :
    eval vecRootParts.1 (vecGlueEntry world reference) = .normal (vecByteCaller entered reference child) := by
  rw [vec_root_prefix_body]
  simp [vecGlueEntry,vecByteCaller,f1,eval,evalRvalue,evalArgs,evalVec,NativeVecReference.eval,storageLive,write,
    NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,borrowed]

theorem vec_root_body_post (world : State) (reference : Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 3) base capacity length buffer)
    (older : reference.tag < world.nextTag) (flow : Flow)
    (computed : evalCode (.native vecRootParts.1 vecByteCall) (vecGlueEntry world reference) = some flow) :
    VecBytePost world reference buffer capacity flow := by
  have borrowedHeap := NativeVecReference.reborrow_heap_projects world (.reference true reference 3) .whole
  have preserved := NativeVecReference.reborrow_incoming_projects world (.reference true reference 3) .whole
  cases borrowed : NativeVecReference.reborrow world (.reference true reference 3) .whole with
  | invalid failed =>
    rw [evalCode.eq_2,vec_root_prefix_invalid world failed reference borrowed] at computed
    cases computed
    left
    simpa only [borrowed,NativeRawVecFields.Result.world,Flow.world] using borrowedHeap.heap_eq
  | value output entered =>
    obtain ⟨_,_,_,_,prepared,_,_,_,_,outputEq⟩ := NativeVecReference.reborrow_success world entered _ output .whole borrowed
    subst output
    have before : entered.pointers.heap = world.pointers.heap := by
      simpa only [borrowed,NativeRawVecFields.Result.world,Flow.world] using borrowedHeap.heap_eq
    have prior : NativeIncomingReference.Preserves world entered := by
      simpa only [borrowed,NativeRawVecFields.Result.world] using preserved
    have carried := NativeIncomingReference.resident prior resident older before
    have age : reference.tag < entered.nextTag := Nat.lt_of_lt_of_le older prior.counter
    have called : evalCode vecByteCall (vecByteCaller entered reference ⟨prepared.nextTag⟩) = some flow := by
      simpa only [evalCode.eq_2,vec_root_prefix_value world entered reference ⟨prepared.nextTag⟩ borrowed] using computed
    have checked := vec_byte_call_post entered reference ⟨prepared.nextTag⟩ base buffer capacity length carried age flow called
    cases flow <;> simpa only [VecBytePost,VecDeallocationPost,before] using checked

/-- Every outer Vec glue outcome preserves the heap or frees the original
stored buffer with its capacity-byte layout, including both unwind paths. -/
theorem vec_glue_code_post (world : State) (reference : Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 3) base capacity length buffer)
    (older : reference.tag < world.nextTag) (flow : Flow)
    (computed : evalCode f1.code (vecGlueEntry world reference) = some flow) :
    VecDeallocationPost world buffer capacity flow := by
  rw [vec_root_code] at computed
  change evalCode (.scope (.native vecRootParts.1 vecByteCall) (vecRawStage false)) (vecGlueEntry world reference) = some flow at computed
  cases actual : evalCode (.native vecRootParts.1 vecByteCall) (vecGlueEntry world reference) with
  | none => simp only [evalCode.eq_3,actual] at computed; cases computed
  | some returned =>
    have checked := vec_root_body_post world reference base buffer capacity length resident older returned actual
    cases returned with
    | normal middle =>
      obtain ⟨slot,shape,before⟩ := checked
      have authority := evalCode_incoming (.native vecRootParts.1 vecByteCall) (vecGlueEntry world reference) (.normal middle) actual
      have incoming : Resident middle.world (.reference true reference 3) base capacity length buffer :=
        NativeIncomingReference.resident authority resident older before
      have carried := closeScope_resident (entered := world) incoming older
      have cleanup := NativeReferenceCleanup.closeScope_heap_projects world middle.world
      by_cases complete : (NativeReferenceCleanup.closeScope world middle.world).pending.isEmpty = true
      · have later : evalCode (vecRawStage false) {middle with world := (NativeReferenceCleanup.closeScope world middle.world).world} = some flow := by
          simpa only [evalCode.eq_3,actual,NativeRecordDropCalls.resumeScope,show (vecGlueEntry world reference).world = world from rfl,complete,ite_true] using computed
        have canonical : {middle with world := (NativeReferenceCleanup.closeScope world middle.world).world} =
            vecRootFrame (NativeReferenceCleanup.closeScope world middle.world).world reference slot := by rw [shape]; rfl
        rw [canonical] at later
        have post := vec_raw_stage_post false _ reference slot base buffer capacity length carried flow later
        simpa only [VecDeallocationPost,cleanup.heap_eq,before] using post
      · simp only [evalCode.eq_3,actual,NativeRecordDropCalls.resumeScope,show (vecGlueEntry world reference).world = world from rfl,complete,Bool.false_eq_true,ite_false,Option.some.injEq] at computed
        subst flow
        exact Or.inl (cleanup.heap_eq.trans before)
    | returned value final | unwind final | invalid final | unsupported source final =>
      simp only [evalCode.eq_3,actual,NativeRecordDropCalls.resumeScope,Option.some.injEq] at computed
      subst flow
      exact checked


theorem vec_resident_decode (world : State) (reference : Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 3) base capacity length buffer) :
    NativeVecReference.decodeExclusive world (world.references.idxOf reference) = some (.reference true reference 3) := by
  obtain ⟨mutable,ref,count,lease,same,member,registered,_,mode,shape,_,_⟩ := resident
  cases same
  have layout : lease.layout = ⟨24,8⟩ := by
    rcases shape with ⟨_,layout⟩ | ⟨impossible,_⟩
    · exact layout
    · exact False.elim ((by decide : (3 : NativeWord64Memory.Word) ≠ 2) impossible)
  simp only [NativeVecReference.decodeExclusive,List.getElem?_idxOf member,registered,
    Option.bind_eq_bind',Option.bind_some,mode,layout,NativeSliceLLBC.mode,and_self,ite_true]

/-- Invocation-level original-buffer identification for the actual outer source
glue. Registry selection and argument initialization are checked, not assumed. -/
theorem vec_glue_invokes (world : State) (reference : Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 3) base capacity length buffer)
    (older : reference.tag < world.nextTag) (flow : Flow)
    (invoked : NativeRecordDropCalls.Invokes f1 world [.vectorExclusiveReference (world.references.idxOf reference)] flow) :
    VecDeallocationPost world buffer capacity flow := by
  have total := invokeCode_total f1 world [.vectorExclusiveReference (world.references.idxOf reference)] source_loops_checked
  cases actual : invokeCode f1 world [.vectorExclusiveReference (world.references.idxOf reference)] with
  | none => rw [actual] at total; cases total
  | some other =>
    have same := NativeRecordDropCalls.invokes_deterministic f1 world _ flow other invoked
      (invokeCode_sound f1 world _ other actual)
    subst other
    have decoded := vec_resident_decode world reference base buffer capacity length resident
    simp only [invokeCode,decodeArgs,decode,decoded,Option.map_some,Option.bind_eq_bind',Option.bind_some,pure,
      vec_glue_initial,Option.map_eq_some_iff] at actual
    obtain ⟨returned,computed,same⟩ := actual
    subst flow
    exact deallocation_post_heap_eq world buffer capacity returned _ (settle_heap_projects world returned).heap_eq
      (vec_glue_code_post world reference base buffer capacity length resident older returned computed)


theorem vec_glue_invokes_zero (world : State) (reference : Reference)
    (base buffer : NativePointerStorage.Pointer) (length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 3) base 0 length buffer)
    (older : reference.tag < world.nextTag) (flow : Flow)
    (invoked : NativeRecordDropCalls.Invokes f1 world [.vectorExclusiveReference (world.references.idxOf reference)] flow) :
    flow.world.pointers.heap = world.pointers.heap := by
  rcases vec_glue_invokes world reference base buffer 0 length resident older flow invoked with same | ⟨positive,_⟩
  · exact same
  · cases positive

theorem vec_glue_changed_block (world : State) (reference : Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 3) base capacity length buffer)
    (older : reference.tag < world.nextTag) (flow : Flow)
    (invoked : NativeRecordDropCalls.Invokes f1 world [.vectorExclusiveReference (world.references.idxOf reference)] flow)
    (changed : flow.world.pointers.heap ≠ world.pointers.heap) :
    0 < capacity.val ∧ ∃ block ∈ world.pointers.heap.memory.blocks,
      block.pointer = buffer ∧ block.layout = ⟨capacity.val,1⟩ ∧
      NativePointerByteMemory.deallocate world.pointers.heap block.pointer block.layout = some flow.world.pointers.heap := by
  rcases vec_glue_invokes world reference base buffer capacity length resident older flow invoked with same | ⟨positive,freed⟩
  · exact False.elim (changed same)
  · obtain ⟨_,_,memory,_⟩ := NativePointerByteMemory.deallocate_success _ _ _ _ freed
    simp only [NativeByteMemory.deallocate,Option.map_eq_some_iff] at memory
    obtain ⟨blocks,released,_⟩ := memory
    obtain ⟨block,member,pointerEq,layoutEq⟩ := NativeByteMemory.release_selected _ _ _ blocks released
    exact ⟨positive,block,member,pointerEq.symm,layoutEq.symm,by rw [← pointerEq,← layoutEq]; exact freed⟩

end HasteBootsVecDrop
