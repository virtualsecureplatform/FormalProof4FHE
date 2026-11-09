namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeResidentVecBorrow
open NativeRecordCallValues

def currentMemoryLayoutValue : NativeRecordValues.Value := .record 9 (.pair (.scalar (.usize 1)) (.pair
  (.record 11 (.pair (.enumeration 12 1) (.scalar .unit))) (.scalar .unit)))

theorem current_memory_values_eq (world : NativeReferenceMachine.State)
    (reference : NativeReferenceMachine.Reference) (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference false reference 2) base capacity length buffer) :
    invokeValues HasteBootsRawVecDrop.f8 world [.scalar (.reference false reference 2),currentMemoryLayoutValue] =
      invoke HasteBootsRawVecDrop.f8 world [.rawVecSharedReference (world.references.idxOf reference),currentMemoryLayout] := by
  simp only [NativeRecordCallValues.invoke_eq,decodeArgs,decode,shared_rawvec_decode resident,
    currentMemoryLayout,currentMemoryLayoutValue,NativeSliceLLBC.decodeInput,Option.map_some,Option.bind_eq_bind',Option.bind_some,pure]

theorem current_memory_values (world : NativeReferenceMachine.State)
    (reference : NativeReferenceMachine.Reference) (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference false reference 2) base capacity length buffer) :
    currentMemoryPost capacity buffer (invokeValues HasteBootsRawVecDrop.f8 world
      [.scalar (.reference false reference 2),currentMemoryLayoutValue]) := by
  rw [current_memory_values_eq world reference base buffer capacity length resident]
  exact current_memory_resident world reference base buffer capacity length resident

theorem current_memory_values_heap (world : NativeReferenceMachine.State) (args : List NativeRecordValues.Value) :
    (invokeValues HasteBootsRawVecDrop.f8 world args).world.pointers.heap = world.pointers.heap := by
  have bound := invokeValues_loss HasteBootsRawVecDrop.f8 world args
  have budget : deallocationBudget HasteBootsRawVecDrop.f8.body = 0 := by decide
  rw [budget] at bound
  apply bound.unchanged
  have bounded := bound.bounded
  have growth := bound.no_growth
  omega

theorem current_memory_values_cases (world : NativeReferenceMachine.State)
    (reference : NativeReferenceMachine.Reference) (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference false reference 2) base capacity length buffer) :
    ∃ final, final.pointers.heap = world.pointers.heap ∧
      (invokeValues HasteBootsRawVecDrop.f8 world [.scalar (.reference false reference 2),currentMemoryLayoutValue] = .invalid final ∨
       invokeValues HasteBootsRawVecDrop.f8 world [.scalar (.reference false reference 2),currentMemoryLayoutValue] =
         .returned (if capacity = 0 then currentMemoryNone else currentMemorySome buffer capacity) final) := by
  have checked := current_memory_values world reference base buffer capacity length resident
  have frame := current_memory_values_heap world [.scalar (.reference false reference 2),currentMemoryLayoutValue]
  generalize actual : invokeValues HasteBootsRawVecDrop.f8 world [.scalar (.reference false reference 2),currentMemoryLayoutValue] = flow at checked frame ⊢
  cases flow with
  | invalid final => exact ⟨final,frame,Or.inl rfl⟩
  | returned value final =>
    change value = _ at checked
    exact ⟨final,frame,Or.inr (by rw [checked])⟩
  | normal changed => cases checked
  | unwind final => cases checked
  | unsupported source final => cases checked

def globalValues (allocator : NativeReferenceMachine.Reference) (buffer : NativePointerStorage.Pointer)
    (capacity : NativeWord64Memory.Word) : List NativeRecordValues.Value :=
  [.scalar (.reference false allocator 0),
   .record 7 (.pair (.scalar (.raw ⟨buffer,none⟩)) (.scalar .unit)),
   .record 9 (.pair (.scalar (.usize capacity)) (.pair
     (.record 11 (.pair (.enumeration 12 1) (.scalar .unit))) (.scalar .unit)))]

def freeFlow (world : NativeReferenceMachine.State) (buffer : NativePointerStorage.Pointer)
    (capacity : NativeWord64Memory.Word) : Flow :=
  match NativeByteDeallocation.execute world ⟨buffer,none⟩ capacity 1 with
  | none => .invalid world
  | some next => .returned (.scalar .unit) next

theorem global_values_zero (world : NativeReferenceMachine.State) (allocator : NativeReferenceMachine.Reference)
    (buffer : NativePointerStorage.Pointer) (nonnull : buffer.address.val ≠ 0) :
    invokeValues HasteBootsRawVecDrop.f9 world (globalValues allocator buffer 0) = settle world (.returned (.scalar .unit) world) := by
  simp [invokeValues,HasteBootsRawVecDrop.f9,globalValues,initial,eval,evalRvalue,evalArgs,evalOperand,
    storageLive,storageDead,write,NativeRecordLLBC.read,retag,NativeSliceLLBC.retagValue,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.copyable,
    HasteBootsRawVecDrop.alignmentDiscriminants,NativeSliceLLBC.fits,nonnull]

theorem global_values_nonzero (world : NativeReferenceMachine.State) (allocator : NativeReferenceMachine.Reference)
    (buffer : NativePointerStorage.Pointer) (capacity : NativeWord64Memory.Word)
    (nonnull : buffer.address.val ≠ 0) (nonzero : capacity ≠ 0) :
    invokeValues HasteBootsRawVecDrop.f9 world (globalValues allocator buffer capacity) =
      settle world (settle world (freeFlow world buffer capacity)) := by
  cases freed : NativeByteDeallocation.execute world ⟨buffer,none⟩ capacity 1 with
  | none =>
    simp [invokeValues,HasteBootsRawVecDrop.f9,globalValues,initial,eval,evalRvalue,evalArgs,evalOperand,
      storageLive,write,NativeRecordLLBC.read,retag,NativeSliceLLBC.retagValue,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
      NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.copyable,
      HasteBootsRawVecDrop.alignmentDiscriminants,NativeSliceLLBC.fits,nonnull,nonzero,deallocate,freed,freeFlow,settle]
  | some next =>
    by_cases complete : (NativeReferenceCleanup.closeScope world next).pending.isEmpty = true
    · simp [invokeValues,HasteBootsRawVecDrop.f9,globalValues,initial,eval,evalRvalue,evalArgs,evalOperand,
      storageLive,storageDead,write,NativeRecordLLBC.read,retag,NativeSliceLLBC.retagValue,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
      NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.copyable,
      HasteBootsRawVecDrop.alignmentDiscriminants,NativeSliceLLBC.fits,nonnull,nonzero,deallocate,freed,freeFlow,
      settle,NativeReferenceCleanup.settleUnit,complete]
    · simp [invokeValues,HasteBootsRawVecDrop.f9,globalValues,initial,eval,evalRvalue,evalArgs,evalOperand,
      storageLive,write,NativeRecordLLBC.read,retag,NativeSliceLLBC.retagValue,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
      NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.copyable,
      HasteBootsRawVecDrop.alignmentDiscriminants,NativeSliceLLBC.fits,nonnull,nonzero,deallocate,freed,freeFlow,
      settle,NativeReferenceCleanup.settleUnit,complete]
theorem global_values_effect (world : NativeReferenceMachine.State) (allocator : NativeReferenceMachine.Reference)
    (buffer : NativePointerStorage.Pointer) (capacity : NativeWord64Memory.Word) (nonnull : buffer.address.val ≠ 0) :
    (invokeValues HasteBootsRawVecDrop.f9 world (globalValues allocator buffer capacity)).world.pointers.heap = world.pointers.heap ∨
      NativePointerByteMemory.deallocate world.pointers.heap buffer ⟨capacity.val,1⟩ =
        some (invokeValues HasteBootsRawVecDrop.f9 world (globalValues allocator buffer capacity)).world.pointers.heap := by
  by_cases zero : capacity = 0
  · subst capacity
    rw [global_values_zero world allocator buffer nonnull]
    exact Or.inl (settle_heap_projects world (.returned (.scalar .unit) world)).heap_eq
  · rw [global_values_nonzero world allocator buffer capacity nonnull zero]
    have frame := (settle_heap_projects world (settle world (freeFlow world buffer capacity))).heap_eq.trans
      (settle_heap_projects world (freeFlow world buffer capacity)).heap_eq
    cases released : NativeByteDeallocation.execute world ⟨buffer,none⟩ capacity 1 with
    | none =>
      left
      simpa only [freeFlow,released,Flow.world] using frame
    | some next =>
      right
      obtain ⟨heap,freed,changed⟩ := NativeByteDeallocation.execute_heap world next ⟨buffer,none⟩ capacity 1 released
      have nextHeap := congrArg (fun state : NativeReferenceMachine.State => state.pointers.heap) changed
      have heapEq : (freeFlow world buffer capacity).world.pointers.heap = heap := by
        simpa only [freeFlow,released,Flow.world] using nextHeap
      exact freed.trans (congrArg Option.some (frame.trans heapEq)).symm

theorem global_values_unit (world : NativeReferenceMachine.State) (allocator : NativeReferenceMachine.Reference)
    (buffer : NativePointerStorage.Pointer) (capacity : NativeWord64Memory.Word) (nonnull : buffer.address.val ≠ 0) :
    UnitResult (invokeValues HasteBootsRawVecDrop.f9 world (globalValues allocator buffer capacity)) := by
  by_cases zero : capacity = 0
  · subst capacity
    rw [global_values_zero world allocator buffer nonnull]
    exact UnitResult.settle world _ rfl
  · rw [global_values_nonzero world allocator buffer capacity nonnull zero]
    apply UnitResult.settle
    apply UnitResult.settle
    cases freed : NativeByteDeallocation.execute world ⟨buffer,none⟩ capacity 1 <;>
      simp only [freeFlow,freed,UnitResult]

theorem global_values_cases (world : NativeReferenceMachine.State) (allocator : NativeReferenceMachine.Reference)
    (buffer : NativePointerStorage.Pointer) (capacity : NativeWord64Memory.Word) (nonnull : buffer.address.val ≠ 0) :
    ∃ final, (final.pointers.heap = world.pointers.heap ∨
      NativePointerByteMemory.deallocate world.pointers.heap buffer ⟨capacity.val,1⟩ = some final.pointers.heap) ∧
      (invokeValues HasteBootsRawVecDrop.f9 world (globalValues allocator buffer capacity) = .invalid final ∨
       invokeValues HasteBootsRawVecDrop.f9 world (globalValues allocator buffer capacity) = .returned (.scalar .unit) final) := by
  have frame := global_values_effect world allocator buffer capacity nonnull
  have checked := global_values_unit world allocator buffer capacity nonnull
  generalize actual : invokeValues HasteBootsRawVecDrop.f9 world (globalValues allocator buffer capacity) = flow at frame checked ⊢
  cases flow with
  | returned value final =>
    change value = .scalar .unit at checked
    subst value
    exact ⟨final,frame,Or.inr rfl⟩
  | invalid final => exact ⟨final,frame,Or.inl rfl⟩
  | normal changed => cases checked
  | unwind final => cases checked
  | unsupported source final => cases checked

/-- Structural call view of the retained caller, checked against its complete body. -/
def memoryCallTail : Body → Option (Body × Body)
  | .live _ next | .dead _ next | .assign _ _ next => memoryCallTail next
  | .call _ _ _ _ _ _ _ unwind next => some (unwind,next)
  | _ => none

def deallocationTail : Body × Body := (memoryCallTail HasteBootsRawVecDrop.f7.body).get (by decide)

theorem deallocation_body : HasteBootsRawVecDrop.f7.body =
    .live 0 (.live 7 (.assign 0 (.aggregate none none []) (.live 3 (.live 4
      (.assign 4 (.borrowRawVec .whole 1 [])
        (.call HasteBootsRawVecDrop.f8.name HasteBootsRawVecDrop.f8.classification HasteBootsRawVecDrop.f8.types
          HasteBootsRawVecDrop.f8.argCount 3 [.move 4 [],.move 2 []] HasteBootsRawVecDrop.f8.body
          deallocationTail.1 deallocationTail.2)))))) := by rfl

def deallocationCaller (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference) : Frame :=
  ⟨HasteBootsRawVecDrop.f7.types,
    [.live (some (.scalar .unit)),.live (some (.scalar (.reference true reference 2))),
     .live (some .uninit),.live none,.live (some .uninit),.dead,.dead,.live none,.dead],world⟩

def deallocationEntry (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference) : Frame :=
  ⟨HasteBootsRawVecDrop.f7.types,
    [.dead,.live (some (.scalar (.reference true reference 2))),.live (some currentMemoryLayoutValue)] ++ List.replicate 6 .dead,world⟩

theorem deallocation_initial (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference) :
    initial HasteBootsRawVecDrop.f7.types HasteBootsRawVecDrop.f7.argCount
      [.scalar (.reference true reference 2),currentMemoryLayoutValue] world = some (deallocationEntry world reference) := by
  simp [initial,HasteBootsRawVecDrop.f7,deallocationEntry,currentMemoryLayoutValue,NativeRecordValues.fits,
    NativeRecordValues.compatible,NativeRecordValues.complete,NativeSliceLLBC.fits,HasteBootsRawVecDrop.alignmentDiscriminants]

theorem deallocation_prefix (world : NativeReferenceMachine.State) (reference child : NativeReferenceMachine.Reference)
    (borrowed : NativeReferenceMachine.State)
    (created : NativeRawVecBorrow.reborrow world (.reference true reference 2) .whole =
      .value (.reference false child 2) borrowed) :
    invokeValues HasteBootsRawVecDrop.f7 world [.scalar (.reference true reference 2),currentMemoryLayoutValue] =
      settle world (resume (deallocationCaller borrowed reference) 3 deallocationTail.1 deallocationTail.2
        (invokeValues HasteBootsRawVecDrop.f8 borrowed [.scalar (.reference false child 2),currentMemoryLayoutValue])) := by
  rw [invokeValues_initialized HasteBootsRawVecDrop.f7 world _ (deallocationEntry world reference)
    (deallocation_initial world reference),deallocation_body]
  simp [deallocationEntry,deallocationCaller,HasteBootsRawVecDrop.f7,eval.eq_6,eval.eq_8,
    NativeRecordCallValues.eval_call HasteBootsRawVecDrop.f8,evalRvalue,evalRawVecBorrow,created,evalArgs,evalOperand,
    storageLive,write,NativeRecordLLBC.read,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
    NativeSliceLLBC.fits,currentMemoryLayoutValue,HasteBootsRawVecDrop.alignmentDiscriminants,
    List.replicate_succ,List.replicate_zero]

theorem deallocation_borrow_invalid (world failed : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (created : NativeRawVecBorrow.reborrow world (.reference true reference 2) .whole = .invalid failed) :
    invokeValues HasteBootsRawVecDrop.f7 world [.scalar (.reference true reference 2),currentMemoryLayoutValue] = .invalid failed := by
  rw [invokeValues_initialized HasteBootsRawVecDrop.f7 world _ (deallocationEntry world reference)
    (deallocation_initial world reference),deallocation_body]
  simp [deallocationEntry,HasteBootsRawVecDrop.f7,eval.eq_6,eval.eq_8,evalRvalue,evalRawVecBorrow,created,evalArgs,
    storageLive,write,NativeRecordLLBC.read,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeSliceLLBC.fits,currentMemoryLayoutValue,HasteBootsRawVecDrop.alignmentDiscriminants,settle]

theorem deallocation_none (world final : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference) :
    resume (deallocationCaller world reference) 3 deallocationTail.1 deallocationTail.2 (.returned currentMemoryNone final) =
      .returned (.scalar .unit) final := by
  simp [resume,deallocationCaller,deallocationTail,memoryCallTail,HasteBootsRawVecDrop.f7,currentMemoryNone,
    write,storageDead,selectChoice,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.sideAt,NativeRecordValues.fits,NativeRecordValues.compatible,NativeRecordValues.complete,NativeSliceLLBC.fits,eval]

theorem deallocation_values_zero (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base 0 length buffer) :
    (invokeValues HasteBootsRawVecDrop.f7 world [.scalar (.reference true reference 2),currentMemoryLayoutValue]).world.pointers.heap =
      world.pointers.heap := by
  have borrowedFrame := (NativeRawVecBorrow.reborrow_heap_projects world (.reference true reference 2) .whole).heap_eq
  cases created : NativeRawVecBorrow.reborrow world (.reference true reference 2) .whole with
  | invalid failed =>
    rw [deallocation_borrow_invalid world failed reference created]
    simpa only [created,NativeRawVecFields.Result.world,Flow.world] using borrowedFrame
  | value value borrowed =>
    have carried := rawvec_reborrow resident created
    obtain ⟨child,valueEq,_⟩ := NativeRawVecBorrow.reborrow_issued_reference world borrowed _ _ .whole created
    change value = .reference false child 2 at valueEq
    subst value
    rw [deallocation_prefix world reference child borrowed created]
    obtain ⟨final,frame,failed | returned⟩ := current_memory_values_cases borrowed child base buffer 0 length carried
    · rw [failed]
      simpa only [resume,settle,Flow.world] using frame.trans (by simpa only [created,NativeRawVecFields.Result.world,Flow.world] using borrowedFrame)
    · rw [ite_eq_left rfl] at returned
      rw [returned,deallocation_none]
      exact (settle_heap_projects world (.returned (.scalar .unit) final)).heap_eq.trans
        (frame.trans (by simpa only [created,NativeRawVecFields.Result.world,Flow.world] using borrowedFrame))

def allocatorCallTail : Body → Option (Body × Body)
  | .live _ next | .dead _ next | .assign _ _ next | .matchChoice _ _ _ _ _ next => allocatorCallTail next
  | .call _ _ _ _ _ _ _ unwind next => some (unwind,next)
  | _ => none

def deallocationGlobalTail : Body × Body := (allocatorCallTail deallocationTail.2).get (by decide)

theorem deallocation_some_body : deallocationTail.2 =
    .dead 4 (.matchChoice 3 [] 10 (.dead 3 (.dead 7 (.dead 2 (.dead 1 .ret)))) .done
      (.live 5 (.assign 5 (.use (.copy 3 [.unwrap 10,.active true,.left,.left]) true .byte)
        (.live 6 (.assign 6 (.use (.copy 3 [.unwrap 10,.active true,.left,.right,.left]) true .byte)
          (.live 8 (.assign 8 (.borrowRawVec .allocator 1 [])
            (.call HasteBootsRawVecDrop.f9.name HasteBootsRawVecDrop.f9.classification HasteBootsRawVecDrop.f9.types
              HasteBootsRawVecDrop.f9.argCount 7 [.move 8 [],.move 5 [],.move 6 []] HasteBootsRawVecDrop.f9.body
              deallocationGlobalTail.1 deallocationGlobalTail.2)))))))) := by rfl

def deallocationGlobalCaller (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (buffer : NativePointerStorage.Pointer) (capacity : NativeWord64Memory.Word) : Frame :=
  ⟨HasteBootsRawVecDrop.f7.types,
    [.live (some (.scalar .unit)),.live (some (.scalar (.reference true reference 2))),
     .live (some .uninit),.live (some (currentMemorySome buffer capacity)),.dead,
     .live (some .uninit),.live (some .uninit),.live none,.live (some .uninit)],world⟩

theorem deallocation_some (world memoryWorld allocatorWorld : NativeReferenceMachine.State)
    (reference allocator : NativeReferenceMachine.Reference) (buffer : NativePointerStorage.Pointer)
    (capacity : NativeWord64Memory.Word) (nonnull : buffer.address.val ≠ 0)
    (created : NativeRawVecBorrow.reborrow memoryWorld (.reference true reference 2) .allocator =
      .value (.reference false allocator 0) allocatorWorld) :
    resume (deallocationCaller world reference) 3 deallocationTail.1 deallocationTail.2
      (.returned (currentMemorySome buffer capacity) memoryWorld) =
      resume (deallocationGlobalCaller allocatorWorld reference buffer capacity) 7 deallocationGlobalTail.1 deallocationGlobalTail.2
        (invokeValues HasteBootsRawVecDrop.f9 allocatorWorld (globalValues allocator buffer capacity)) := by
  rw [deallocation_some_body]
  simp [resume,deallocationCaller,deallocationGlobalCaller,HasteBootsRawVecDrop.f7,currentMemorySome,globalValues,
    write,storageLive,storageDead,selectChoice,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.replace,NativeRecordValues.sideAt,NativeRecordValues.fits,NativeRecordValues.compatible,
    NativeRecordValues.complete,NativeRecordValues.copyable,NativeSliceLLBC.fits,nonnull,
    eval.eq_1,eval.eq_6,eval.eq_7,eval.eq_8,eval.eq_10,NativeRecordCallValues.eval_call HasteBootsRawVecDrop.f9,
    evalRvalue,evalRawVecBorrow,created,evalArgs,evalOperand,retag,NativeSliceLLBC.retagValue,HasteBootsRawVecDrop.alignmentDiscriminants]

theorem deallocation_allocator_invalid (world memoryWorld failed : NativeReferenceMachine.State)
    (reference : NativeReferenceMachine.Reference) (buffer : NativePointerStorage.Pointer)
    (capacity : NativeWord64Memory.Word) (nonnull : buffer.address.val ≠ 0)
    (created : NativeRawVecBorrow.reborrow memoryWorld (.reference true reference 2) .allocator = .invalid failed) :
    resume (deallocationCaller world reference) 3 deallocationTail.1 deallocationTail.2
      (.returned (currentMemorySome buffer capacity) memoryWorld) = .invalid failed := by
  rw [deallocation_some_body]
  simp [resume,deallocationCaller,HasteBootsRawVecDrop.f7,currentMemorySome,
    write,storageLive,storageDead,selectChoice,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.sideAt,NativeRecordValues.fits,NativeRecordValues.compatible,
    NativeRecordValues.complete,NativeRecordValues.copyable,NativeSliceLLBC.fits,nonnull,
    eval.eq_1,eval.eq_6,eval.eq_7,eval.eq_8,eval.eq_10,
    evalRvalue,evalRawVecBorrow,created,evalOperand,retag,NativeSliceLLBC.retagValue,HasteBootsRawVecDrop.alignmentDiscriminants]

theorem deallocation_global_unit (world final : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (buffer : NativePointerStorage.Pointer) (capacity : NativeWord64Memory.Word) :
    resume (deallocationGlobalCaller world reference buffer capacity) 7 deallocationGlobalTail.1 deallocationGlobalTail.2
      (.returned (.scalar .unit) final) = .returned (.scalar .unit) final := by
  simp [resume,deallocationGlobalCaller,deallocationGlobalTail,allocatorCallTail,deallocationTail,memoryCallTail,
    HasteBootsRawVecDrop.f7,write,storageDead,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.compatible,NativeRecordValues.complete,NativeSliceLLBC.fits,eval]

/-- Every heap change is the free of the original stored buffer and capacity. -/
def DeallocationPost (world : NativeReferenceMachine.State) (buffer : NativePointerStorage.Pointer)
    (capacity : NativeWord64Memory.Word) (flow : Flow) : Prop :=
  flow.world.pointers.heap = world.pointers.heap ∨
    NativePointerByteMemory.deallocate world.pointers.heap buffer ⟨capacity.val,1⟩ = some flow.world.pointers.heap

theorem deallocation_post_settle (entered world : NativeReferenceMachine.State)
    (buffer : NativePointerStorage.Pointer) (capacity : NativeWord64Memory.Word) (flow : Flow)
    (checked : DeallocationPost world buffer capacity flow) : DeallocationPost world buffer capacity (settle entered flow) := by
  simpa only [DeallocationPost,(settle_heap_projects entered flow).heap_eq] using checked

theorem deallocation_values (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer) :
    DeallocationPost world buffer capacity
      (invokeValues HasteBootsRawVecDrop.f7 world [.scalar (.reference true reference 2),currentMemoryLayoutValue]) := by
  by_cases zero : capacity = 0
  · subst capacity
    exact Or.inl (deallocation_values_zero world reference base buffer length resident)
  · have contents := resident
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,fields⟩ := contents
    have nonnull := fields.nonnull
    have borrowedFrame := (NativeRawVecBorrow.reborrow_heap_projects world (.reference true reference 2) .whole).heap_eq
    cases created : NativeRawVecBorrow.reborrow world (.reference true reference 2) .whole with
    | invalid failed =>
      rw [deallocation_borrow_invalid world failed reference created]
      left
      simpa only [created,NativeRawVecFields.Result.world,Flow.world] using borrowedFrame
    | value value borrowed =>
      have carried := rawvec_reborrow resident created
      obtain ⟨child,valueEq,_⟩ := NativeRawVecBorrow.reborrow_issued_reference world borrowed _ _ .whole created
      change value = .reference false child 2 at valueEq
      subst value
      have borrowedHeap : borrowed.pointers.heap = world.pointers.heap := by
        simpa only [created,NativeRawVecFields.Result.world] using borrowedFrame
      rw [deallocation_prefix world reference child borrowed created]
      apply deallocation_post_settle
      obtain ⟨memoryWorld,memoryFrame,failed | returned⟩ := current_memory_values_cases borrowed child base buffer capacity length carried
      · rw [failed]
        exact Or.inl (memoryFrame.trans borrowedHeap)
      · rw [ite_eq_right zero] at returned
        rw [returned]
        have allocatorFrame := (NativeRawVecBorrow.reborrow_heap_projects memoryWorld (.reference true reference 2) .allocator).heap_eq
        cases allocated : NativeRawVecBorrow.reborrow memoryWorld (.reference true reference 2) .allocator with
        | invalid failed =>
          rw [deallocation_allocator_invalid borrowed memoryWorld failed reference buffer capacity nonnull allocated]
          left
          have failedHeap : failed.pointers.heap = memoryWorld.pointers.heap := by
            simpa only [allocated,NativeRawVecFields.Result.world] using allocatorFrame
          exact failedHeap.trans (memoryFrame.trans borrowedHeap)
        | value value allocatorWorld =>
          obtain ⟨allocator,valueEq,_⟩ := NativeRawVecBorrow.reborrow_issued_reference memoryWorld allocatorWorld _ _ .allocator allocated
          change value = .reference false allocator 0 at valueEq
          subst value
          have allocatedHeap : allocatorWorld.pointers.heap = memoryWorld.pointers.heap := by
            simpa only [allocated,NativeRawVecFields.Result.world] using allocatorFrame
          have allocatorHeap : allocatorWorld.pointers.heap = world.pointers.heap :=
            allocatedHeap.trans (memoryFrame.trans borrowedHeap)
          rw [deallocation_some borrowed memoryWorld allocatorWorld reference allocator buffer capacity nonnull allocated]
          obtain ⟨final,effect,failed | returned⟩ := global_values_cases allocatorWorld allocator buffer capacity nonnull
          · rw [failed]
            simpa only [DeallocationPost,resume,Flow.world,allocatorHeap] using effect
          · rw [returned,deallocation_global_unit]
            simpa only [DeallocationPost,Flow.world,allocatorHeap] using effect

theorem deallocation_changed_buffer (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer)
    (changed : (invokeValues HasteBootsRawVecDrop.f7 world
      [.scalar (.reference true reference 2),currentMemoryLayoutValue]).world.pointers.heap ≠ world.pointers.heap) :
    0 < capacity.val ∧ NativePointerByteMemory.deallocate world.pointers.heap buffer ⟨capacity.val,1⟩ =
      some (invokeValues HasteBootsRawVecDrop.f7 world [.scalar (.reference true reference 2),currentMemoryLayoutValue]).world.pointers.heap := by
  have nonzero : capacity ≠ 0 := by
    intro empty
    subst capacity
    exact changed (deallocation_values_zero world reference base buffer length resident)
  have positive : 0 < capacity.val := by
    have valNonzero : capacity.val ≠ 0 := fun zero => nonzero (Fin.ext zero)
    omega
  refine ⟨positive,?_⟩
  rcases deallocation_values world reference base buffer capacity length resident with same | freed
  · exact False.elim (changed same)
  · exact freed

theorem deallocation_values_eq (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer) :
    invokeValues HasteBootsRawVecDrop.f7 world [.scalar (.reference true reference 2),currentMemoryLayoutValue] =
      invoke HasteBootsRawVecDrop.f7 world [.rawVecExclusiveReference (world.references.idxOf reference),currentMemoryLayout] := by
  obtain ⟨mutable,ref,count,lease,same,member,registered,_,mode,shape,_,_⟩ := resident
  cases same
  have layout : lease.layout = ⟨16,8⟩ := by
    rcases shape with ⟨impossible,_⟩ | ⟨_,layout⟩
    · exact False.elim ((by decide : (2 : NativeWord64Memory.Word) ≠ 3) impossible)
    · exact layout
  have decoded : NativeRawVecBorrow.decodeExclusive world (world.references.idxOf reference) = some (.reference true reference 2) := by
    simp only [NativeRawVecBorrow.decodeExclusive,List.getElem?_idxOf member,registered,Option.bind_eq_bind',Option.bind_some,
      mode,layout,NativeSliceLLBC.mode,and_self,ite_true]
  simp only [NativeRecordCallValues.invoke_eq,decodeArgs,decode,decoded,currentMemoryLayout,currentMemoryLayoutValue,
    NativeSliceLLBC.decodeInput,Option.map_some,Option.bind_eq_bind',Option.bind_some,pure]

theorem deallocation_invocation (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer) :
    DeallocationPost world buffer capacity (invoke HasteBootsRawVecDrop.f7 world
      [.rawVecExclusiveReference (world.references.idxOf reference),currentMemoryLayout]) := by
  rw [← deallocation_values_eq world reference base buffer capacity length resident]
  exact deallocation_values world reference base buffer capacity length resident

theorem deallocation_changed_block (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (base buffer : NativePointerStorage.Pointer) (capacity length : NativeWord64Memory.Word)
    (resident : Resident world (.reference true reference 2) base capacity length buffer)
    (changed : (invokeValues HasteBootsRawVecDrop.f7 world
      [.scalar (.reference true reference 2),currentMemoryLayoutValue]).world.pointers.heap ≠ world.pointers.heap) :
    ∃ block ∈ world.pointers.heap.memory.blocks,
      block.pointer = buffer ∧ block.layout = ⟨capacity.val,1⟩ ∧
      NativePointerByteMemory.deallocate world.pointers.heap block.pointer block.layout =
        some (invokeValues HasteBootsRawVecDrop.f7 world [.scalar (.reference true reference 2),currentMemoryLayoutValue]).world.pointers.heap := by
  have freed := (deallocation_changed_buffer world reference base buffer capacity length resident changed).2
  obtain ⟨_,_,memory,_⟩ := NativePointerByteMemory.deallocate_success _ _ _ _ freed
  simp only [NativeByteMemory.deallocate,Option.map_eq_some_iff] at memory
  obtain ⟨blocks,released,_⟩ := memory
  obtain ⟨block,member,pointerEq,layoutEq⟩ := NativeByteMemory.release_selected _ _ _ blocks released
  exact ⟨block,member,pointerEq.symm,layoutEq.symm,by rw [← pointerEq,← layoutEq]; exact freed⟩

end HasteBootsVecDrop
