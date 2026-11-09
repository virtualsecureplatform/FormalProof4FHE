namespace HasteBootsRawVecDeallocation
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

def layoutInput (size alignment : NativeWord64Memory.Word) : Input :=
  .record 9 (.pair (.scalar (.usize size)) (.pair
    (.record 11 (.pair (.enumeration 12 alignment) .unit)) .unit))

theorem body_projects (frame : Frame) :
    NativeReferenceMachine.Runs frame.world (eval f7.body frame).world := eval_projects f7.body frame

theorem invocation_projects (world : NativeReferenceMachine.State) (args : List Input) :
    NativeReferenceMachine.Runs world (invoke f7 world args).world := invoke_projects f7 world args

theorem current_memory_projects (frame : Frame) :
    NativeReferenceMachine.Runs frame.world (eval f8.body frame).world := eval_projects f8.body frame

theorem global_projects (frame : Frame) :
    NativeReferenceMachine.Runs frame.world (eval f9.body frame).world := eval_projects f9.body frame

theorem zero_element_skips_allocator (world borrowed : NativeReferenceMachine.State) (index : Nat)
    (parent child : NativeReferenceMachine.Reference)
    (decoded : NativeRawVecBorrow.decodeExclusive world index = some (.reference true parent 2))
    (created : NativeRawVecBorrow.reborrow world (.reference true parent 2) .whole =
      .value (.reference false child 2) borrowed) :
    invoke f7 world [.rawVecExclusiveReference index,layoutInput 0 1] =
      settle world (.returned (.scalar .unit) borrowed) := by
  simp [invoke, f7, decodeArgs, decode, decoded, initial, layoutInput, eval, evalRvalue,
    evalRawVecBorrow, created, evalOperand, evalArgs, storageLive, storageDead, write,
    NativeRecordLLBC.read, NativeRecordValues.fits, NativeRecordValues.complete,
    NativeRecordValues.compatible, NativeRecordValues.typeAt, NativeRecordValues.get,
    NativeRecordValues.replace, NativeRecordValues.copyable, NativeRecordValues.sideAt,
    selectChoice, NativeSliceLLBC.decodeInput, NativeSliceLLBC.fits, retag,
    NativeSliceLLBC.retagValue, alignmentDiscriminants, settle]

theorem zero_element_preserves_heap (world borrowed final : NativeReferenceMachine.State) (index : Nat)
    (parent child : NativeReferenceMachine.Reference)
    (decoded : NativeRawVecBorrow.decodeExclusive world index = some (.reference true parent 2))
    (created : NativeRawVecBorrow.reborrow world (.reference true parent 2) .whole =
      .value (.reference false child 2) borrowed)
    (returned : invoke f7 world [.rawVecExclusiveReference index,layoutInput 0 1] = .returned (.scalar .unit) final) :
    final.pointers.heap = world.pointers.heap := by
  rw [zero_element_skips_allocator world borrowed index parent child decoded created] at returned
  have cleanupFrame : (NativeReferenceCleanup.closeScope world borrowed).world.pointers.heap = borrowed.pointers.heap :=
    congrArg (fun state => state.pointers.heap)
      (NativeReferenceCleanup.release_frame borrowed (NativeReferenceCleanup.scopeTags world borrowed))
  by_cases complete : (NativeReferenceCleanup.closeScope world borrowed).pending.isEmpty = true
  · simp [settle, NativeReferenceCleanup.settleUnit, complete] at returned
    rw [← returned]
    exact cleanupFrame.trans (NativeRawVecBorrow.reborrow_preserves_heap world borrowed _ _ .whole created)
  · simp [settle, NativeReferenceCleanup.settleUnit, complete] at returned

def externalEntry (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (size : NativeWord64Memory.Word) : Frame :=
  ⟨f12.types,[.dead,.live (some (.record 7 (.pair (.scalar (.raw ⟨pointer,none⟩)) (.scalar .unit)))),
    .live (some (.scalar (.usize size))),
    .live (some (.record 11 (.pair (.enumeration 12 1) (.scalar .unit))))],world⟩

theorem external_exact (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (size : NativeWord64Memory.Word) (nonnull : pointer.address.val ≠ 0) :
    eval f12.body (externalEntry world pointer size) =
      match NativeByteDeallocation.execute world ⟨pointer,none⟩ size 1 with
      | none => .invalid world
      | some next => .returned (.scalar .unit) next := by
  simp [f12, externalEntry, eval, deallocate, evalArgs, evalOperand, NativeRecordLLBC.read,
    NativeRecordValues.fits, NativeRecordValues.complete, NativeRecordValues.compatible,
    NativeRecordValues.typeAt, NativeRecordValues.get, NativeRecordValues.replace,
    NativeSliceLLBC.fits, nonnull, alignmentDiscriminants]
  rfl

theorem external_normal_return_frees_one (world next : NativeReferenceMachine.State)
    (pointer : NativePointerStorage.Pointer) (size : NativeWord64Memory.Word)
    (nonnull : pointer.address.val ≠ 0)
    (returned : eval f12.body (externalEntry world pointer size) = .returned (.scalar .unit) next) :
    next.pointers.heap.memory.blocks.length + 1 = world.pointers.heap.memory.blocks.length := by
  rw [external_exact world pointer size nonnull] at returned
  cases freed : NativeByteDeallocation.execute world ⟨pointer,none⟩ size 1 with
  | none => rw [freed] at returned; cases returned
  | some released =>
    rw [freed] at returned
    cases returned
    exact NativeByteDeallocation.execute_frees_one world next ⟨pointer,none⟩ size 1 freed

end HasteBootsRawVecDeallocation
