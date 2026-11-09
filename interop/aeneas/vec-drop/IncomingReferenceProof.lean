namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC (Frame Flow)
open NativeReferenceMachine (State)
open NativeByteSliceIndex (Slice)
open NativeIncomingReference (Preserves)

theorem loopOutcome_incoming (world : State) (slice : Slice) : Preserves world (loopOutcome world slice).world := by
  simp only [loopOutcome]
  split <;> exact NativeIncomingReference.run world slice

/-- The actual retained loop preserves incoming references and old leases on
every outcome, including a rejected argument or failed iteration prefix. -/
theorem loop_code_incoming (classification : NativeByteDropCalls.Classification) (frame : Frame) (flow : Flow)
    (executed : NativeRecordDropCalls.Runs (.loop classification HasteBootsVecByteLoop.f6) frame flow) :
    Preserves frame.world flow.world ∧ flow.world.pointers.heap = frame.world.pointers.heap := by
  have computed := (evalCode_iff (.loop classification HasteBootsVecByteLoop.f6) frame flow (by simp only [sourceLoops,beq_self_eq_true])).mp executed
  cases argument : NativeRecordDropCalls.loopArgument frame with
  | none =>
    simp only [evalCode,ite_true,argument,Option.some.injEq] at computed
    subst flow
    exact ⟨.refl _,rfl⟩
  | some slice =>
    simp only [evalCode,ite_true,argument,Option.some.injEq] at computed
    subst flow
    exact ⟨loopOutcome_incoming frame.world slice,loopOutcome_heap_frame frame.world slice⟩

theorem loop_code_resident (classification : NativeByteDropCalls.Classification) (frame : Frame) (flow : Flow)
    (mutable : Bool) (reference : NativeReferenceMachine.Reference) (count capacity length : NativeWord64Memory.Word)
    (base buffer : NativePointerStorage.Pointer)
    (view : NativeResidentVecBorrow.Resident frame.world (.reference mutable reference count) base capacity length buffer)
    (older : reference.tag < frame.world.nextTag)
    (executed : NativeRecordDropCalls.Runs (.loop classification HasteBootsVecByteLoop.f6) frame flow) :
    NativeResidentVecBorrow.Resident flow.world (.reference mutable reference count) base capacity length buffer := by
  obtain ⟨preserved,heap⟩ := loop_code_incoming classification frame flow executed
  exact NativeIncomingReference.resident preserved view older heap
end HasteBootsVecDrop
