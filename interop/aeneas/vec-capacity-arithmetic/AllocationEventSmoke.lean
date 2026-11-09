namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def eventFields : NativeRecordValues.Ty := .scalar .unit
private def eventFormatter (text : String) (world : NativeReferenceMachine.State) : Flow := .unsupported text world
private def eventPanic (text : String) (world : NativeReferenceMachine.State) : Flow := .unsupported text world
private def eventShim : NativeAllocatorLLBC.Body := .legacy (.live 0 (.assign 0 .unit .ret)) .done
private def eventOccupied : NativeReferenceMachine.State := NativeAllocatorExecution.allocated NativeReferenceMachine.empty 8 ⟨3,1⟩
private def eventBefore : NativeReferenceMachine.State := NativeZstBorrow.granted eventOccupied 64
private def eventAfter : NativeReferenceMachine.State := NativeAllocatorExecution.allocated eventBefore 16 ⟨3,1⟩

example : NativeReferenceMachine.execute eventBefore (.raw (.allocate 16 ⟨3,1⟩)) = some eventAfter := by decide

example : eventAfter.pointers.history = ⟨16,⟨3,1⟩,1⟩ :: eventBefore.pointers.history := by decide

example : NativePointerMachine.Issued eventAfter.pointers ⟨16,1⟩ := by
  exact allocator_success_issued eventBefore eventAfter 16 3 1 ⟨16,some ⟨16,1⟩⟩ (by decide)

example : ¬ NativePointerMachine.Issued eventBefore.pointers ⟨16,1⟩ := by
  simp [NativePointerMachine.Issued,eventBefore,eventOccupied,NativeZstBorrow.granted,NativeZstBorrow.placed,NativePointerMachine.push,NativePointerMachine.Allocation.origin,
    NativeAllocatorExecution.allocated,NativeReferenceMachine.empty,NativePointerMachine.empty,NativePointerByteMemory.empty,NativeByteMemory.empty]

example : terminalRootInvoke eventFields eventFormatter eventPanic eventOccupied 256 64 (some 16) eventShim 3 =
    .returned (positiveVecValue ⟨16,some ⟨16,1⟩⟩ 3) eventAfter := by decide

example : eventAfter.leases = eventBefore.leases ∧ eventAfter.references = eventBefore.references ∧
    eventAfter.births = eventBefore.births ∧ eventAfter.nextTag = eventBefore.nextTag := by decide

end HasteBootsVecCapacityArithmetic
