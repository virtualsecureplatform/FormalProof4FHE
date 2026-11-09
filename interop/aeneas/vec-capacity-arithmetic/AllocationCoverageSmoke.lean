namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def coverageFields : NativeRecordValues.Ty := .scalar .unit
private def coverageFormatter (text : String) (world : NativeReferenceMachine.State) : Flow := .unsupported text world
private def coveragePanic (text : String) (world : NativeReferenceMachine.State) : Flow := .unsupported text world
private def coverageShim : NativeAllocatorLLBC.Body := .legacy (.live 0 (.assign 0 .unit .ret)) .done
private def coverageBorrowed : NativeReferenceMachine.State := NativeZstBorrow.granted NativeReferenceMachine.empty 64
private def coverageOccupied : NativeReferenceMachine.State := NativeAllocatorExecution.allocated NativeReferenceMachine.empty 8 ⟨3,1⟩
private def coverageInvalid : Flow → Bool
  | .invalid _ => true
  | _ => false

example (outcome : Option NativePointerStorage.Address) :
    terminalRootInvoke coverageFields coverageFormatter coveragePanic NativeReferenceMachine.empty 256 64 outcome coverageShim 3 =
      normalAllocationOutcome coverageFields coverageFormatter coveragePanic NativeReferenceMachine.empty 3 256 64 outcome coverageBorrowed := by
  exact terminal_root_normal_allocation _ _ _ _ _ _ _ (by decide) _ _ _
    (NativeReferenceMachine.reachable_wellFormed _ .empty) (by decide) (by decide) (by decide)

example : terminalRootInvoke coverageFields coverageFormatter coveragePanic NativeReferenceMachine.empty 256 64 (some 0) coverageShim 3 =
    .invalid coverageBorrowed := by decide

example : terminalRootInvoke coverageFields coverageFormatter coveragePanic NativeReferenceMachine.empty 256 64 (some (2^64-1)) coverageShim 3 =
    .invalid coverageBorrowed := by decide

example : coverageInvalid (terminalRootInvoke coverageFields coverageFormatter coveragePanic coverageOccupied 256 64 (some 8) coverageShim 3) = true := by decide

example : (terminalRootInvoke coverageFields coverageFormatter coveragePanic coverageOccupied 256 64 (some 8) coverageShim 3).world.pointers.heap =
    coverageOccupied.pointers.heap := by decide

example : terminalRootInvoke coverageFields coverageFormatter coveragePanic coverageOccupied 256 64 (some 16) coverageShim 3 =
    .returned (positiveVecValue ⟨16,some ⟨16,1⟩⟩ 3)
      (NativeAllocatorExecution.allocated (NativeZstBorrow.granted coverageOccupied 64) 16 ⟨3,1⟩) := by decide

example : (terminalRootInvoke coverageFields coverageFormatter coveragePanic coverageOccupied 256 64 (some 16) coverageShim 3).world.pointers.heap.memory.nextGeneration = 2 := by decide

example (formatter panic : String → NativeReferenceMachine.State → Flow)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State) :
    terminalRootInvoke coverageFields formatter panic NativeReferenceMachine.empty 3 64 none coverageShim (2^63) ≠ .returned value world := by
  exact terminal_root_rejected_no_return coverageFields formatter panic NativeReferenceMachine.empty (2^63) 3 64 (by decide)
    none coverageShim (by decide) (NativeReferenceMachine.reachable_wellFormed _ .empty) value world

example (formatter panic : String → NativeReferenceMachine.State → Flow)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State) :
    terminalRootInvoke coverageFields formatter panic NativeReferenceMachine.empty 3 64 none coverageShim 3 ≠ .returned value world := by
  exact terminal_root_null_no_return coverageFields formatter panic NativeReferenceMachine.empty 3 3 64 (by decide)
    coverageShim coverageBorrowed (NativeReferenceMachine.reachable_wellFormed _ .empty) (by decide) (by decide) (by decide) value world

example (formatter panic : String → NativeReferenceMachine.State → Flow) :
    terminalRootInvoke coverageFields formatter panic NativeReferenceMachine.empty 0 0 (some 0) coverageShim 0 =
      .returned zeroVecValue NativeReferenceMachine.empty := terminal_root_zero _ _ _ _ _ _ _ _

end HasteBootsVecCapacityArithmetic
