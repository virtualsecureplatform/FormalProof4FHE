namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def unitShim : NativeAllocatorLLBC.Body := .legacy (.live 0 (.assign 0 .unit .ret)) .done
private def unusedShim : NativeAllocatorLLBC.Body := .legacy (.unsupported "unexpected shim") .done
private def outerAllocationTerminal : Body := .switchUsize (.copy 1 [(.unwrap 4),.left]) 3
  (.unsupported "allocation size 3") (.unsupported "other allocation size") .abort
private def resultLabel : Flow → Option String
  | .unsupported source _ => some source
  | _ => none
private def rootRun (capacity : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) : Flow :=
  handledRootInvoke NativeReferenceMachine.empty 256 64 outcome shim (.unsupported "capacity overflow") outerAllocationTerminal capacity

example : resultLabel (rootRun (2^63) (some 8) unusedShim) = some "capacity overflow" := by decide
example : resultLabel (rootRun (2^64-1) none unusedShim) = some "capacity overflow" := by decide
example : resultLabel (rootRun 3 none unitShim) = some "allocation size 3" := by decide
example : resultLabel (rootRun 4 none unitShim) = some "other allocation size" := by decide

example : (rootRun 3 none unitShim).world.nextTag = 3 := by decide
example : (rootRun (2^63) none unusedShim).world.nextTag = 2 := by decide

example : NativeByteRange.loadRange (rootRun (2^63) none unusedShim).world.pointers.heap.memory
    ⟨264,some ⟨256,0⟩⟩ ⟨8,8⟩ = none := by decide

example : (rootRun 3 (some 8) unitShim).world.pointers.heap =
    (NativeAllocatorExecution.allocated (NativeZstBorrow.granted NativeReferenceMachine.empty 64) 8 ⟨3,1⟩).pointers.heap := by decide

example : rootRun 0 (some 0) unusedShim = .returned zeroVecValue NativeReferenceMachine.empty :=
  handled_root_zero _ _ _ _ _ _ _

example : (handledRawErrorMoved NativeReferenceMachine.empty 3 NativeReferenceMachine.empty (.allocationError 3 1)).slots[7]? =
    some (.live (some .uninit)) := by decide

example : (handledRawErrorMoved NativeReferenceMachine.empty 3 NativeReferenceMachine.empty (.allocationError 3 1)).slots[4]? =
    some (.live (some (.record 8 (.choice true (.pair .uninit (.scalar .unit)))))) := by decide

private def outcomeIsUnwind : Flow → Bool
  | .unwind _ => true
  | _ => false

example : outcomeIsUnwind (handledRootInvoke NativeReferenceMachine.empty 256 64 none unitShim .abort .resume 3) = true := by decide
example : outcomeIsUnwind (handledRootInvoke NativeReferenceMachine.empty 256 64 none unusedShim .resume .abort (2^63)) = true := by decide

end HasteBootsVecCapacityArithmetic
