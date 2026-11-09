namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def terminalRootTestFields : NativeRecordValues.Ty := .scalar .unit
private def terminalRootTestFormatter (_text : String) (world : NativeReferenceMachine.State) : Flow :=
  .returned (.record 21 (.scalar .unit)) world
private def terminalRootTestPanic (name : String) (world : NativeReferenceMachine.State) : Flow := .unsupported name world
private def terminalRootUnitShim : NativeAllocatorLLBC.Body := .legacy (.live 0 (.assign 0 .unit .ret)) .done
private def terminalRootUnusedShim : NativeAllocatorLLBC.Body := .legacy (.unsupported "unexpected shim") .done
private def terminalRootLabel : Flow → Option String
  | .unsupported source _ => some source
  | _ => none
private def terminalRootUnwound : Flow → Bool
  | .unwind _ => true
  | _ => false
private def terminalRootInvalid : Flow → Bool
  | .invalid _ => true
  | _ => false

example : terminalRootLabel (terminalRootInvoke terminalRootTestFields terminalRootTestFormatter terminalRootTestPanic
    NativeReferenceMachine.empty 256 64 none terminalRootUnitShim 3) = some "core::panicking::panic_fmt" := by decide

example : terminalRootLabel (terminalRootInvoke terminalRootTestFields terminalRootTestFormatter terminalRootTestPanic
    NativeReferenceMachine.empty 256 64 (some 8) terminalRootUnusedShim (2^63)) = some "core::panicking::panic_fmt" := by decide

example : terminalRootLabel (terminalRootInvoke terminalRootTestFields (fun text world => .unsupported text world) terminalRootTestPanic
    NativeReferenceMachine.empty 256 64 none terminalRootUnitShim 3) = some "allocation failed" := by decide

example : terminalRootLabel (terminalRootInvoke terminalRootTestFields (fun text world => .unsupported text world) terminalRootTestPanic
    NativeReferenceMachine.empty 256 64 none terminalRootUnusedShim (2^64-1)) = some "capacity overflow" := by decide

example : terminalRootUnwound (terminalRootInvoke terminalRootTestFields (fun _ world => .unwind world) terminalRootTestPanic
    NativeReferenceMachine.empty 256 64 none terminalRootUnitShim 3) = true := by decide

example : terminalRootUnwound (terminalRootInvoke terminalRootTestFields terminalRootTestFormatter (fun _ world => .unwind world)
    NativeReferenceMachine.empty 256 64 none terminalRootUnusedShim (2^63)) = true := by decide

example : terminalRootInvalid (terminalRootInvoke terminalRootTestFields (fun _ world => .returned (.scalar .unit) world) terminalRootTestPanic
    NativeReferenceMachine.empty 256 64 none terminalRootUnitShim 3) = true := by decide

example : (terminalRootInvoke terminalRootTestFields (fun _ world => .returned (.scalar .unit) world) terminalRootTestPanic
    NativeReferenceMachine.empty 256 64 none terminalRootUnitShim 3).world.nextTag = 3 := by decide

example : (terminalRootInvoke terminalRootTestFields (fun _ world => .unwind (NativeZstBorrow.granted world 512)) terminalRootTestPanic
    NativeReferenceMachine.empty 256 64 none terminalRootUnitShim 3).world.nextTag = 4 := by decide

example : (terminalRootInvoke terminalRootTestFields terminalRootTestFormatter
    (fun _ world => .returned (.scalar .unit) (NativeZstBorrow.granted world 1024))
    NativeReferenceMachine.empty 256 64 none terminalRootUnitShim 3).world.nextTag = 4 := by decide

example : NativeByteRange.loadRange
    (terminalRootInvoke terminalRootTestFields terminalRootTestFormatter terminalRootTestPanic
      NativeReferenceMachine.empty 256 64 none terminalRootUnusedShim (2^63)).world.pointers.heap.memory
      ⟨264,some ⟨256,0⟩⟩ ⟨8,8⟩ = none := by decide

example : terminalRootInvoke terminalRootTestFields terminalRootTestFormatter terminalRootTestPanic
    NativeReferenceMachine.empty 0 0 (some 0) terminalRootUnusedShim 0 = .returned zeroVecValue NativeReferenceMachine.empty :=
  terminal_root_zero _ _ _ _ _ _ _ _

example : (terminalRootInvoke terminalRootTestFields terminalRootTestFormatter terminalRootTestPanic
    NativeReferenceMachine.empty 256 64 (some 8) terminalRootUnitShim 3).world.pointers.heap =
      (NativeAllocatorExecution.allocated (NativeZstBorrow.granted NativeReferenceMachine.empty 64) 8 ⟨3,1⟩).pointers.heap := by decide

example : terminalRootInvalid (terminalRootInvoke terminalRootTestFields terminalRootTestFormatter terminalRootTestPanic
    NativeReferenceMachine.empty 3 64 none terminalRootUnitShim 3) = true := by decide

example : (terminalRootInvoke terminalRootTestFields terminalRootTestFormatter terminalRootTestPanic
    NativeReferenceMachine.empty 3 64 none terminalRootUnitShim 3).world.nextTag = 2 := by decide

example (world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (valid : NativeReferenceMachine.WellFormed world) :
    NativeReferenceMachine.WellFormed (terminalRootInvoke terminalRootTestFields terminalRootTestFormatter terminalRootTestPanic
      world 256 64 none terminalRootUnitShim capacity).world := by
  exact terminal_root_wellFormed _ _ _ (fun _ _ => .refl _) (fun _ _ => .refl _) _ _ _ _ _ _ valid

end HasteBootsVecCapacityArithmetic
