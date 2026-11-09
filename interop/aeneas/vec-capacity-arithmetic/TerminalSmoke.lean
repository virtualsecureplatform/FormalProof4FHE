namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

-- This carrier deliberately has no native Arguments representation claim.
private def terminalTestFields : NativeRecordValues.Ty := .scalar .unit
private def terminalTestFormatter (_text : String) (world : NativeReferenceMachine.State) : Flow :=
  .returned (.record 21 (.scalar .unit)) world
private def terminalTestPanic (name : String) (world : NativeReferenceMachine.State) : Flow := .unsupported name world
private def terminalTestLayout : NativeRecordValues.Value := NativeReservationErrorLocal.layoutValue reservationErrorTags 3 8

example : terminalOverflowInvoke terminalTestFields terminalTestFormatter terminalTestPanic NativeReferenceMachine.empty =
    .unsupported "core::panicking::panic_fmt" NativeReferenceMachine.empty := by decide

example : terminalAllocationInvoke terminalTestFields terminalTestFormatter terminalTestPanic NativeReferenceMachine.empty terminalTestLayout =
    .unsupported "core::panicking::panic_fmt" NativeReferenceMachine.empty := by decide

example : terminalOverflowInvoke terminalTestFields (fun text world => .unsupported text world) terminalTestPanic NativeReferenceMachine.empty =
    .unsupported "capacity overflow" NativeReferenceMachine.empty := by decide

example : terminalAllocationInvoke terminalTestFields (fun text world => .unsupported text world) terminalTestPanic NativeReferenceMachine.empty terminalTestLayout =
    .unsupported "allocation failed" NativeReferenceMachine.empty := by decide

example : terminalOverflowInvoke terminalTestFields (fun _ world => .unwind world) terminalTestPanic NativeReferenceMachine.empty =
    .unwind NativeReferenceMachine.empty := by decide

example : terminalAllocationInvoke terminalTestFields (fun _ world => .unwind world) terminalTestPanic NativeReferenceMachine.empty terminalTestLayout =
    .unwind NativeReferenceMachine.empty := by decide

example : terminalAllocationInvoke terminalTestFields terminalTestFormatter (fun _ world => .unwind world) NativeReferenceMachine.empty terminalTestLayout =
    .unwind NativeReferenceMachine.empty := by decide

example : terminalOverflowInvoke terminalTestFields (fun _ world => .returned (.scalar .unit) world) terminalTestPanic NativeReferenceMachine.empty =
    .invalid NativeReferenceMachine.empty := by decide

example : terminalAllocationInvoke terminalTestFields (fun _ world => .returned (.record 22 (.scalar .unit)) world) terminalTestPanic NativeReferenceMachine.empty terminalTestLayout =
    .invalid NativeReferenceMachine.empty := by decide

example : terminalAllocationInvoke terminalTestFields terminalTestFormatter (fun _ world => .returned (.scalar .unit) world) NativeReferenceMachine.empty terminalTestLayout =
    .invalid NativeReferenceMachine.empty := by decide

example : terminalOverflowInvoke terminalTestFields terminalTestFormatter (fun _ world => .normal ⟨[],[],world⟩) NativeReferenceMachine.empty =
    .invalid NativeReferenceMachine.empty := by decide

example : terminalAllocationInvoke terminalTestFields terminalTestFormatter terminalTestPanic NativeReferenceMachine.empty (.scalar .unit) =
    .invalid NativeReferenceMachine.empty := by decide

example : terminalAllocationInvoke terminalTestFields terminalTestFormatter terminalTestPanic NativeReferenceMachine.empty
    (NativeReservationErrorLocal.layoutValue reservationErrorTags 3 3) = .invalid NativeReferenceMachine.empty := by decide

example : terminalAllocationInvoke terminalTestFields
    (fun _ world => .unwind (NativeZstBorrow.granted world 512)) terminalTestPanic NativeReferenceMachine.empty terminalTestLayout =
      .unwind (NativeZstBorrow.granted NativeReferenceMachine.empty 512) := by decide

example : terminalOverflowInvoke terminalTestFields terminalTestFormatter
    (fun _ world => .returned (.scalar .unit) (NativeZstBorrow.granted world 1024)) NativeReferenceMachine.empty =
      .invalid (NativeZstBorrow.granted NativeReferenceMachine.empty 1024) := by decide

end HasteBootsVecCapacityArithmetic
