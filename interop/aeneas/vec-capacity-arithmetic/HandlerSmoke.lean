namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

private def overflowTerminal : Body := .unsupported "overflow terminal"
private def allocationTerminal : Body := .switchUsize (.copy 1 [(.unwrap 4),.left]) 3
  (.unsupported "allocation size 3") (.unsupported "wrong allocation size") .abort
private def runHandler (kind : NativeReservationErrorFields.Kind) : Flow :=
  handlerInvoke NativeReferenceMachine.empty 64 overflowTerminal allocationTerminal
    (NativeReservationErrorLocal.encode reservationErrorTags kind)
private def stored (kind : NativeReservationErrorFields.Kind) : NativeReferenceMachine.State :=
  (NativeReservationErrorLocal.snapshotValue reservationErrorTags NativeReferenceMachine.empty 64
    (NativeReservationErrorLocal.encode reservationErrorTags kind)).world

example : runHandler .capacityOverflow = .unsupported "overflow terminal"
    (NativeReservationErrorFields.wordAccess (stored .capacityOverflow) 0 0).world := by decide

example : runHandler (.allocationError 3 8) = .unsupported "allocation size 3"
    (NativeReservationErrorFields.wordAccess
      (NativeReservationErrorFields.wordAccess (stored (.allocationError 3 8)) 0 0).world 0 8).world := by decide

example : runHandler (.allocationError 4 8) = .unsupported "wrong allocation size"
    (NativeReservationErrorFields.wordAccess
      (NativeReservationErrorFields.wordAccess (stored (.allocationError 4 8)) 0 0).world 0 8).world := by decide

example : NativeByteRange.loadRange (runHandler .capacityOverflow).world.pointers.heap.memory
    ⟨72,some ⟨64,0⟩⟩ ⟨8,8⟩ = none := by decide

example : (runHandler (.allocationError 3 8)).world.leases = (stored (.allocationError 3 8)).leases := by decide

example : handlerInvoke NativeReferenceMachine.empty 64 overflowTerminal allocationTerminal (.scalar .unit) =
    .invalid NativeReferenceMachine.empty := by decide

example : runHandler (.allocationError 3 0) = .invalid NativeReferenceMachine.empty := by decide

example : handlerInvoke NativeReferenceMachine.empty 3 overflowTerminal allocationTerminal
    (NativeReservationErrorLocal.encode reservationErrorTags .capacityOverflow) =
      .invalid NativeReferenceMachine.empty := by decide

-- Terminal bodies are model parameters. These examples exercise source cleanup
-- and Never-return rejection without asserting native panic/abort behavior.
example : handlerInvoke NativeReferenceMachine.empty 64 .resume .abort
    (NativeReservationErrorLocal.encode reservationErrorTags .capacityOverflow) =
      .unwind (NativeReservationErrorFields.wordAccess (stored .capacityOverflow) 0 0).world := by decide

example : handlerInvoke NativeReferenceMachine.empty 64 .abort .resume
    (NativeReservationErrorLocal.encode reservationErrorTags (.allocationError 3 8)) =
      .unwind (NativeReservationErrorFields.wordAccess
        (NativeReservationErrorFields.wordAccess (stored (.allocationError 3 8)) 0 0).world 0 8).world := by decide

example : handlerInvoke NativeReferenceMachine.empty 64 (.live 0 (.assign 0 .unit .ret)) .abort
    (NativeReservationErrorLocal.encode reservationErrorTags .capacityOverflow) =
      .invalid (NativeReservationErrorFields.wordAccess (stored .capacityOverflow) 0 0).world := by decide

example (value : NativeRecordValues.Value) : NativeRecordValues.fits handlerNeverType value = false :=
  handler_never_fits value

end HasteBootsVecCapacityArithmetic
