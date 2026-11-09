namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
private def sourceOverflowResident : NativeReferenceMachine.State :=
  (NativeReservationErrorLocal.snapshotValue reservationErrorTags NativeReferenceMachine.empty 64
    ((NativeRecordValues.get capacityOverflowValue [(.unwrap 8),(.active true),.left]).getD .uninit)).world
private def sourceAllocationResident : NativeReferenceMachine.State :=
  (NativeReservationErrorLocal.snapshotValue reservationErrorTags NativeReferenceMachine.empty 64
    ((NativeRecordValues.get (constructorErrorValue 3) [(.unwrap 8),(.active true),.left]).getD .uninit)).world
example : NativeReservationErrorRead.getKind reservationErrorTags sourceOverflowResident (.scalar (.reference false ⟨0⟩ 2)) =
    .value (NativeReservationErrorLocal.kindValue reservationErrorTags .capacityOverflow)
      (NativeReservationErrorFields.wordAccess sourceOverflowResident 0 0).world := by decide
example : NativeReservationErrorRead.getKind reservationErrorTags sourceAllocationResident (.scalar (.reference false ⟨0⟩ 2)) =
    .value (NativeReservationErrorLocal.kindValue reservationErrorTags (.allocationError 3 1))
      (NativeReservationErrorFields.wordAccess (NativeReservationErrorFields.wordAccess sourceAllocationResident 0 0).world 0 8).world := by decide
end HasteBootsVecCapacityArithmetic
