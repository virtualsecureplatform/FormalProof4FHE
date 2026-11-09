namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots

theorem source_overflow_getter_complete (world next : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (result : NativeRecordValues.Value) (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue reservationErrorTags world base
      ((NativeRecordValues.get capacityOverflowValue [(.unwrap 8),(.active true),.left]).getD .uninit) = .value result next) :
    ∃ final, NativeReservationErrorRead.getKind reservationErrorTags next result =
      .value (NativeReservationErrorLocal.kindValue reservationErrorTags .capacityOverflow) final := by
  change NativeReservationErrorLocal.snapshotValue reservationErrorTags world base
    (NativeReservationErrorLocal.encode reservationErrorTags .capacityOverflow) = .value result next at executed
  exact NativeReservationErrorRead.snapshot_getKind_decoded _ _ _ _ _ _ _ valid (by rfl) executed

theorem source_allocation_getter_complete (capacity : NativeWord64Memory.Word) (bounded : capacity.val < 2^63)
    (world next : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (result : NativeRecordValues.Value) (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue reservationErrorTags world base
      ((NativeRecordValues.get (constructorErrorValue capacity) [(.unwrap 8),(.active true),.left]).getD .uninit) = .value result next) :
    ∃ final, NativeReservationErrorRead.getKind reservationErrorTags next result =
      .value (NativeReservationErrorLocal.kindValue reservationErrorTags (.allocationError capacity 1)) final := by
  change NativeReservationErrorLocal.snapshotValue reservationErrorTags world base
    (NativeReservationErrorLocal.encode reservationErrorTags (.allocationError capacity 1)) = .value result next at executed
  have decoded := source_allocation_local_decodes capacity bounded
  change NativeReservationErrorLocal.decode reservationErrorTags
    (NativeReservationErrorLocal.encode reservationErrorTags (.allocationError capacity 1)) = some (.allocationError capacity 1) at decoded
  exact NativeReservationErrorRead.snapshot_getKind_decoded _ _ _ _ _ _ _ valid decoded executed

end HasteBootsVecCapacityArithmetic
