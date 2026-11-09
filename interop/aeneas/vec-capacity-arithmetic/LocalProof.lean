namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots

theorem source_overflow_local_encoding :
    NativeRecordValues.get capacityOverflowValue [(.unwrap 8),(.active true),.left] =
      some (NativeReservationErrorLocal.encode reservationErrorTags .capacityOverflow) := rfl

theorem source_allocation_local_encoding (capacity : NativeWord64Memory.Word) :
    NativeRecordValues.get (constructorErrorValue capacity) [(.unwrap 8),(.active true),.left] =
      some (NativeReservationErrorLocal.encode reservationErrorTags (.allocationError capacity 1)) := rfl

theorem source_overflow_local_decodes :
    (NativeRecordValues.get capacityOverflowValue [(.unwrap 8),(.active true),.left] >>=
      NativeReservationErrorLocal.decode reservationErrorTags) = some .capacityOverflow := rfl

theorem source_allocation_local_decodes (capacity : NativeWord64Memory.Word) (bounded : capacity.val < 2^63) :
    (NativeRecordValues.get (constructorErrorValue capacity) [(.unwrap 8),(.active true),.left] >>=
      NativeReservationErrorLocal.decode reservationErrorTags) = some (.allocationError capacity 1) := by
  have valid : NativeReservationErrorLocal.Valid (.allocationError capacity 1) := by
    refine ⟨by decide,⟨?_,?_⟩⟩
    · change 1 ∈ (List.range 64).map (fun exponent => 2 ^ exponent)
      decide
    · change capacity.val + (1-1) ≤ 2^63-1
      omega
  rw [source_allocation_local_encoding]
  change NativeReservationErrorLocal.decode reservationErrorTags
    (NativeReservationErrorLocal.encode reservationErrorTags (.allocationError capacity 1)) = _
  rw [NativeReservationErrorLocal.decode_encode,ite_eq_left valid]

end HasteBootsVecCapacityArithmetic
