namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots

example : (NativeRecordValues.get capacityOverflowValue [(.unwrap 8),(.active true),.left] >>=
    NativeReservationErrorLocal.decode reservationErrorTags) = some .capacityOverflow := source_overflow_local_decodes
example : (NativeRecordValues.get (constructorErrorValue 3) [(.unwrap 8),(.active true),.left] >>=
    NativeReservationErrorLocal.decode reservationErrorTags) = some (.allocationError 3 1) :=
  source_allocation_local_decodes 3 (by decide)
example : (NativeRecordValues.get (constructorErrorValue (2^63-1)) [(.unwrap 8),(.active true),.left] >>=
    NativeReservationErrorLocal.decode reservationErrorTags) = some (.allocationError (2^63-1) 1) :=
  source_allocation_local_decodes (2^63-1) (by decide)

end HasteBootsVecCapacityArithmetic
