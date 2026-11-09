namespace HasteBootsReservationErrorKind
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

-- Type identities used by the separate constructor extraction. This exercises
-- nominal relabeling; linking that extraction's source calls remains separate.
private def constructorTags : NativeReservationErrorLocal.Tags := ⟨9,18,4,11,12⟩
private def resident (kind : NativeReservationErrorFields.Kind) : NativeReferenceMachine.State :=
  (NativeReservationErrorLocal.snapshotValue constructorTags NativeReferenceMachine.empty 64
    (NativeReservationErrorLocal.encode constructorTags kind)).world
private def reference : NativeRecordValues.Value := .scalar (.reference false ⟨0⟩ 2)

example (world : NativeReferenceMachine.State) :
    eval (getterBodyFor constructorTags) (materializedFrameFor constructorTags world .capacityOverflow) =
      .returned (NativeReservationErrorLocal.kindValue constructorTags .capacityOverflow) world :=
  getter_overflow_for constructorTags world

example (world : NativeReferenceMachine.State) :
    eval (getterBodyFor constructorTags) (materializedFrameFor constructorTags world (.allocationError 3 8)) =
      .returned (NativeReservationErrorLocal.kindValue constructorTags (.allocationError 3 8)) world :=
  getter_allocation_for constructorTags world 3 8 (by decide)

example : invokeFor constructorTags (resident .capacityOverflow) reference =
    .returned (NativeReservationErrorLocal.kindValue constructorTags .capacityOverflow)
      (NativeReservationErrorFields.wordAccess (resident .capacityOverflow) 0 0).world := by
  rw [invoke_for_equiv]
  rfl

example : invokeFor constructorTags (resident (.allocationError 3 8)) reference =
    .returned (NativeReservationErrorLocal.kindValue constructorTags (.allocationError 3 8))
      (NativeReservationErrorFields.wordAccess
        (NativeReservationErrorFields.wordAccess (resident (.allocationError 3 8)) 0 0).world 0 8).world := by
  rw [invoke_for_equiv]
  rfl

example : NativeByteRange.loadRange (resident .capacityOverflow).pointers.heap.memory
    ⟨72,some ⟨64,0⟩⟩ ⟨8,8⟩ = none := by decide

example : invokeFor constructorTags (resident .capacityOverflow) (.scalar (.reference true ⟨0⟩ 2)) =
    .invalid (resident .capacityOverflow) := by rw [invoke_for_equiv]; rfl

example : invokeFor constructorTags (resident .capacityOverflow) (.scalar (.reference false ⟨0⟩ 0)) =
    .invalid (resident .capacityOverflow) := by rw [invoke_for_equiv]; rfl

example : invokeFor constructorTags (resident .capacityOverflow) (.scalar (.reference false ⟨99⟩ 2)) =
    .invalid (resident .capacityOverflow) := by rw [invoke_for_equiv]; rfl

example (descriptor : NativeReservationErrorLocal.Tags) (world : NativeReferenceMachine.State)
    (value : NativeRecordValues.Value) :
    (invokeFor descriptor world value).world.pointers.heap = world.pointers.heap :=
  invoke_heap_for descriptor world value

end HasteBootsReservationErrorKind
