namespace HasteBootsReservationErrorKind
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
example (world : NativeReferenceMachine.State) : eval getterBody (materializedFrame world .capacityOverflow) =
    .returned (NativeReservationErrorLocal.kindValue tags .capacityOverflow) world := getter_overflow world
example (world : NativeReferenceMachine.State) : eval getterBody (materializedFrame world (.allocationError 3 8)) =
    .returned (NativeReservationErrorLocal.kindValue tags (.allocationError 3 8)) world := getter_allocation world 3 8 (by decide)
example (world : NativeReferenceMachine.State) : eval getterBody (materializedFrame world (.allocationError (2^63-1) 1)) =
    .returned (NativeReservationErrorLocal.kindValue tags (.allocationError (2^63-1) 1)) world := getter_allocation world _ 1 (by decide)
private def ready (kind : NativeReservationErrorFields.Kind) : NativeReferenceMachine.State :=
  (NativeReservationErrorLocal.snapshotValue tags NativeReferenceMachine.empty 64 (NativeReservationErrorLocal.encode tags kind)).world
private def operand : NativeRecordValues.Value := .scalar (.reference false ⟨0⟩ 2)
example : invoke (ready .capacityOverflow) operand = .returned (NativeReservationErrorLocal.kindValue tags .capacityOverflow)
    (NativeReservationErrorFields.wordAccess (ready .capacityOverflow) 0 0).world := by
  rw [getter_equiv]
  rfl
example : invoke (ready (.allocationError 3 8)) operand = .returned (NativeReservationErrorLocal.kindValue tags (.allocationError 3 8))
    (NativeReservationErrorFields.wordAccess (NativeReservationErrorFields.wordAccess (ready (.allocationError 3 8)) 0 0).world 0 8).world := by
  rw [getter_equiv]
  rfl
example : NativeByteRange.loadRange (ready .capacityOverflow).pointers.heap.memory ⟨72,some ⟨64,0⟩⟩ ⟨8,8⟩ = none := by decide
example : invoke (ready .capacityOverflow) (.scalar (.reference true ⟨0⟩ 2)) = .invalid (ready .capacityOverflow) := by rw [getter_equiv]; rfl
example : invoke (ready .capacityOverflow) (.scalar (.reference false ⟨0⟩ 0)) = .invalid (ready .capacityOverflow) := by rw [getter_equiv]; rfl
example : invoke (ready .capacityOverflow) (.scalar (.reference false ⟨99⟩ 2)) = .invalid (ready .capacityOverflow) := by rw [getter_equiv]; rfl
example (world : NativeReferenceMachine.State) (value : NativeRecordValues.Value) :
    (invoke world value).world.pointers.heap = world.pointers.heap := invoke_heap world value
end HasteBootsReservationErrorKind
