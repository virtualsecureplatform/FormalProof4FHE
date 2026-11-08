namespace HasteBootsScalarPointerBody
open FormalProof4FHE.HasteBoots
open NativeScalarLLBC
open NativePointerStorage (Pointer)

theorem raw_store_pointer_source (state next : NativeReferenceMachine.State) (slotIndex valueIndex : Nat)
    (slot value : Pointer) (selectedSlot : state.pointers.registers[slotIndex]? = some slot)
    (selectedValue : state.pointers.registers[valueIndex]? = some value)
    (executed : NativeReferenceMachine.execute state (.raw (.store slotIndex valueIndex)) = some next) :
    invoke f4 state.pointers.heap [.pointer slot, .pointer value] = .returned .unit next.pointers.heap ∧
      NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger state) .exclusive slot ⟨8, 8⟩ = true := by
  obtain ⟨allowed, actual⟩ := NativeReferenceMachine.raw_success state next (.store slotIndex valueIndex) executed
  have permission := NativeReferenceMachine.raw_permission_selected state slotIndex slot .exclusive ⟨8, 8⟩ selectedSlot allowed
  simp only [NativePointerMachine.execute, selectedSlot, selectedValue, Option.bind_some, Option.map_eq_some_iff] at actual
  obtain ⟨heap, stored, same⟩ := actual
  constructor
  · rw [write_pointer_wrapper, write_pointer_body, stored]
    exact congrArg (Outcome.returned .unit) (congrArg NativePointerMachine.State.heap same)
  · exact permission

theorem raw_load_pointer_source (state next : NativeReferenceMachine.State) (slotIndex : Nat) (slot : Pointer)
    (selectedSlot : state.pointers.registers[slotIndex]? = some slot)
    (executed : NativeReferenceMachine.execute state (.raw (.load slotIndex)) = some next) :
    ∃ value, invoke f3 state.pointers.heap [.pointer slot] = .returned (.pointer value) state.pointers.heap ∧
      next.pointers.registers[0]? = some value ∧ next.pointers.heap = state.pointers.heap ∧
      NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger state) .shared slot ⟨8, 8⟩ = true := by
  obtain ⟨allowed, actual⟩ := NativeReferenceMachine.raw_success state next (.load slotIndex) executed
  have permission := NativeReferenceMachine.raw_permission_selected state slotIndex slot .shared ⟨8, 8⟩ selectedSlot allowed
  simp only [NativePointerMachine.execute, selectedSlot, Option.bind_some, Option.map_eq_some_iff] at actual
  obtain ⟨value, loaded, same⟩ := actual
  refine ⟨value, ?_, ?_, ?_, permission⟩
  · rw [read_pointer_wrapper, read_pointer_body, loaded]
  · rw [← same]; rfl
  · rw [← same]; rfl

end HasteBootsScalarPointerBody
