namespace HasteBootsRawVecFields
open FormalProof4FHE.HasteBoots

theorem geometry_exact : sourceSize = 16 ∧ sourceAlignment = 8 ∧ capacityOffset = 0 ∧ pointerOffset = 8 := by decide

theorem capacity_read_step (world next : NativeReferenceMachine.State) (index : Nat) (value : NativeWord64Memory.Word)
    (loaded : capacityRead world index = .value value next) :
    NativeReferenceMachine.execute world (.access index capacityOffset (.read 8 sourceAlignment)) = some next :=
  (NativeRawVecFields.capacity_success world next index value loaded).2.1

theorem pointer_read_step (world next : NativeReferenceMachine.State) (index : Nat) (value : NativePointerStorage.Pointer)
    (loaded : pointerRead world index = .value value next) :
    NativeReferenceMachine.execute world (.access index pointerOffset .loadPointer) = some next :=
  (NativeRawVecFields.pointer_success world next index value loaded).2.1

theorem capacity_checked_bound (world next : NativeReferenceMachine.State) (index : Nat) (value : NativeWord64Memory.Word)
    (loaded : capacityRead world index = .value value next) : value.val < 2^63 :=
  (NativeRawVecFields.capacity_success world next index value loaded).2.2.2

theorem pointer_shadow_origin (world next : NativeReferenceMachine.State) (index : Nat) (value : NativePointerStorage.Pointer)
    (loaded : pointerRead world index = .value value next) :
    ∃ (lease : NativeByteBorrow.Lease) (slot : NativePointerStorage.Pointer) (owner : NativePointerStorage.Origin),
      NativeByteRange.pointerAt lease.pointer pointerOffset = some slot ∧ slot.provenance = some owner ∧
      NativeWord64Memory.load world.pointers.heap.memory slot = some value.address ∧
      NativePointerShadow.uniform world.pointers.heap.shadow owner slot.address.val 8 = some value.provenance := by
  obtain ⟨lease,slot,owner,shifted,origin,address,shadow,_⟩ := NativeRawVecFields.pointer_effect world next index value loaded
  exact ⟨lease,slot,owner,shifted,origin,address,shadow⟩

theorem capacity_failure_prefix (world next : NativeReferenceMachine.State) (index : Nat)
    (failed : capacityRead world index = .invalid next) :
    next = world ∨ NativeReferenceMachine.execute world (.access index capacityOffset (.read 8 sourceAlignment)) = some next :=
  NativeRawVecFields.capacity_failure_prefix world next index failed

theorem pointer_failure_prefix (world next : NativeReferenceMachine.State) (index : Nat)
    (failed : pointerRead world index = .invalid next) :
    next = world ∨ NativeReferenceMachine.execute world (.access index pointerOffset .loadPointer) = some next :=
  NativeRawVecFields.pointer_failure_prefix world next index failed

end HasteBootsRawVecFields
