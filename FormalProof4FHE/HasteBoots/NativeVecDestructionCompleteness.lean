module
public import FormalProof4FHE.HasteBoots.NativeRawVecDeallocationCompleteness
public import FormalProof4FHE.HasteBoots.NativeRecordIncomingReference
@[expose] public section

/-! Resident Vec descriptors carried through the actual destructor borrows.
Field initialization and logical alias permissions are derived separately from
ownership of the data buffer. Native construction and compiler refinement remain
separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeVecDestructionCompleteness
open NativeReferenceMachine (State Reference)
open NativeResidentVec (Descriptor)
open NativeBorrowFrontier (ExclusiveFrontier)

/-- Re-index the same original descriptor after a checked heap and loan frame. -/
def reframe {world : State} {index : Nat} (descriptor : Descriptor world index) (after : State)
    (heap : after.pointers.heap = world.pointers.heap)
    (registered : NativeByteBorrow.lookup after.leases descriptor.reference.tag = some descriptor.lease)
    (referenceResident : descriptor.reference ∈ after.references)
    (pointerResident : descriptor.lease.pointer ∈ after.pointers.registers) :
    Descriptor after (after.references.idxOf descriptor.reference) where
  reference := descriptor.reference
  lease := descriptor.lease
  resident := List.getElem?_idxOf referenceResident
  registered := registered
  baseResident := List.getElem?_idxOf pointerResident
  exclusive := descriptor.exclusive
  extent := descriptor.extent
  capacitySlot := descriptor.capacitySlot
  pointerSlot := descriptor.pointerSlot
  lengthSlot := descriptor.lengthSlot
  capacityAt := descriptor.capacityAt
  pointerAt := descriptor.pointerAt
  lengthAt := descriptor.lengthAt
  capacity := descriptor.capacity
  length := descriptor.length
  buffer := descriptor.buffer
  capacityStored := by rw [heap]; exact descriptor.capacityStored
  pointerStored := by rw [heap]; exact descriptor.pointerStored
  lengthStored := by rw [heap]; exact descriptor.lengthStored
  capacityBound := descriptor.capacityBound
  lengthBound := descriptor.lengthBound
  nonnull := descriptor.nonnull

theorem reborrow_extends (world : State) (value : NativeSliceLLBC.Value) (target : NativeVecReference.Target) :
    NativeScopeRestoration.Extends world (NativeVecReference.reborrow world value target).world := by
  cases selected : NativeVecReference.parent world value with
  | none => simp only [NativeVecReference.reborrow,selected,NativeRawVecFields.Result.world]; exact .refl _
  | some entry =>
    rcases entry with ⟨index,register,lease⟩
    cases shifted : NativeByteRange.pointerAt lease.pointer target.offset with
    | none => simp only [NativeVecReference.reborrow,selected,shifted,NativeRawVecFields.Result.world]; exact .refl _
    | some pointer =>
      cases address : NativeReferenceMachine.execute world (.raw (.withAddress register pointer.address)) with
      | none => simp only [NativeVecReference.reborrow,selected,shifted,address,NativeRawVecFields.Result.world]; exact .refl _
      | some prepared =>
        have first := NativeScopeRestoration.step world prepared _ address
        cases issued : NativeReferenceMachine.execute prepared (.reborrow index 0 .exclusive target.layout) with
        | none => simpa only [NativeVecReference.reborrow,selected,shifted,address,issued,NativeRawVecFields.Result.world] using first
        | some next =>
          have second := NativeScopeRestoration.step prepared next _ issued
          simpa only [NativeVecReference.reborrow,selected,shifted,address,issued,NativeRawVecFields.Result.world] using first.trans second

theorem available_reborrow (before after : State) (pointer : NativePointerStorage.Pointer) (size : Nat)
    (value output : NativeSliceLLBC.Value) (target : NativeVecReference.Target)
    (available : NativeVecBytePrefix.Available before pointer size)
    (borrowed : NativeVecReference.reborrow before value target = .value output after) :
    NativeVecBytePrefix.Available after pointer size := by
  obtain ⟨index,register,lease,childPointer,prepared,_,_,address,issued,_⟩ :=
    NativeVecReference.reborrow_success before after value output target borrowed
  have same : prepared.leases = before.leases := by
    simp [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,
      NativePointerMachine.execute,Option.map_map] at address
    obtain ⟨stored,_,same⟩ := address
    cases same
    rfl
  have ready := NativeRawVecDeallocationCompleteness.available_same_loans before prepared pointer size available same
  simp only [NativeReferenceMachine.execute,Option.bind_eq_some_iff] at issued
  obtain ⟨reference,_,stored,_,granted⟩ := issued
  exact NativeRawVecDeallocationCompleteness.available_grant prepared after pointer size reference.tag .exclusive stored target.layout ready granted

/-- The whole-object borrow constructs the byte callee's full descriptor from
its original stored fields and the actual minted reference. -/
theorem whole_descriptor_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world)
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    ∃ next, ∃ after : Descriptor next (next.references.idxOf ⟨world.nextTag⟩),
      NativeVecReference.reborrow world (.reference true descriptor.reference 3) .whole =
        .value (.reference true after.reference 3) next ∧
      after.capacity = descriptor.capacity ∧ after.length = descriptor.length ∧ after.buffer = descriptor.buffer ∧
      NativeReferenceMachine.Reachable next ∧ ExclusiveFrontier (NativeReferenceMachine.ledger next) after.lease ∧
      next.pointers.heap = world.pointers.heap := by
  have valid := NativeReferenceMachine.reachable_wellFormed world reachable
  obtain ⟨next,borrowed,available,resident⟩ := NativeRawVecBorrowCompleteness.vec_reborrow_complete world index descriptor
    ⟨valid.1.1,valid.2.1⟩ frontier .whole
  have reached := NativeVecReference.reborrow_reachable world (.reference true descriptor.reference 3) .whole reachable
  rw [borrowed] at reached
  have heap := NativeVecReference.reborrow_preserves_heap world next _ _ .whole borrowed
  obtain ⟨mutable,reference,count,lease,valueEq,member,registered,baseEq,mode,shape,present,contents⟩ := resident
  cases valueEq
  have leaseEq : lease = ⟨world.nextTag,some descriptor.lease.tag,descriptor.lease.pointer,⟨24,8⟩,.exclusive⟩ :=
    Option.some.inj (registered.symm.trans available.2.1)
  subst lease
  let after : Descriptor next (next.references.idxOf ⟨world.nextTag⟩) := {
    reference := ⟨world.nextTag⟩
    lease := ⟨world.nextTag,some descriptor.lease.tag,descriptor.lease.pointer,⟨24,8⟩,.exclusive⟩
    resident := List.getElem?_idxOf member
    registered := registered
    baseResident := List.getElem?_idxOf present
    exclusive := rfl
    extent := rfl
    capacitySlot := descriptor.capacitySlot
    pointerSlot := descriptor.pointerSlot
    lengthSlot := descriptor.lengthSlot
    capacityAt := descriptor.capacityAt
    pointerAt := descriptor.pointerAt
    lengthAt := descriptor.lengthAt
    capacity := descriptor.capacity
    length := descriptor.length
    buffer := descriptor.buffer
    capacityStored := by rw [heap]; exact descriptor.capacityStored
    pointerStored := by rw [heap]; exact descriptor.pointerStored
    lengthStored := by rw [heap]; exact descriptor.lengthStored
    capacityBound := descriptor.capacityBound
    lengthBound := descriptor.lengthBound
    nonnull := descriptor.nonnull }
  exact ⟨next,after,borrowed,rfl,rfl,rfl,reached,available,heap⟩

/-- The RawVec field borrow constructs the proven destructor's readiness
conditions, deriving its initialized header from the resident Vec fields. -/
theorem rawvec_ready_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world)
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    ∃ next, NativeVecReference.reborrow world (.reference true descriptor.reference 3) .rawVec =
        .value (.reference true ⟨world.nextTag⟩ 2) next ∧
      Nonempty (NativeRawVecDeallocationCompleteness.Ready next ⟨world.nextTag⟩ descriptor.capacity descriptor.length descriptor.buffer) ∧
      next.pointers.heap = world.pointers.heap := by
  have valid := NativeReferenceMachine.reachable_wellFormed world reachable
  obtain ⟨next,borrowed,available,resident⟩ := NativeRawVecBorrowCompleteness.vec_reborrow_complete world index descriptor
    ⟨valid.1.1,valid.2.1⟩ frontier .rawVec
  have reached := NativeVecReference.reborrow_reachable world (.reference true descriptor.reference 3) .rawVec reachable
  rw [borrowed] at reached
  have heap := NativeVecReference.reborrow_preserves_heap world next _ _ .rawVec borrowed
  obtain ⟨mutable,reference,count,lease,valueEq,member,registered,baseEq,mode,shape,present,contents⟩ := resident
  cases valueEq
  have leaseEq : lease = ⟨world.nextTag,some descriptor.lease.tag,descriptor.lease.pointer,⟨16,8⟩,.exclusive⟩ :=
    Option.some.inj (registered.symm.trans available.2.1)
  subst lease
  have initialized : ∃ bytes, NativeByteRange.loadRange next.pointers.heap.memory descriptor.lease.pointer ⟨16,8⟩ = some bytes := by
    rw [heap]
    exact descriptor.rawvec_initialized valid.1.1
  exact ⟨next,borrowed,⟨⟨_,reached,available,rfl,rfl,member,present,contents,initialized⟩⟩,heap⟩

end FormalProof4FHE.HasteBoots.NativeVecDestructionCompleteness
