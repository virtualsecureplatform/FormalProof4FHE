module
public import FormalProof4FHE.HasteBoots.NativeHeapFrame
public import FormalProof4FHE.HasteBoots.NativeHeapRelease
@[expose] public section

/-! Original-heap observations and resident byte-Vec ownership. These checked
model invariants do not establish native construction, ABI or lifetime validity. -/
namespace FormalProof4FHE.HasteBoots.NativeResidentVec
open NativeReferenceMachine (State Reference)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeByteBorrow (Lease)

/-- A successful pointer access reads the original heap through the selected
resident lease, retaining the complete stored provenance. -/
theorem access_pointer_observation (world next : State) (index offset : Nat)
    (executed : NativeReferenceMachine.execute world (.access index offset .loadPointer) = some next) :
    ∃ reference lease slot value,
      world.references[index]? = some reference ∧
      NativeByteBorrow.lookup world.leases reference.tag = some lease ∧
      NativeByteRange.pointerAt lease.pointer offset = some slot ∧
      NativePointerByteMemory.load world.pointers.heap slot = some value ∧
      next.pointers.registers = value :: slot :: world.pointers.registers ∧
      next.pointers.heap = world.pointers.heap := by
  obtain ⟨reference,lease,slot,prepared,selected,registered,_,_,shifted,_,preparation,performed⟩ :=
    NativeReferenceMachine.access_success world next index offset .loadPointer executed
  have preparedEq := (NativeReferenceMachine.prepare_success world lease.pointer slot.address prepared preparation).2
  have provenance := (NativeByteRange.pointerAt_fields lease.pointer offset slot shifted).2
  have scratchEq : (⟨slot.address, lease.pointer.provenance⟩ : Pointer) = slot := by
    rw [← provenance]
  rw [scratchEq] at preparedEq
  subst prepared
  simp only [NativeReferenceMachine.perform, NativePointerMachine.execute,
    NativePointerMachine.push, List.getElem?_cons_zero, Option.bind_some,
    Option.map_eq_some_iff] at performed
  obtain ⟨pointers,⟨value,loaded,same⟩,finished⟩ := performed
  subst pointers
  subst next
  exact ⟨reference,lease,slot,value,selected,registered,shifted,loaded,rfl,rfl⟩

/-- A successful byte access emits exactly the original heap range. -/
theorem access_read_observation (world next : State) (index offset size alignment : Nat)
    (executed : NativeReferenceMachine.execute world (.access index offset (.read size alignment)) = some next) :
    ∃ reference lease slot bytes,
      world.references[index]? = some reference ∧
      NativeByteBorrow.lookup world.leases reference.tag = some lease ∧
      NativeByteRange.pointerAt lease.pointer offset = some slot ∧
      NativeByteRange.loadRange world.pointers.heap.memory slot ⟨size,alignment⟩ = some bytes ∧
      next.outputs = bytes :: world.outputs ∧ next.pointers.heap = world.pointers.heap := by
  obtain ⟨reference,lease,slot,prepared,selected,registered,_,_,shifted,_,preparation,performed⟩ :=
    NativeReferenceMachine.access_success world next index offset (.read size alignment) executed
  have preparedEq := (NativeReferenceMachine.prepare_success world lease.pointer slot.address prepared preparation).2
  subst prepared
  simp only [NativeReferenceMachine.perform, NativePointerMachine.push, Option.map_eq_some_iff] at performed
  obtain ⟨bytes,loaded,finished⟩ := performed
  subst next
  exact ⟨reference,lease,slot,bytes,selected,registered,shifted,loaded,rfl,rfl⟩

theorem access_word_observation (world next : State) (index offset : Nat) (value : Word)
    (executed : NativeReferenceMachine.execute world (.access index offset (.read 8 8)) = some next)
    (decoded : (next.outputs[0]? >>= NativeWord64Memory.decode) = some value) :
    ∃ reference lease slot,
      world.references[index]? = some reference ∧
      NativeByteBorrow.lookup world.leases reference.tag = some lease ∧
      NativeByteRange.pointerAt lease.pointer offset = some slot ∧
      NativeWord64Memory.load world.pointers.heap.memory slot = some value := by
  obtain ⟨reference,lease,slot,bytes,resident,registered,shifted,loaded,outputs,_⟩ :=
    access_read_observation world next index offset 8 8 executed
  rw [outputs, List.getElem?_cons_zero] at decoded
  change NativeWord64Memory.decode bytes = some value at decoded
  exact ⟨reference,lease,slot,resident,registered,shifted,by
    simp only [NativeWord64Memory.load, loaded, Option.bind_some, decoded]⟩

/-- The closed access operation succeeds when its resident permission, source
register and physical pointer load are available. -/
theorem access_pointer_complete (world : State) (index offset : Nat) (reference : Reference)
    (lease : Lease) (slot value : Pointer)
    (resident : world.references[index]? = some reference)
    (registered : NativeByteBorrow.lookup world.leases reference.tag = some lease)
    (bounded : offset + 8 ≤ lease.layout.size)
    (shifted : NativeByteRange.pointerAt lease.pointer offset = some slot)
    (allowed : NativeByteBorrow.throughAllowed (NativeReferenceMachine.ledger world)
      reference.tag .shared slot ⟨8,8⟩ = true)
    (baseResident : world.pointers.registers[world.pointers.registers.idxOf lease.pointer]? = some lease.pointer)
    (loaded : NativePointerByteMemory.load world.pointers.heap slot = some value) :
    ∃ next, NativeReferenceMachine.execute world (.access index offset .loadPointer) = some next ∧
      next.pointers.registers = value :: slot :: world.pointers.registers ∧
      next.pointers.heap = world.pointers.heap := by
  have provenance := (NativeByteRange.pointerAt_fields lease.pointer offset slot shifted).2
  have scratchEq : (⟨slot.address,lease.pointer.provenance⟩ : Pointer) = slot := by rw [← provenance]
  let prepared := NativePointerMachine.push world.pointers slot
  have preparation : NativeReferenceMachine.prepare world lease.pointer slot.address = some prepared := by
    simp only [NativeReferenceMachine.prepare, baseResident, ite_true,
      NativePointerMachine.execute, Option.map_some, scratchEq]
    rfl
  refine ⟨{world with pointers := NativePointerMachine.push prepared value},?_,rfl,rfl⟩
  simp only [NativeReferenceMachine.execute, NativeReferenceMachine.access, resident,
    Option.bind_some, registered, NativeReferenceMachine.Access.mode, NativeReferenceMachine.Access.layout,
    true_or, bounded, and_self, ite_true, shifted, allowed, preparation,
    NativeReferenceMachine.perform, NativePointerMachine.execute, prepared,
    NativePointerMachine.push, List.getElem?_cons_zero, loaded, Option.map_some,
    NativeReferenceMachine.setPointers]

/-- No field values or origins are manufactured from register addresses. -/
structure Descriptor (world : State) (index : Nat) where
  reference : Reference
  lease : Lease
  resident : world.references[index]? = some reference
  registered : NativeByteBorrow.lookup world.leases reference.tag = some lease
  baseResident : world.pointers.registers[world.pointers.registers.idxOf lease.pointer]? = some lease.pointer
  exclusive : lease.mode = .exclusive
  extent : lease.layout = ⟨24,8⟩
  capacitySlot : Pointer
  pointerSlot : Pointer
  lengthSlot : Pointer
  capacityAt : NativeByteRange.pointerAt lease.pointer 0 = some capacitySlot
  pointerAt : NativeByteRange.pointerAt lease.pointer 8 = some pointerSlot
  lengthAt : NativeByteRange.pointerAt lease.pointer 16 = some lengthSlot
  capacity : Word
  length : Word
  buffer : Pointer
  capacityStored : NativeWord64Memory.load world.pointers.heap.memory capacitySlot = some capacity
  pointerStored : NativePointerByteMemory.load world.pointers.heap pointerSlot = some buffer
  lengthStored : NativeWord64Memory.load world.pointers.heap.memory lengthSlot = some length
  capacityBound : capacity.val < 2^63
  lengthBound : length.val ≤ capacity.val
  nonnull : buffer.address.val ≠ 0

/-- Positive capacity owns an exact byte allocation. Zero capacity requires no
allocation for its nonnull dangling buffer. Unused capacity need not be initialized. -/
def OwnsBuffer {world : State} {index : Nat} (descriptor : Descriptor world index) : Prop :=
  descriptor.capacity.val = 0 ∨
    (0 < descriptor.capacity.val ∧ ∃ block ∈ world.pointers.heap.memory.blocks,
      block.pointer = descriptor.buffer ∧ block.layout = ⟨descriptor.capacity.val,1⟩)

/-- The original-heap observation determines every successful pointer field read. -/
theorem Descriptor.pointer_access {world : State} {index : Nat} (descriptor : Descriptor world index)
    (next : State) (value : Pointer)
    (read : NativeRawVecFields.pointerAccess world index = .value value next) : value = descriptor.buffer := by
  cases actual : NativeReferenceMachine.execute world (.access index 8 .loadPointer) with
  | none => simp only [NativeRawVecFields.pointerAccess, actual] at read; cases read
  | some changed =>
    cases found : changed.pointers.registers[0]? with
    | none => simp only [NativeRawVecFields.pointerAccess, actual, found] at read; cases read
    | some pointer =>
      simp only [NativeRawVecFields.pointerAccess, actual, found] at read
      split at read
      · cases read
        obtain ⟨reference,lease,slot,loaded,resident,registered,shifted,stored,registers,_⟩ :=
          access_pointer_observation world next index 8 actual
        have refEq := Option.some.inj (resident.symm.trans descriptor.resident)
        subst reference
        have leaseEq := Option.some.inj (registered.symm.trans descriptor.registered)
        subst lease
        have slotEq := Option.some.inj (shifted.symm.trans descriptor.pointerAt)
        subst slot
        have valueEq := Option.some.inj (stored.symm.trans descriptor.pointerStored)
        rw [registers, List.getElem?_cons_zero] at found
        exact (Option.some.inj found).symm.trans valueEq
      · cases read

theorem Descriptor.pointer_access_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (allowed : NativeByteBorrow.throughAllowed (NativeReferenceMachine.ledger world)
      descriptor.reference.tag .shared descriptor.pointerSlot ⟨8,8⟩ = true) :
    ∃ next, NativeRawVecFields.pointerAccess world index = .value descriptor.buffer next := by
  have bounded : 8 + 8 ≤ descriptor.lease.layout.size := by rw [descriptor.extent]; decide
  obtain ⟨next,actual,registers,_⟩ := access_pointer_complete world index 8 descriptor.reference
    descriptor.lease descriptor.pointerSlot descriptor.buffer descriptor.resident descriptor.registered bounded
    descriptor.pointerAt allowed descriptor.baseResident descriptor.pointerStored
  refine ⟨next,?_⟩
  simp only [NativeRawVecFields.pointerAccess, actual, registers, List.getElem?_cons_zero]
  split
  · rfl
  · rename_i rejected
    exact False.elim (rejected descriptor.nonnull)

/-- The resident field slot uniquely determines an observed word. -/
theorem Descriptor.word_access {world : State} {index : Nat} (descriptor : Descriptor world index)
    (next : State) (offset : Nat) (slot : Pointer) (value stored : Word)
    (shifted : NativeByteRange.pointerAt descriptor.lease.pointer offset = some slot)
    (storedAt : NativeWord64Memory.load world.pointers.heap.memory slot = some stored)
    (executed : NativeReferenceMachine.execute world (.access index offset (.read 8 8)) = some next)
    (decoded : (next.outputs[0]? >>= NativeWord64Memory.decode) = some value) : value = stored := by
  obtain ⟨reference,lease,location,resident,registered,atSlot,observed⟩ :=
    access_word_observation world next index offset value executed decoded
  have refEq := Option.some.inj (resident.symm.trans descriptor.resident)
  subst reference
  have leaseEq := Option.some.inj (registered.symm.trans descriptor.registered)
  subst lease
  have slotEq := Option.some.inj (atSlot.symm.trans shifted)
  subst location
  exact Option.some.inj (observed.symm.trans storedAt)

theorem Descriptor.capacity_access {world : State} {index : Nat} (descriptor : Descriptor world index)
    (next : State) (value : Word)
    (read : NativeRawVecFields.capacityAccess world index = .value value next) : value = descriptor.capacity := by
  cases actual : NativeReferenceMachine.execute world (.access index 0 (.read 8 8)) with
  | none => simp only [NativeRawVecFields.capacityAccess, actual] at read; cases read
  | some changed =>
    cases decoded : changed.outputs[0]? >>= NativeWord64Memory.decode with
    | none => simp only [NativeRawVecFields.capacityAccess, actual, decoded] at read; cases read
    | some word =>
      simp only [NativeRawVecFields.capacityAccess, actual, decoded] at read
      split at read
      · cases read
        exact descriptor.word_access next 0 descriptor.capacitySlot value descriptor.capacity
          descriptor.capacityAt descriptor.capacityStored actual decoded
      · cases read

theorem Descriptor.length_access {world : State} {index : Nat} (descriptor : Descriptor world index)
    (next : State) (value : Word)
    (read : NativeVecReference.lengthAccess world index = .value value next) : value = descriptor.length := by
  cases actual : NativeReferenceMachine.execute world (.access index 16 (.read 8 8)) with
  | none => simp only [NativeVecReference.lengthAccess, actual] at read; cases read
  | some changed =>
    cases decoded : changed.outputs[0]? >>= NativeWord64Memory.decode with
    | none => simp only [NativeVecReference.lengthAccess, actual, decoded] at read; cases read
    | some word =>
      simp only [NativeVecReference.lengthAccess, actual, decoded] at read
      cases read
      exact descriptor.word_access next 16 descriptor.lengthSlot value descriptor.length
        descriptor.lengthAt descriptor.lengthStored actual decoded

theorem Descriptor.zero_capacity_length {world : State} {index : Nat} (descriptor : Descriptor world index)
    (zero : descriptor.capacity.val = 0) : descriptor.length.val = 0 := by
  have bounded := descriptor.lengthBound
  omega

theorem OwnsBuffer.positive_block {world : State} {index : Nat} {descriptor : Descriptor world index}
    (owned : OwnsBuffer descriptor) (positive : 0 < descriptor.capacity.val) :
    ∃ block ∈ world.pointers.heap.memory.blocks,
      block.pointer = descriptor.buffer ∧ block.layout = ⟨descriptor.capacity.val,1⟩ := by
  rcases owned with zero | ⟨_,block⟩
  · omega
  · exact block

theorem OwnsBuffer.positive_origin {world : State} {index : Nat} {descriptor : Descriptor world index}
    (owned : OwnsBuffer descriptor) (positive : 0 < descriptor.capacity.val) :
    ∃ origin, descriptor.buffer.provenance = some origin := by
  obtain ⟨block,_,pointerEq,_⟩ := owned.positive_block positive
  exact ⟨block.origin,by rw [← pointerEq]; rfl⟩

/-- The initialized element prefix is separate from ownership of capacity. -/
def InitializedElements {world : State} {index : Nat} (descriptor : Descriptor world index) : Prop :=
  ∃ bytes, NativeByteRange.loadRange world.pointers.heap.memory descriptor.buffer
    ⟨descriptor.length.val,1⟩ = some bytes

theorem Descriptor.empty_elements_initialized {world : State} {index : Nat} (descriptor : Descriptor world index)
    (empty : descriptor.length.val = 0) : InitializedElements descriptor := by
  refine ⟨[],?_⟩
  rw [empty]
  apply NativeByteRange.empty_range
  refine ⟨by decide,descriptor.nonnull,by simp only [Nat.mod_one],?_⟩
  have bounded := descriptor.buffer.address.isLt
  omega

theorem Descriptor.zero_capacity_initialized {world : State} {index : Nat} (descriptor : Descriptor world index)
    (empty : descriptor.capacity.val = 0) : InitializedElements descriptor :=
  descriptor.empty_elements_initialized (descriptor.zero_capacity_length empty)

theorem Descriptor.read_pointer_field {world : State} {index : Nat} (descriptor : Descriptor world index)
    (input output : NativeSliceLLBC.Value) (register : Nat) (next : State)
    (selected : NativeVecReference.parent world input = some (index,register,descriptor.lease))
    (read : NativeVecReference.readField world input .pointer = .value output next) :
    output = .raw ⟨descriptor.buffer,none⟩ := by
  cases actual : NativeRawVecFields.pointerAccess world index with
  | invalid changed => simp only [NativeVecReference.readField, selected, actual] at read; cases read
  | value pointer changed =>
    have same := descriptor.pointer_access changed pointer actual
    simp only [NativeVecReference.readField, selected, actual] at read
    cases read
    rw [same]

theorem Descriptor.read_length_field {world : State} {index : Nat} (descriptor : Descriptor world index)
    (input output : NativeSliceLLBC.Value) (register : Nat) (next : State)
    (selected : NativeVecReference.parent world input = some (index,register,descriptor.lease))
    (read : NativeVecReference.readField world input .length = .value output next) :
    output = .usize descriptor.length := by
  cases actual : NativeVecReference.lengthAccess world index with
  | invalid changed => simp only [NativeVecReference.readField, selected, actual] at read; cases read
  | value length changed =>
    have same := descriptor.length_access changed length actual
    simp only [NativeVecReference.readField, selected, actual] at read
    cases read
    rw [same]

/-- Membership of the exact base/layout suffices for the primitive release. -/
theorem release_owned_member (blocks : List NativeByteMemory.Block) (block : NativeByteMemory.Block)
    (member : block ∈ blocks) :
    ∃ remaining, NativeByteMemory.releaseBlocks blocks block.pointer block.layout = some remaining := by
  induction blocks with
  | nil => cases member
  | cons head tail ih =>
    by_cases matched : block.pointer = head.pointer ∧ block.layout = head.layout
    · exact ⟨tail,by simp only [NativeByteMemory.releaseBlocks, matched, and_self, ite_true]⟩
    · have inTail : block ∈ tail := by
        rcases List.mem_cons.mp member with same | rest
        · subst head; exact False.elim (matched ⟨rfl,rfl⟩)
        · exact rest
      obtain ⟨remaining,released⟩ := ih inTail
      exact ⟨head :: remaining,by simp only [NativeByteMemory.releaseBlocks, matched, ite_false, released, Option.map_some]⟩

theorem Descriptor.byte_layout_valid {world : State} {index : Nat} (descriptor : Descriptor world index) :
    (NativeByteMemory.Layout.mk descriptor.capacity.val 1).Valid := by
  constructor
  · exact (by decide : 1 ∈ (List.range 64).map (fun exponent => 2^exponent))
  · have bounded := descriptor.capacityBound
    simp only [Nat.sub_self, Nat.add_zero]
    omega

/-- Existence at the byte/shadow allocator boundary, without requiring the
unused capacity bytes to be initialized or readable. -/
theorem OwnsBuffer.deallocation_exists {world : State} {index : Nat} {descriptor : Descriptor world index}
    (owned : OwnsBuffer descriptor) (positive : 0 < descriptor.capacity.val) :
    ∃ after, NativePointerByteMemory.deallocate world.pointers.heap descriptor.buffer
      ⟨descriptor.capacity.val,1⟩ = some after := by
  obtain ⟨block,member,pointerEq,layoutEq⟩ := owned.positive_block positive
  obtain ⟨remaining,released⟩ := release_owned_member world.pointers.heap.memory.blocks block member
  refine ⟨⟨{world.pointers.heap.memory with blocks := remaining},
    world.pointers.heap.shadow.filter (fun cell => decide (cell.owner ≠ block.origin))⟩,?_⟩
  rw [← pointerEq, ← layoutEq]
  have memory : NativeByteMemory.deallocate world.pointers.heap.memory block.pointer block.layout =
      some {world.pointers.heap.memory with blocks := remaining} := by
    simp only [NativeByteMemory.deallocate, released, Option.map_some]
  simp only [NativePointerByteMemory.deallocate, show block.pointer.provenance = some block.origin from rfl,
    Option.bind_eq_bind', Option.bind_some, memory, pure]

theorem OwnsBuffer.deallocation_effect {world : State} {index : Nat} {descriptor : Descriptor world index}
    (owned : OwnsBuffer descriptor) (positive : 0 < descriptor.capacity.val) :
    ∃ after, NativePointerByteMemory.deallocate world.pointers.heap descriptor.buffer
        ⟨descriptor.capacity.val,1⟩ = some after ∧
      NativeHeapRelease.count after + 1 = NativeHeapRelease.count world.pointers.heap ∧
      after.memory.blocks.Sublist world.pointers.heap.memory.blocks ∧
      after.memory.nextGeneration = world.pointers.heap.memory.nextGeneration := by
  obtain ⟨after,freed⟩ := owned.deallocation_exists positive
  have released : NativeHeapRelease.Releases world.pointers.heap after :=
    .free (.refl _) descriptor.buffer ⟨descriptor.capacity.val,1⟩ positive descriptor.byte_layout_valid descriptor.nonnull freed
  exact ⟨after,freed,NativeHeapRelease.deallocate_count _ _ _ _ freed,released.blocks_sublist,released.generation⟩

/-- Freeing the owned data allocation preserves a separately stored descriptor,
including the pointer value that has now become dangling. -/
theorem Descriptor.deallocation_preserves_fields {world : State} {index : Nat} (descriptor : Descriptor world index)
    (after : NativePointerByteMemory.State)
    (separate : descriptor.lease.pointer.provenance ≠ descriptor.buffer.provenance)
    (freed : NativePointerByteMemory.deallocate world.pointers.heap descriptor.buffer
      ⟨descriptor.capacity.val,1⟩ = some after) :
    NativeWord64Memory.load after.memory descriptor.capacitySlot = some descriptor.capacity ∧
    NativePointerByteMemory.load after descriptor.pointerSlot = some descriptor.buffer ∧
    NativeWord64Memory.load after.memory descriptor.lengthSlot = some descriptor.length := by
  have capOrigin := (NativeByteRange.pointerAt_fields _ _ _ descriptor.capacityAt).2
  have ptrOrigin := (NativeByteRange.pointerAt_fields _ _ _ descriptor.pointerAt).2
  have lenOrigin := (NativeByteRange.pointerAt_fields _ _ _ descriptor.lengthAt).2
  have capFrame := NativeHeapRelease.deallocate_range_frame _ _ _ _ freed descriptor.capacitySlot ⟨8,8⟩
    (by rw [capOrigin]; exact separate)
  have ptrFrame := NativeHeapRelease.deallocate_load_frame _ _ _ _ freed descriptor.pointerSlot
    (by rw [ptrOrigin]; exact separate)
  have lenFrame := NativeHeapRelease.deallocate_range_frame _ _ _ _ freed descriptor.lengthSlot ⟨8,8⟩
    (by rw [lenOrigin]; exact separate)
  constructor
  · simpa only [NativeWord64Memory.load, capFrame] using descriptor.capacityStored
  · constructor
    · rw [ptrFrame]; exact descriptor.pointerStored
    · simpa only [NativeWord64Memory.load, lenFrame] using descriptor.lengthStored

theorem Descriptor.deallocation_rejects_elements {world : State} {index : Nat} (descriptor : Descriptor world index)
    (after : NativePointerByteMemory.State) (valid : NativeByteMemory.WellFormed world.pointers.heap.memory)
    (freed : NativePointerByteMemory.deallocate world.pointers.heap descriptor.buffer
      ⟨descriptor.capacity.val,1⟩ = some after)
    (pointer : Pointer) (sameOrigin : pointer.provenance = descriptor.buffer.provenance)
    (view : NativeByteMemory.Layout) (positive : 0 < view.size) :
    NativeByteRange.loadRange after.memory pointer view = none := by
  obtain ⟨_,_,memory,_⟩ := NativePointerByteMemory.deallocate_success _ _ _ _ freed
  exact NativeByteRange.positive_after_deallocation _ valid _ _ _ memory pointer sameOrigin view positive

end FormalProof4FHE.HasteBoots.NativeResidentVec
