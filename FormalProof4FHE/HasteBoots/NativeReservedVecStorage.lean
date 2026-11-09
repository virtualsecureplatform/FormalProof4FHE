module
public import FormalProof4FHE.HasteBoots.NativePointerRestore
@[expose] public section

/-! Reservation headers retain their complete typed buffer pointer. The payload
may be entirely uninitialized because the stored element length is zero.
Native allocator, constructor, compiler and lifetime correspondence remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeReservedVecStorage
open NativeReferenceMachine (State)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeByteMemory (Byte)

def bytes (capacity : Word) (buffer : Pointer) : List Byte :=
  NativeWord64Memory.encode capacity ++ NativeWord64Memory.encode buffer.address ++ NativeWord64Memory.encode 0

theorem bytes_length (capacity : Word) (buffer : Pointer) : (bytes capacity buffer).length = 24 := by
  simp only [bytes,List.length_append,NativeWord64Memory.encode_length]

theorem subword (memory : NativeByteMemory.State) (valid : NativeByteMemory.WellFormed memory)
    (header : Pointer) (capacity : Word) (buffer : Pointer) (offset : Nat) (word : Word)
    (loaded : NativeByteRange.loadRange memory header ⟨24,8⟩ = some (bytes capacity buffer))
    (bounded : offset + 8 ≤ 24) (aligned : offset % 8 = 0)
    (selected : ((bytes capacity buffer).drop offset).take 8 = NativeWord64Memory.encode word) :
    ∃ slot, NativeByteRange.pointerAt header offset = some slot ∧ NativeWord64Memory.load memory slot = some word := by
  have original := NativeByteRange.loadRange_geometry memory header ⟨24,8⟩ _ loaded
  have byteGeometry : NativeByteRange.Geometry header ⟨24,1⟩ :=
    ⟨by decide,original.2.1,by exact Nat.mod_one _,original.2.2.2⟩
  have byteRead : NativeByteRange.loadRange memory header ⟨24,1⟩ = some (bytes capacity buffer) := by
    simpa only [NativeByteRange.loadRange,original,byteGeometry,ite_true] using loaded
  obtain ⟨slot,shifted,read⟩ := NativeByteRangeCompleteness.loadRange_subrange memory valid header 24 offset 8 _ byteRead bounded
  have address := (NativeByteRange.pointerAt_fields header offset slot shifted).1
  have subGeometry := NativeByteRange.loadRange_geometry memory slot ⟨8,1⟩ _ read
  have wordGeometry : NativeByteRange.Geometry slot ⟨8,8⟩ := by
    refine ⟨by decide,subGeometry.2.1,?_,subGeometry.2.2.2⟩
    change slot.address.val % 8 = 0
    rw [address,Nat.add_mod,original.2.2.1,aligned]
  have wordRead : NativeByteRange.loadRange memory slot ⟨8,8⟩ = some (NativeWord64Memory.encode word) := by
    rw [selected] at read
    simpa only [NativeByteRange.loadRange,wordGeometry,subGeometry,ite_true] using read
  exact ⟨slot,shifted,by simp only [NativeWord64Memory.load,wordRead,Option.bind_some,NativeWord64Memory.decode_encode]⟩

/-- Write address bytes, then restore the source pointer's complete provenance. -/
def write (heap : NativePointerByteMemory.State) (header : Pointer) (capacity : Word) (buffer : Pointer) :
    Option NativePointerByteMemory.State := do
  let slot ← NativeByteRange.pointerAt header 8
  let middle ← NativePointerByteMemory.writeBytes heap header 8 (bytes capacity buffer)
  NativePointerByteMemory.store middle slot buffer

/-- The typed pointer store preserves the full byte write exactly, including the
capacity and zero length, while retaining the source allocation origin. -/
theorem write_complete (heap : NativePointerByteMemory.State) (header : Pointer) (capacity : Word) (buffer : Pointer)
    (valid : NativeByteMemory.WellFormed heap.memory)
    (checked : NativeByteRange.checkRange heap.memory header ⟨24,8⟩ = true) :
    ∃ middle next capacitySlot pointerSlot lengthSlot,
      NativePointerByteMemory.writeBytes heap header 8 (bytes capacity buffer) = some middle ∧
      NativePointerByteMemory.store middle pointerSlot buffer = some next ∧ write heap header capacity buffer = some next ∧
      NativeByteRange.pointerAt header 0 = some capacitySlot ∧ NativeByteRange.pointerAt header 8 = some pointerSlot ∧
      NativeByteRange.pointerAt header 16 = some lengthSlot ∧
      NativeWord64Memory.load next.memory capacitySlot = some capacity ∧
      NativePointerByteMemory.load next pointerSlot = some buffer ∧
      NativeWord64Memory.load next.memory lengthSlot = some 0 ∧
      NativeByteRange.loadRange next.memory header ⟨24,8⟩ = some (bytes capacity buffer) ∧
      next.memory = middle.memory ∧ next.memory.blocks.map NativeByteMemory.shape = heap.memory.blocks.map NativeByteMemory.shape := by
  obtain ⟨memory,stored⟩ := NativeByteRangeWrite.storeRange_of_checked heap.memory valid header 8 (bytes capacity buffer)
    (by simpa only [bytes_length] using checked)
  let middle : NativePointerByteMemory.State := ⟨memory,match header.provenance with
    | none => heap.shadow
    | some owner => NativePointerShadow.clear heap.shadow owner header.address.val (bytes capacity buffer).length⟩
  have written : NativePointerByteMemory.writeBytes heap header 8 (bytes capacity buffer) = some middle := by
    simp only [NativePointerByteMemory.writeBytes,stored,Option.bind_eq_bind',Option.bind,pure,middle]
    rfl
  have afterValid := NativeByteRangeWrite.storeRange_wellFormed heap.memory valid header 8 _ memory stored
  have read := NativeByteRangeWrite.storeRange_then_load heap.memory header 8 _ memory stored
  rw [bytes_length] at read
  obtain ⟨capacitySlot,capacityAt,capacityStored⟩ := subword memory afterValid header capacity buffer 0 capacity read (by decide) (by decide) (by
    simp [bytes,NativeWord64Memory.encode_length])
  obtain ⟨pointerSlot,pointerAt,pointerAddress⟩ := subword memory afterValid header capacity buffer 8 buffer.address read (by decide) (by decide) (by
    simp [bytes,NativeWord64Memory.encode_length])
  obtain ⟨lengthSlot,lengthAt,lengthStored⟩ := subword memory afterValid header capacity buffer 16 0 read (by decide) (by decide) (by
    have first : (bytes capacity buffer).drop 8 = NativeWord64Memory.encode buffer.address ++ NativeWord64Memory.encode 0 := by
      simpa only [bytes,List.append_assoc,NativeWord64Memory.encode_length] using
        (show (NativeWord64Memory.encode capacity ++ (NativeWord64Memory.encode buffer.address ++ NativeWord64Memory.encode 0)).drop (NativeWord64Memory.encode capacity).length = _ from List.drop_left)
    have second : (NativeWord64Memory.encode buffer.address ++ NativeWord64Memory.encode 0).drop 8 = NativeWord64Memory.encode 0 := by
      simpa only [NativeWord64Memory.encode_length] using
        (show (NativeWord64Memory.encode buffer.address ++ NativeWord64Memory.encode 0).drop (NativeWord64Memory.encode buffer.address).length = _ from List.drop_left)
    have full : (bytes capacity buffer).drop 16 = NativeWord64Memory.encode 0 := by
      change (bytes capacity buffer).drop (8+8) = _
      rw [← List.drop_drop,first,second]
    rw [full]
    simpa only [NativeWord64Memory.encode_length] using (show (NativeWord64Memory.encode 0).take (NativeWord64Memory.encode 0).length = _ from List.take_length))
  obtain ⟨block,_,covered,_⟩ := NativeByteRange.loadRange_positive_selected memory header ⟨24,8⟩ (by decide) _ read
  have owner := (NativeByteRange.pointerAt_fields header 8 pointerSlot pointerAt).2.trans covered.1
  obtain ⟨next,restored,same,pointerStored,_⟩ := NativePointerRestore.restore middle pointerSlot buffer block.origin owner pointerAddress
  refine ⟨middle,next,capacitySlot,pointerSlot,lengthSlot,written,restored,?_,capacityAt,pointerAt,lengthAt,?_,pointerStored,?_,?_,same,?_⟩
  · simp only [write,pointerAt,written,Option.bind_eq_bind',Option.bind,restored]
  · rw [same]; exact capacityStored
  · rw [same]; exact lengthStored
  · rw [same]; exact read
  · rw [same]
    exact (NativeByteRangeWrite.storeRange_success heap.memory header 8 _ memory stored).2.2

/-- All pointer values used by the typed store are selected from actual machine
registers. The temporary slot register is the sole new pointer register. -/
def install (world : State) (headerRegister bufferRegister : Nat) (capacity : Word) : Option State := do
  let header ← world.pointers.registers[headerRegister]?
  let buffer ← world.pointers.registers[bufferRegister]?
  let slot ← NativeByteRange.pointerAt header 8
  NativeReferenceMachine.run world
    [.raw (.writeBytes headerRegister 8 (bytes capacity buffer)),.raw (.withAddress headerRegister slot.address),
      .raw (.store 0 (bufferRegister + 1)),.borrow (headerRegister + 1) .exclusive ⟨24,8⟩]

structure Ready (world : State) (capacity : Word) (buffer header : Pointer) where
  descriptor : NativeResidentVec.Descriptor world 0
  capacity_eq : descriptor.capacity = capacity
  length_zero : descriptor.length = 0
  buffer_eq : descriptor.buffer = buffer
  header_eq : descriptor.lease.pointer = header
  frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease

theorem Ready.initialized {world : State} {capacity : Word} {buffer header : Pointer}
    (ready : Ready world capacity buffer header) : NativeResidentVec.InitializedElements ready.descriptor :=
  ready.descriptor.empty_elements_initialized (congrArg Fin.val ready.length_zero)

/-- Store arbitrary bounded reservation capacity and the registered complete
buffer pointer, then derive the actual resident exclusive descriptor. -/
theorem install_complete (world : State) (headerRegister bufferRegister : Nat) (capacity : Word) (buffer header : Pointer)
    (reachable : NativeReferenceMachine.Reachable world)
    (headerResident : world.pointers.registers[headerRegister]? = some header)
    (bufferResident : world.pointers.registers[bufferRegister]? = some buffer)
    (checked : NativeByteRange.checkRange world.pointers.heap.memory header ⟨24,8⟩ = true)
    (separate : NativeVecBytePrefix.Available world header 24)
    (capacityBound : capacity.val < 2^63) (nonnull : buffer.address.val ≠ 0) :
    ∃ next, ∃ ready : Ready next capacity buffer header,
      install world headerRegister bufferRegister capacity = some next ∧ NativeReferenceMachine.Reachable next ∧
      next.pointers.registers = ready.descriptor.pointerSlot :: world.pointers.registers ∧
      next.leases = ready.descriptor.lease :: world.leases ∧
      next.references = ⟨world.nextTag⟩ :: world.references ∧ ready.descriptor.reference = ⟨world.nextTag⟩ ∧
      next.pointers.heap.memory.blocks.map NativeByteMemory.shape = world.pointers.heap.memory.blocks.map NativeByteMemory.shape := by
  have valid := NativeReferenceMachine.reachable_wellFormed world reachable
  obtain ⟨middleHeap,finalHeap,capacitySlot,pointerSlot,lengthSlot,written,restored,_,capacityAt,pointerAt,lengthAt,
      capacityStored,pointerStored,lengthStored,headerRead,_,shapes⟩ :=
    write_complete world.pointers.heap header capacity buffer valid.1.1 checked
  have allowedHeader : NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger world) .exclusive header ⟨24,8⟩ = true := by
    apply List.all_eq_true.mpr
    intro lease member
    exact decide_eq_true (Or.inr (separate lease member))
  have address := (NativeByteRange.pointerAt_fields header 8 pointerSlot pointerAt).1
  have origin := (NativeByteRange.pointerAt_fields header 8 pointerSlot pointerAt).2
  have separateSlot : ∀ lease ∈ world.leases, ¬ NativeByteBorrow.Overlap pointerSlot ⟨8,8⟩ lease.pointer lease.layout := by
    intro lease member
    apply NativeBorrowFrontier.disjoint_subrange ⟨0,none,header,⟨24,8⟩,.exclusive⟩ lease pointerSlot ⟨8,8⟩
    · refine ⟨origin,?_,?_⟩ <;> dsimp only at * <;> omega
    · exact separate lease member
  have allowedSlot : NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger world) .exclusive pointerSlot ⟨8,8⟩ = true := by
    apply List.all_eq_true.mpr
    intro lease member
    exact decide_eq_true (Or.inr (separateSlot lease member))
  let middle : State := {world with pointers := {world.pointers with heap := middleHeap}}
  have writeStep : NativeReferenceMachine.execute world (.raw (.writeBytes headerRegister 8 (bytes capacity buffer))) = some middle := by
    simp only [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,NativeReferenceMachine.rawPermission,
      headerResident,Option.any_some,bytes_length,allowedHeader,ite_true,NativePointerMachine.execute,written,Option.bind_some,
      Option.map_some,NativePointerMachine.setHeap,NativeReferenceMachine.setPointers,middle]
  let shifted : State := {middle with pointers := NativePointerMachine.push middle.pointers pointerSlot}
  have shiftStep : NativeReferenceMachine.execute middle (.raw (.withAddress headerRegister pointerSlot.address)) = some shifted := by
    have same : (⟨pointerSlot.address,header.provenance⟩ : Pointer) = pointerSlot := by rw [← origin]
    simp only [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,ite_true,NativePointerMachine.execute,
      middle,headerResident,Option.map_some,same,NativeReferenceMachine.setPointers,shifted]
  let stored : State := {shifted with pointers := {shifted.pointers with heap := finalHeap}}
  have storeStep : NativeReferenceMachine.execute shifted (.raw (.store 0 (bufferRegister + 1))) = some stored := by
    have permission : NativeReferenceMachine.rawPermissions shifted (.store 0 (bufferRegister + 1)) = true := by
      change NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger world) .exclusive pointerSlot ⟨8,8⟩ = true
      exact allowedSlot
    change (if NativeReferenceMachine.rawPermissions shifted (.store 0 (bufferRegister + 1)) then
      (NativePointerMachine.execute shifted.pointers (.store 0 (bufferRegister + 1))).map
        (NativeReferenceMachine.setPointers shifted) else none) = some stored
    rw [permission]
    change (NativePointerMachine.execute shifted.pointers (.store 0 (bufferRegister + 1))).map
      (NativeReferenceMachine.setPointers shifted) = some stored
    simp only [NativePointerMachine.execute,shifted,NativePointerMachine.push,
      List.getElem?_cons_zero,List.getElem?_cons_succ,middle,bufferResident,restored,Option.bind_some,Option.map_some,
      NativePointerMachine.setHeap,NativeReferenceMachine.setPointers,stored]
  let lease : NativeByteBorrow.Lease := ⟨world.nextTag,none,header,⟨24,8⟩,.exclusive⟩
  let next : State := ⟨stored.pointers,world.nextTag + 1,lease :: world.leases,
    ⟨world.nextTag⟩ :: world.references,lease :: world.births,world.outputs⟩
  have borrowed : NativeReferenceMachine.execute stored (.borrow (headerRegister + 1) .exclusive ⟨24,8⟩) = some next := by
    simp only [NativeReferenceMachine.execute,stored,shifted,middle,NativePointerMachine.push,List.getElem?_cons_succ,
      headerResident,Option.bind_some,NativeReferenceMachine.grant,NativeByteBorrow.borrow,NativeByteBorrow.parentAllowed]
    change (if NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger world) .exclusive header ⟨24,8⟩ then
      (NativeByteRange.loadRange finalHeap.memory header ⟨24,8⟩).map _ else none).map _ = some next
    rw [allowedHeader]
    change ((NativeByteRange.loadRange finalHeap.memory header ⟨24,8⟩).map _).map _ = some next
    rw [headerRead]
    rfl
  have reached := NativeReferenceMachine.Reachable.step
    (NativeReferenceMachine.Reachable.step (NativeReferenceMachine.Reachable.step
      (NativeReferenceMachine.Reachable.step reachable _ writeStep) _ shiftStep) _ storeStep) _ borrowed
  have registered : NativeByteBorrow.lookup next.leases world.nextTag = some lease := by
    simp only [next,NativeByteBorrow.lookup,lease,ite_true]
  have baseResident : next.pointers.registers[next.pointers.registers.idxOf header]? = some header :=
    List.getElem?_idxOf (List.mem_cons_of_mem _ (List.mem_of_getElem? headerResident))
  let descriptor : NativeResidentVec.Descriptor next 0 := {
    reference := ⟨world.nextTag⟩
    lease := lease
    resident := rfl
    registered := registered
    baseResident := baseResident
    exclusive := rfl
    extent := rfl
    capacitySlot := capacitySlot
    pointerSlot := pointerSlot
    lengthSlot := lengthSlot
    capacityAt := capacityAt
    pointerAt := pointerAt
    lengthAt := lengthAt
    capacity := capacity
    length := 0
    buffer := buffer
    capacityStored := capacityStored
    pointerStored := pointerStored
    lengthStored := lengthStored
    capacityBound := capacityBound
    lengthBound := Nat.zero_le _
    nonnull := nonnull }
  have frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger next) lease := by
    refine ⟨rfl,registered,?_⟩
    intro other member
    change other ∈ lease :: world.leases at member
    rcases List.mem_cons.mp member with same | old
    · exact Or.inl (congrArg NativeByteBorrow.Lease.tag same)
    · exact Or.inr (Or.inr (separate other old))
  let ready : Ready next capacity buffer header := ⟨descriptor,rfl,rfl,rfl,rfl,frontier⟩
  refine ⟨next,ready,?_,reached,rfl,rfl,rfl,rfl,shapes⟩
  simp only [install,headerResident,bufferResident,pointerAt,Option.bind_eq_bind',Option.bind,
    NativeReferenceMachine.run,writeStep,shiftStep,storeStep,borrowed]

/-- Byte initialization preserves each allocation's identity, base and extent. -/
theorem owned_of_shapes (before after : NativeByteMemory.State) (capacity : Word) (buffer : Pointer)
    (shapes : after.blocks.map NativeByteMemory.shape = before.blocks.map NativeByteMemory.shape)
    (owned : ∃ block ∈ before.blocks, block.pointer = buffer ∧ block.layout = ⟨capacity.val,1⟩) :
    ∃ block ∈ after.blocks, block.pointer = buffer ∧ block.layout = ⟨capacity.val,1⟩ := by
  obtain ⟨block,member,pointer,layout⟩ := owned
  have mapped : NativeByteMemory.shape block ∈ after.blocks.map NativeByteMemory.shape := by
    rw [shapes]
    exact List.mem_map_of_mem member
  obtain ⟨next,present,same⟩ := List.mem_map.mp mapped
  exact ⟨next,present,(congrArg NativeByteMemory.Block.pointer same).trans pointer,
    (congrArg NativeByteMemory.Block.layout same).trans layout⟩

theorem Ready.owned {world : State} {capacity : Word} {buffer header : Pointer}
    (ready : Ready world capacity buffer header) (before : NativeByteMemory.State)
    (positive : 0 < capacity.val)
    (shapes : world.pointers.heap.memory.blocks.map NativeByteMemory.shape = before.blocks.map NativeByteMemory.shape)
    (owned : ∃ block ∈ before.blocks, block.pointer = buffer ∧ block.layout = ⟨capacity.val,1⟩) :
    NativeResidentVec.OwnsBuffer ready.descriptor := by
  right
  rw [ready.capacity_eq,ready.buffer_eq]
  exact ⟨positive,owned_of_shapes before world.pointers.heap.memory capacity buffer shapes owned⟩

theorem Ready.available {world : State} {capacity : Word} {buffer header : Pointer}
    (ready : Ready world capacity buffer header) (before : State)
    (loans : world.leases = ready.descriptor.lease :: before.leases)
    (available : NativeVecBytePrefix.Available before buffer capacity.val)
    (headerSeparate : ¬ NativeByteBorrow.Overlap buffer ⟨capacity.val,1⟩ header ⟨24,8⟩) :
    NativeVecBytePrefix.Available world ready.descriptor.buffer ready.descriptor.capacity.val := by
  intro lease member
  rw [ready.capacity_eq,ready.buffer_eq]
  rw [loans] at member
  rcases List.mem_cons.mp member with same | old
  · subst lease
    rw [ready.header_eq,ready.descriptor.extent]
    exact headerSeparate
  · exact available lease old

end FormalProof4FHE.HasteBoots.NativeReservedVecStorage
