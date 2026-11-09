module
public import FormalProof4FHE.HasteBoots.NativeVecDestructionCompleteness
@[expose] public section

/-! Serialize the retained empty byte Vec value into a checked modeled header.
Compiler, native aggregate ABI and lifetime correspondence remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeEmptyVecStorage
open NativeReferenceMachine (State)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeByteMemory (Byte)

/-- Capacity, dangling pointer address and length in the retained target layout. -/
def bytes : List Byte := NativeWord64Memory.encode 0 ++ NativeWord64Memory.encode 1 ++ NativeWord64Memory.encode 0

theorem bytes_length : bytes.length = 24 := by decide

theorem subword (memory : NativeByteMemory.State) (valid : NativeByteMemory.WellFormed memory)
    (header : Pointer) (offset : Nat) (word : Word)
    (loaded : NativeByteRange.loadRange memory header ⟨24,8⟩ = some bytes)
    (bounded : offset + 8 ≤ 24) (aligned : offset % 8 = 0)
    (selected : (bytes.drop offset).take 8 = NativeWord64Memory.encode word) :
    ∃ slot, NativeByteRange.pointerAt header offset = some slot ∧ NativeWord64Memory.load memory slot = some word := by
  have original := NativeByteRange.loadRange_geometry memory header ⟨24,8⟩ bytes loaded
  have byteGeometry : NativeByteRange.Geometry header ⟨24,1⟩ :=
    ⟨by decide,original.2.1,by exact Nat.mod_one _,original.2.2.2⟩
  have byteRead : NativeByteRange.loadRange memory header ⟨24,1⟩ = some bytes := by
    simpa only [NativeByteRange.loadRange,original,byteGeometry,ite_true] using loaded
  obtain ⟨slot,shifted,read⟩ := NativeByteRangeCompleteness.loadRange_subrange memory valid header 24 offset 8 bytes byteRead bounded
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

/-- All three stored values follow from the actual byte write, including erased
pointer shadow metadata. No allocation origin is recovered from address bits. -/
theorem written_fields (heap next : NativePointerByteMemory.State) (header : Pointer)
    (valid : NativeByteMemory.WellFormed heap.memory)
    (written : NativePointerByteMemory.writeBytes heap header 8 bytes = some next) :
    ∃ capacitySlot pointerSlot lengthSlot,
      NativeByteRange.pointerAt header 0 = some capacitySlot ∧
      NativeByteRange.pointerAt header 8 = some pointerSlot ∧
      NativeByteRange.pointerAt header 16 = some lengthSlot ∧
      NativeWord64Memory.load next.memory capacitySlot = some 0 ∧
      NativePointerByteMemory.load next pointerSlot = some ⟨1,none⟩ ∧
      NativeWord64Memory.load next.memory lengthSlot = some 0 := by
  obtain ⟨stored,shadow⟩ := NativePointerByteMemory.writeBytes_success heap next header 8 bytes written
  have afterValid := NativeByteRangeWrite.storeRange_wellFormed heap.memory valid header 8 bytes next.memory stored
  have read := NativeByteRangeWrite.storeRange_then_load heap.memory header 8 bytes next.memory stored
  rw [bytes_length] at read
  obtain ⟨capacitySlot,capacityAt,capacityStored⟩ := subword next.memory afterValid header 0 0 read (by decide) (by decide) (by decide)
  obtain ⟨pointerSlot,pointerAt,pointerStored⟩ := subword next.memory afterValid header 8 1 read (by decide) (by decide) (by decide)
  obtain ⟨lengthSlot,lengthAt,lengthStored⟩ := subword next.memory afterValid header 16 0 read (by decide) (by decide) (by decide)
  obtain ⟨block,_,covered,_⟩ := NativeByteRange.loadRange_positive_selected next.memory header ⟨24,8⟩ (by decide) bytes read
  have owner := covered.1
  rw [owner,bytes_length] at shadow
  have pointerOrigin := (NativeByteRange.pointerAt_fields header 8 pointerSlot pointerAt).2
  have pointerAddress := (NativeByteRange.pointerAt_fields header 8 pointerSlot pointerAt).1
  have uniform : NativePointerShadow.uniform next.shadow block.origin pointerSlot.address.val 8 = some none := by
    rw [shadow]
    apply NativePointerShadow.uniform_of_lookup _ _ _ _ (by decide)
    intro index inside
    apply NativePointerShadow.clear_inside
    rw [pointerAddress]
    omega
  refine ⟨capacitySlot,pointerSlot,lengthSlot,capacityAt,pointerAt,lengthAt,capacityStored,?_,lengthStored⟩
  simp only [NativePointerByteMemory.load,pointerOrigin,owner,Option.bind_eq_bind',Option.bind,pointerStored,uniform,pure]

/-- Write the full header, then issue its actual fresh exclusive reference. -/
def install (world : State) (register : Nat) : Option State :=
  NativeReferenceMachine.run world [.raw (.writeBytes register 8 bytes),.borrow register .exclusive ⟨24,8⟩]

/-- An installed empty header, with the actual resident reference and frontier. -/
structure Ready (world : State) where
  descriptor : NativeResidentVec.Descriptor world 0
  capacity_zero : descriptor.capacity = 0
  buffer_dangling : descriptor.buffer = ⟨1,none⟩
  frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease

theorem Ready.initialized {world : State} (ready : Ready world) : NativeResidentVec.InitializedElements ready.descriptor :=
  ready.descriptor.zero_capacity_initialized (congrArg Fin.val ready.capacity_zero)

theorem Ready.owned {world : State} (ready : Ready world) : NativeResidentVec.OwnsBuffer ready.descriptor :=
  Or.inl (congrArg Fin.val ready.capacity_zero)

theorem Ready.available {world : State} (ready : Ready world) :
    NativeVecBytePrefix.Available world ready.descriptor.buffer ready.descriptor.capacity.val := by
  intro lease member overlapping
  have positive := overlapping.1
  rw [ready.capacity_zero] at positive
  exact Nat.not_lt_zero _ positive

/-- Checked live header geometry and physical separation suffice for the actual
write and fresh borrow. Success of either operation is a conclusion. -/
theorem install_complete (world : State) (register : Nat) (header : Pointer)
    (reachable : NativeReferenceMachine.Reachable world)
    (resident : world.pointers.registers[register]? = some header)
    (checked : NativeByteRange.checkRange world.pointers.heap.memory header ⟨24,8⟩ = true)
    (separate : NativeVecBytePrefix.Available world header 24) :
    ∃ next, ∃ ready : Ready next,
      install world register = some next ∧ NativeReferenceMachine.Reachable next ∧
      next.pointers.registers = world.pointers.registers ∧
      next.leases = ready.descriptor.lease :: world.leases ∧
      next.references = ⟨world.nextTag⟩ :: world.references ∧
      ready.descriptor.reference = ⟨world.nextTag⟩ := by
  have valid := NativeReferenceMachine.reachable_wellFormed world reachable
  have allowed : NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger world) .exclusive header ⟨24,8⟩ = true := by
    apply List.all_eq_true.mpr
    intro lease member
    exact decide_eq_true (Or.inr (separate lease member))
  obtain ⟨memory,stored⟩ := NativeByteRangeWrite.storeRange_of_checked world.pointers.heap.memory valid.1.1 header 8 bytes
    (by simpa only [bytes_length] using checked)
  let heap : NativePointerByteMemory.State := ⟨memory, match header.provenance with
    | none => world.pointers.heap.shadow
    | some owner => NativePointerShadow.clear world.pointers.heap.shadow owner header.address.val bytes.length⟩
  have written : NativePointerByteMemory.writeBytes world.pointers.heap header 8 bytes = some heap := by
    simp only [NativePointerByteMemory.writeBytes,stored,Option.bind_eq_bind',Option.bind,pure,heap]
    rfl
  let middle : State := {world with pointers := {world.pointers with heap := heap}}
  have stepWrite : NativeReferenceMachine.execute world (.raw (.writeBytes register 8 bytes)) = some middle := by
    simp only [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,NativeReferenceMachine.rawPermission,
      resident,Option.any_some,bytes_length,allowed,ite_true,NativePointerMachine.execute,written,Option.bind_some,
      Option.map_some,NativePointerMachine.setHeap,NativeReferenceMachine.setPointers,middle]
  have middleReachable := NativeReferenceMachine.Reachable.step reachable _ stepWrite
  have read := NativeByteRangeWrite.storeRange_then_load world.pointers.heap.memory header 8 bytes memory stored
  rw [bytes_length] at read
  let lease : NativeByteBorrow.Lease := ⟨world.nextTag,none,header,⟨24,8⟩,.exclusive⟩
  let next : State := ⟨middle.pointers,world.nextTag + 1,lease :: world.leases,
    ⟨world.nextTag⟩ :: world.references,lease :: world.births,world.outputs⟩
  have borrowed : NativeReferenceMachine.execute middle (.borrow register .exclusive ⟨24,8⟩) = some next := by
    simp only [NativeReferenceMachine.execute,middle,resident,Option.bind_some,NativeReferenceMachine.grant,
      NativeByteBorrow.borrow,NativeByteBorrow.parentAllowed]
    change (if NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger world) .exclusive header ⟨24,8⟩ then
      (NativeByteRange.loadRange memory header ⟨24,8⟩).map _ else none).map _ = some next
    rw [allowed]
    change ((NativeByteRange.loadRange memory header ⟨24,8⟩).map _).map _ = some next
    rw [read]
    rfl
  have nextReachable := NativeReferenceMachine.Reachable.step middleReachable _ borrowed
  obtain ⟨capacitySlot,pointerSlot,lengthSlot,capacityAt,pointerAt,lengthAt,capacityStored,pointerStored,lengthStored⟩ :=
    written_fields world.pointers.heap heap header valid.1.1 written
  have registered : NativeByteBorrow.lookup next.leases world.nextTag = some lease := by
    simp only [next,NativeByteBorrow.lookup,lease,ite_true]
  have baseResident : next.pointers.registers[next.pointers.registers.idxOf header]? = some header :=
    List.getElem?_idxOf (List.mem_of_getElem? resident)
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
    capacity := 0
    length := 0
    buffer := ⟨1,none⟩
    capacityStored := capacityStored
    pointerStored := pointerStored
    lengthStored := lengthStored
    capacityBound := by decide
    lengthBound := by decide
    nonnull := by decide }
  have frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger next) lease := by
    refine ⟨rfl,registered,?_⟩
    intro other member
    change other ∈ lease :: world.leases at member
    rcases List.mem_cons.mp member with same | old
    · exact Or.inl (congrArg NativeByteBorrow.Lease.tag same)
    · exact Or.inr (Or.inr (separate other old))
  let ready : Ready next := ⟨descriptor,rfl,rfl,frontier⟩
  refine ⟨next,ready,?_,nextReachable,rfl,rfl,rfl,rfl⟩
  simp only [install,NativeReferenceMachine.run,stepWrite,Option.bind_some,borrowed]

end FormalProof4FHE.HasteBoots.NativeEmptyVecStorage
