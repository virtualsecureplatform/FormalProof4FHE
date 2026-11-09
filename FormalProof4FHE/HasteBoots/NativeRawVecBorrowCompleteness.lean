module
public import FormalProof4FHE.HasteBoots.NativeBorrowFrontier
public import FormalProof4FHE.HasteBoots.NativeRawVecMutBorrow
public import FormalProof4FHE.HasteBoots.NativeResidentVecBorrow
@[expose] public section

/-! Completion of the retained RawVec reservation and activation operations.
Resident identities, initialized fields and the alias frontier are explicit.
Native Rust lifetimes and the destructor's subsequent calls remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeRawVecBorrowCompleteness
open NativeReferenceMachine (State Reference)
open NativeByteBorrow (Lease)
open NativeBorrowFrontier

/-- Reservation prepares the existing base address without minting a loan. -/
def prepared (world : State) (lease : Lease) : State :=
  {world with pointers := NativePointerMachine.push world.pointers lease.pointer}

/-- Both retained Vec borrow targets complete from the stored fields and alias
frontier, preserving the original resident fields in their issued operands. -/
theorem vec_reborrow_complete (world : State) (index : Nat)
    (descriptor : NativeResidentVec.Descriptor world index)
    (valid : NativeByteBorrow.WellFormed (NativeReferenceMachine.ledger world))
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease)
    (target : NativeVecReference.Target) :
    ∃ next, NativeVecReference.reborrow world (.reference true descriptor.reference 3) target =
        .value (.reference true ⟨world.nextTag⟩ target.count) next ∧
      ExclusiveFrontier (NativeReferenceMachine.ledger next)
        ⟨world.nextTag,some descriptor.lease.tag,descriptor.lease.pointer,target.layout,.exclusive⟩ ∧
      NativeResidentVecBorrow.Resident next (.reference true ⟨world.nextTag⟩ target.count)
        descriptor.lease.pointer descriptor.capacity descriptor.length descriptor.buffer := by
  have referenceResident := List.mem_of_getElem? descriptor.resident
  have pointerResident := List.mem_of_getElem? descriptor.baseResident
  have selected : NativeVecReference.parent world (.reference true descriptor.reference 3) =
      some (world.references.idxOf descriptor.reference,
        world.pointers.registers.idxOf descriptor.lease.pointer,descriptor.lease) := by
    simp only [NativeVecReference.parent,ne_eq,not_true_eq_false,ite_false,descriptor.registered,
      Option.bind_eq_bind',Option.bind_some,descriptor.exclusive,descriptor.extent,
      List.getElem?_idxOf referenceResident,List.getElem?_idxOf pointerResident,and_self,ite_true]
  have address : NativeReferenceMachine.execute world
      (.raw (.withAddress (world.pointers.registers.idxOf descriptor.lease.pointer) descriptor.lease.pointer.address)) =
      some (prepared world descriptor.lease) := by
    simp only [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,ite_true,
      NativePointerMachine.execute,List.getElem?_idxOf pointerResident,Option.map_some,
      NativeReferenceMachine.setPointers,prepared,NativePointerMachine.push]
  have contained : Contained descriptor.lease.pointer target.layout descriptor.lease := by
    rw [Contained,descriptor.extent]
    refine ⟨rfl,Nat.le_refl _,?_⟩
    cases target <;> simp only [NativeVecReference.Target.layout] <;> omega
  have loaded : ∃ bytes, NativeByteRange.loadRange world.pointers.heap.memory
      descriptor.lease.pointer target.layout = some bytes := by
    cases target with
    | whole => exact descriptor.header_initialized valid.1
    | rawVec => exact descriptor.rawvec_initialized valid.1
  obtain ⟨bytes,initialized⟩ := loaded
  obtain ⟨next,issued,available⟩ := grant_initialized (prepared world descriptor.lease) valid
    descriptor.lease frontier _ _ bytes contained initialized
  have tag := (NativeByteBorrow.lookup_selected _ _ _ descriptor.registered).2
  have actual : NativeReferenceMachine.execute (prepared world descriptor.lease)
      (.reborrow (world.references.idxOf descriptor.reference) 0 .exclusive target.layout) = some next := by
    simp only [NativeReferenceMachine.execute,prepared,NativePointerMachine.push,
      List.getElem?_idxOf referenceResident,List.getElem?_cons_zero,Option.bind_some]
    simpa only [tag,prepared,NativePointerMachine.push] using issued
  have offset : target.offset = 0 := by cases target <;> rfl
  have borrowed : NativeVecReference.reborrow world (.reference true descriptor.reference 3) target =
      .value (.reference true ⟨world.nextTag⟩ target.count) next := by
    simp only [NativeVecReference.reborrow,selected,offset,NativeResidentVecBorrow.pointerAt_zero,address,actual]
    rfl
  exact ⟨next,borrowed,available,NativeResidentVecBorrow.vec_reborrow
    (NativeResidentVecBorrow.descriptor_resident descriptor) target borrowed⟩

theorem reserve_complete (world : State) (reference : Reference) (lease : Lease)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger world))
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) lease)
    (tag : reference.tag = lease.tag) (shape : lease.layout = ⟨16,8⟩)
    (referenceResident : reference ∈ world.references) (pointerResident : lease.pointer ∈ world.pointers.registers) :
    NativeRawVecMutBorrow.reserve world (.reference true reference 2) =
      .value ⟨reference,lease.pointer⟩ (prepared world lease) := by
  have registered : NativeByteBorrow.lookup world.leases lease.tag = some lease := frontier.2.1
  have selected : NativeRawVecBorrow.parent world (.reference true reference 2) =
      some (world.references.idxOf reference,world.pointers.registers.idxOf lease.pointer,lease) := by
    simp only [NativeRawVecBorrow.parent,ne_eq,not_true_eq_false,ite_false,tag,registered,
      Option.bind_eq_bind',Option.bind_some,frontier.1,NativeSliceLLBC.mode,shape,
      List.getElem?_idxOf referenceResident,List.getElem?_idxOf pointerResident,and_self,ite_true]
  have address : NativeReferenceMachine.execute world
      (.raw (.withAddress (world.pointers.registers.idxOf lease.pointer) lease.pointer.address)) =
      some (prepared world lease) := by
    simp only [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,ite_true,
      NativePointerMachine.execute,List.getElem?_idxOf pointerResident,Option.map_some,
      NativeReferenceMachine.setPointers,prepared,NativePointerMachine.push]
  have contained : Contained lease.pointer ⟨16,8⟩ lease := by
    rw [Contained,shape]
    exact ⟨rfl,Nat.le_refl _,Nat.le_refl _⟩
  have allowed := parent_allowed (NativeReferenceMachine.ledger world) valid lease frontier
    .shared lease.pointer ⟨16,8⟩ contained
  have permitted : NativeByteBorrow.parentAllowed (NativeReferenceMachine.ledger (prepared world lease))
      (some reference.tag) .shared lease.pointer ⟨16,8⟩ = true := by
    simpa only [prepared,NativePointerMachine.push,NativeReferenceMachine.ledger,tag] using allowed
  simp only [NativeRawVecMutBorrow.reserve,selected,address,permitted,ite_true]

theorem activate_complete (world : State) (reference : Reference) (lease : Lease)
    (valid : NativeByteBorrow.WellFormed (NativeReferenceMachine.ledger world))
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) lease)
    (tag : reference.tag = lease.tag) (shape : lease.layout = ⟨16,8⟩)
    (referenceResident : reference ∈ world.references)
    (bytes : List NativeByteMemory.Byte)
    (initialized : NativeByteRange.loadRange world.pointers.heap.memory lease.pointer ⟨16,8⟩ = some bytes) :
    ∃ next, NativeRawVecMutBorrow.activate (prepared world lease) ⟨reference,lease.pointer⟩ =
        .value (.reference true ⟨world.nextTag⟩ 2) next ∧
      ExclusiveFrontier (NativeReferenceMachine.ledger next)
        ⟨world.nextTag,some lease.tag,lease.pointer,⟨16,8⟩,.exclusive⟩ := by
  have contained : Contained lease.pointer ⟨16,8⟩ lease := by
    rw [Contained,shape]
    exact ⟨rfl,Nat.le_refl _,Nat.le_refl _⟩
  obtain ⟨next,issued,available⟩ := grant_initialized (prepared world lease) valid lease frontier
    lease.pointer ⟨16,8⟩ bytes contained initialized
  have referenceSelected : (prepared world lease).references[(prepared world lease).references.idxOf reference]? =
      some reference := List.getElem?_idxOf referenceResident
  have pointerSelected : (prepared world lease).pointers.registers[
      (prepared world lease).pointers.registers.idxOf lease.pointer]? = some lease.pointer :=
    List.getElem?_idxOf (List.mem_cons_self ..)
  have actual : NativeReferenceMachine.execute (prepared world lease)
      (.reborrow ((prepared world lease).references.idxOf reference)
        ((prepared world lease).pointers.registers.idxOf lease.pointer) .exclusive ⟨16,8⟩) = some next := by
    simp only [NativeReferenceMachine.execute,referenceSelected,pointerSelected,Option.bind_some,tag]
    exact issued
  refine ⟨next,?_,available⟩
  simp only [NativeRawVecMutBorrow.activate,referenceSelected,pointerSelected,and_self,ite_true,actual]
  rfl

theorem immediate_complete (world : State) (reference : Reference) (lease : Lease)
    (valid : NativeByteBorrow.WellFormed (NativeReferenceMachine.ledger world))
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) lease)
    (tag : reference.tag = lease.tag) (shape : lease.layout = ⟨16,8⟩)
    (referenceResident : reference ∈ world.references) (pointerResident : lease.pointer ∈ world.pointers.registers)
    (bytes : List NativeByteMemory.Byte)
    (initialized : NativeByteRange.loadRange world.pointers.heap.memory lease.pointer ⟨16,8⟩ = some bytes) :
    ∃ next, NativeRawVecMutBorrow.immediate world (.reference true reference 2) =
        .value (.reference true ⟨world.nextTag⟩ 2) next ∧
      ExclusiveFrontier (NativeReferenceMachine.ledger next)
        ⟨world.nextTag,some lease.tag,lease.pointer,⟨16,8⟩,.exclusive⟩ := by
  obtain ⟨next,activated,available⟩ := activate_complete world reference lease valid frontier tag shape
    referenceResident bytes initialized
  exact ⟨next,by rw [NativeRawVecMutBorrow.immediate,
    reserve_complete world reference lease valid.2 frontier tag shape referenceResident pointerResident]; exact activated,available⟩

/-- The Vec field borrow feeds the actual RawVec reservation and activation.
No successful intermediate operation is a hypothesis. -/
theorem vec_rawvec_activation_complete (world : State) (index : Nat)
    (descriptor : NativeResidentVec.Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world)
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    ∃ entered next, NativeVecReference.reborrow world (.reference true descriptor.reference 3) .rawVec =
        .value (.reference true ⟨world.nextTag⟩ 2) entered ∧
      NativeRawVecMutBorrow.immediate entered (.reference true ⟨world.nextTag⟩ 2) =
        .value (.reference true ⟨entered.nextTag⟩ 2) next ∧
      NativeResidentVecBorrow.Resident next (.reference true ⟨entered.nextTag⟩ 2)
        descriptor.lease.pointer descriptor.capacity descriptor.length descriptor.buffer ∧
      ExclusiveFrontier (NativeReferenceMachine.ledger next)
        ⟨entered.nextTag,some world.nextTag,descriptor.lease.pointer,⟨16,8⟩,.exclusive⟩ ∧
      NativeReferenceMachine.Reachable next ∧ next.pointers.heap = world.pointers.heap := by
  have valid := NativeReferenceMachine.reachable_wellFormed world reachable
  obtain ⟨entered,borrowed,available,resident⟩ := vec_reborrow_complete world index descriptor
    ⟨valid.1.1,valid.2.1⟩ frontier .rawVec
  have nextReach := NativeVecReference.reborrow_reachable world (.reference true descriptor.reference 3) .rawVec reachable
  rw [borrowed] at nextReach
  have nextValid := NativeReferenceMachine.reachable_wellFormed entered nextReach
  have heap := NativeVecReference.reborrow_preserves_heap world entered _ _ .rawVec borrowed
  obtain ⟨bytes,loaded⟩ := descriptor.rawvec_initialized valid.1.1
  have initialized : NativeByteRange.loadRange entered.pointers.heap.memory descriptor.lease.pointer
      ⟨16,8⟩ = some bytes := by rw [heap]; exact loaded
  obtain ⟨mutable,reference,count,lease,valueEq,member,registered,baseEq,mode,shape,present,contents⟩ := resident
  cases valueEq
  have leaseEq : lease = ⟨world.nextTag,some descriptor.lease.tag,descriptor.lease.pointer,⟨16,8⟩,.exclusive⟩ :=
    Option.some.inj (registered.symm.trans available.2.1)
  subst lease
  obtain ⟨next,activated,finalAvailable⟩ := immediate_complete entered ⟨world.nextTag⟩
    ⟨world.nextTag,some descriptor.lease.tag,descriptor.lease.pointer,⟨16,8⟩,.exclusive⟩
    ⟨nextValid.1.1,nextValid.2.1⟩ available rfl rfl member present bytes initialized
  have initialResident := NativeResidentVecBorrow.vec_reborrow
    (NativeResidentVecBorrow.descriptor_resident descriptor) .rawVec borrowed
  have finalReach := NativeSliceLLBC.reference_runs_reachable entered _ nextReach
    (NativeRawVecMutBorrow.immediate_projects entered (.reference true ⟨world.nextTag⟩ 2))
  rw [activated] at finalReach
  have finalHeap := (NativeRawVecMutBorrow.immediate_heap_projects entered
    (.reference true ⟨world.nextTag⟩ 2)).heap_eq
  rw [activated] at finalHeap
  exact ⟨entered,next,borrowed,activated,
    NativeResidentVecBorrow.rawvec_immediate initialResident activated,finalAvailable,
    finalReach,finalHeap.trans heap⟩

end FormalProof4FHE.HasteBoots.NativeRawVecBorrowCompleteness
