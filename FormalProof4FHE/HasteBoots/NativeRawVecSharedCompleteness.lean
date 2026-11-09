module
public import FormalProof4FHE.HasteBoots.NativeRawVecBorrowCompleteness
@[expose] public section

/-! Shared RawVec header loans and their checked read permissions.
The alias condition keeps ancestors resident and other overlapping loans absent.
Native Rust lifetime correspondence remains a separate obligation. -/
namespace FormalProof4FHE.HasteBoots.NativeRawVecSharedCompleteness
open NativeByteBorrow (State Lease ParentPath LedgerValid)
open NativePointerStorage (Pointer)
open NativeByteMemory (Layout)
open NativeBorrowFrontier

/-- A shared child has only its ancestors overlapping its header range. -/
def SharedFrontier (state : State) (lease : Lease) : Prop :=
  lease.mode = .shared ∧ NativeByteBorrow.lookup state.leases lease.tag = some lease ∧
    ∀ other ∈ state.leases, other.tag = lease.tag ∨ ParentPath state.leases other.tag lease.tag ∨
      ¬ NativeByteBorrow.Overlap lease.pointer lease.layout other.pointer other.layout

theorem shared_through_allowed (state : State) (valid : LedgerValid state) (lease : Lease)
    (frontier : SharedFrontier state lease) (pointer : Pointer) (layout : Layout)
    (contained : Contained pointer layout lease) :
    NativeByteBorrow.throughAllowed state lease.tag .shared pointer layout = true := by
  simp only [NativeByteBorrow.throughAllowed,List.all_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  intro other member
  rcases frontier.2.2 other member with same | ancestor | separate
  · exact Or.inl (Or.inl same)
  · have age := (valid.1 lease (NativeByteBorrow.lookup_selected _ _ _ frontier.2.1).1).1
    exact Or.inl (Or.inr (NativeByteBorrow.ancestor_complete state valid other.tag lease.tag ancestor state.nextTag age))
  · exact Or.inr (Or.inr (disjoint_subrange lease other pointer layout contained separate))

theorem shared_borrow_frontier (state next : State) (valid : LedgerValid state) (parent : Lease)
    (frontier : ExclusiveFrontier state parent) (pointer : Pointer) (layout : Layout) (tag : Nat)
    (borrowed : NativeByteBorrow.borrow state (some parent.tag) .shared pointer layout = some (tag,next)) :
    SharedFrontier next ⟨tag,some parent.tag,pointer,layout,.shared⟩ := by
  obtain ⟨fresh,_,_,leases,allowed,_⟩ := NativeByteBorrow.borrow_success state _ .shared pointer layout tag next borrowed
  obtain ⟨selected,found,_,_,origin,start,finish,_⟩ := NativeByteBorrow.parent_checked state parent.tag .shared pointer layout allowed
  have same := Option.some.inj (found.symm.trans frontier.2.1)
  subst selected
  let child : Lease := ⟨tag,some parent.tag,pointer,layout,.shared⟩
  have childFound : NativeByteBorrow.lookup next.leases tag = some child := by
    simp only [leases,NativeByteBorrow.lookup,ite_true,child]
  refine ⟨rfl,childFound,?_⟩
  intro other member
  rw [leases] at member
  rcases List.mem_cons.mp member with same | prior
  · exact Or.inl (congrArg Lease.tag same)
  · rcases frontier.2.2 other prior with same | ancestor | separate
    · right; left
      rw [same]
      exact .direct parent.tag tag child childFound rfl
    · right; left
      have path := path_cons_fresh state valid child fresh other.tag parent.tag ancestor
      rw [← leases] at path
      exact .trans other.tag parent.tag tag child childFound rfl path
    · exact Or.inr (Or.inr (disjoint_subrange parent other pointer layout ⟨origin,start,finish⟩ separate))

/-- The initialized shared header loan is issued by the existing machine grant. -/
theorem shared_grant_initialized (world : NativeReferenceMachine.State)
    (valid : NativeByteBorrow.WellFormed (NativeReferenceMachine.ledger world)) (lease : Lease)
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) lease)
    (pointer : Pointer) (layout : Layout) (output : List NativeByteMemory.Byte)
    (contained : Contained pointer layout lease)
    (loaded : NativeByteRange.loadRange world.pointers.heap.memory pointer layout = some output) :
    ∃ next, NativeReferenceMachine.grant world (some lease.tag) .shared pointer layout = some next ∧
      SharedFrontier (NativeReferenceMachine.ledger next)
        ⟨world.nextTag,some lease.tag,pointer,layout,.shared⟩ := by
  have allowed := parent_allowed (NativeReferenceMachine.ledger world) valid.2 lease frontier
    .shared pointer layout contained
  let ledgerNext : State := ⟨world.pointers.heap.memory,world.nextTag + 1,
    ⟨world.nextTag,some lease.tag,pointer,layout,.shared⟩ :: world.leases⟩
  have borrowed : NativeByteBorrow.borrow (NativeReferenceMachine.ledger world)
      (some lease.tag) .shared pointer layout = some (world.nextTag,ledgerNext) := by
    simp only [NativeByteBorrow.borrow,allowed,ite_true]
    change (NativeByteRange.loadRange world.pointers.heap.memory pointer layout).map _ = _
    simp only [loaded,Option.map_some]
    rfl
  let next : NativeReferenceMachine.State :=
    ⟨world.pointers,ledgerNext.nextTag,ledgerNext.leases,⟨world.nextTag⟩ :: world.references,
      ⟨world.nextTag,some lease.tag,pointer,layout,.shared⟩ :: world.births,world.outputs⟩
  have issued : NativeReferenceMachine.grant world (some lease.tag) .shared pointer layout = some next := by
    rw [NativeReferenceMachine.grant,borrowed]
    rfl
  exact ⟨next,issued,shared_borrow_frontier (NativeReferenceMachine.ledger world) ledgerNext valid.2
    lease frontier pointer layout world.nextTag borrowed⟩

/-- The retained whole RawVec shared borrow completes without a supplied
successful permission check or borrow result. -/
theorem rawvec_whole_complete (world : NativeReferenceMachine.State)
    (reference : NativeReferenceMachine.Reference) (lease : Lease)
    (valid : NativeByteBorrow.WellFormed (NativeReferenceMachine.ledger world))
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) lease)
    (tag : reference.tag = lease.tag) (shape : lease.layout = ⟨16,8⟩)
    (referenceResident : reference ∈ world.references) (pointerResident : lease.pointer ∈ world.pointers.registers)
    (bytes : List NativeByteMemory.Byte)
    (initialized : NativeByteRange.loadRange world.pointers.heap.memory lease.pointer ⟨16,8⟩ = some bytes) :
    ∃ next, NativeRawVecBorrow.reborrow world (.reference true reference 2) .whole =
        .value (.reference false ⟨world.nextTag⟩ 2) next ∧
      SharedFrontier (NativeReferenceMachine.ledger next)
        ⟨world.nextTag,some lease.tag,lease.pointer,⟨16,8⟩,.shared⟩ := by
  have registered : NativeByteBorrow.lookup world.leases lease.tag = some lease := frontier.2.1
  have selected : NativeRawVecBorrow.parent world (.reference true reference 2) =
      some (world.references.idxOf reference,world.pointers.registers.idxOf lease.pointer,lease) := by
    simp only [NativeRawVecBorrow.parent,ne_eq,not_true_eq_false,ite_false,tag,registered,
      Option.bind_eq_bind',Option.bind_some,frontier.1,NativeSliceLLBC.mode,shape,
      List.getElem?_idxOf referenceResident,List.getElem?_idxOf pointerResident,and_self,ite_true]
  let prepared := NativeRawVecBorrowCompleteness.prepared world lease
  have address : NativeReferenceMachine.execute world
      (.raw (.withAddress (world.pointers.registers.idxOf lease.pointer) lease.pointer.address)) = some prepared := by
    simp only [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,ite_true,
      NativePointerMachine.execute,List.getElem?_idxOf pointerResident,Option.map_some,
      NativeReferenceMachine.setPointers,prepared,NativeRawVecBorrowCompleteness.prepared,NativePointerMachine.push]
  have contained : Contained lease.pointer ⟨16,8⟩ lease := by
    rw [Contained,shape]
    exact ⟨rfl,Nat.le_refl _,Nat.le_refl _⟩
  obtain ⟨next,issued,available⟩ := shared_grant_initialized prepared valid lease frontier
    lease.pointer ⟨16,8⟩ bytes contained initialized
  have actual : NativeReferenceMachine.execute prepared
      (.reborrow (world.references.idxOf reference) 0 .shared ⟨16,8⟩) = some next := by
    simp only [NativeReferenceMachine.execute,prepared,NativeRawVecBorrowCompleteness.prepared,NativePointerMachine.push,
      List.getElem?_idxOf referenceResident,List.getElem?_cons_zero,Option.bind_some,tag]
    simpa only [prepared,NativeRawVecBorrowCompleteness.prepared,NativePointerMachine.push] using issued
  refine ⟨next,?_,available⟩
  simp only [NativeRawVecBorrow.reborrow,selected,NativeRawVecBorrow.Target.offset,
    NativeResidentVecBorrow.pointerAt_zero,address,NativeRawVecBorrow.Target.layout,actual,NativeRawVecBorrow.Target.count]
  rfl

/-- Stored RawVec fields carried by a checked shared header loan. -/
structure Header (world : NativeReferenceMachine.State) (reference : NativeReferenceMachine.Reference)
    (capacity length : NativeWord64Memory.Word) (buffer : Pointer) where
  lease : Lease
  valid : LedgerValid (NativeReferenceMachine.ledger world)
  frontier : SharedFrontier (NativeReferenceMachine.ledger world) lease
  tag : reference.tag = lease.tag
  shape : lease.layout = ⟨16,8⟩
  referenceResident : reference ∈ world.references
  pointerResident : lease.pointer ∈ world.pointers.registers
  fields : NativeResidentVecBorrow.Contents world.pointers.heap lease.pointer capacity length buffer

theorem Header.registered {world reference capacity length buffer}
    (header : Header world reference capacity length buffer) :
    NativeByteBorrow.lookup world.leases reference.tag = some header.lease := by
  rw [header.tag]
  exact header.frontier.2.1

theorem Header.resident {world reference capacity length buffer}
    (header : Header world reference capacity length buffer) :
    NativeResidentVecBorrow.Resident world (.reference false reference 2) header.lease.pointer capacity length buffer :=
  ⟨false,reference,2,header.lease,rfl,header.referenceResident,header.registered,rfl,
    header.frontier.1,Or.inr ⟨rfl,header.shape⟩,header.pointerResident,header.fields⟩

theorem Header.resolve {world reference capacity length buffer}
    (header : Header world reference capacity length buffer) :
    NativeRawVecReference.resolve world reference .inner = some (world.references.idxOf reference) := by
  have selected := NativeRawVecReference.select_complete .inner world _ reference header.lease
    (List.getElem?_idxOf header.referenceResident) header.registered header.frontier.1 header.shape
  simp only [NativeRawVecReference.resolve,List.getElem?_idxOf header.referenceResident,selected,and_self,ite_true]

theorem Header.field_allowed {world reference capacity length buffer}
    (header : Header world reference capacity length buffer) (offset : Nat) (slot : Pointer)
    (shifted : NativeByteRange.pointerAt header.lease.pointer offset = some slot) (bounded : offset + 8 ≤ 16) :
    NativeByteBorrow.throughAllowed (NativeReferenceMachine.ledger world) reference.tag .shared slot ⟨8,8⟩ = true := by
  obtain ⟨address,origin⟩ := NativeByteRange.pointerAt_fields _ _ _ shifted
  have contained : Contained slot ⟨8,8⟩ header.lease := by
    refine ⟨origin,?_,?_⟩
    · rw [address]; omega
    · rw [header.shape]
      change slot.address.val + 8 ≤ header.lease.pointer.address.val + 16
      rw [address]; omega
  rw [header.tag]
  exact shared_through_allowed _ header.valid header.lease header.frontier slot ⟨8,8⟩ contained

/-- A field read prepares its real address and emits the stored word bytes. -/
def wordWorld (world : NativeReferenceMachine.State) (slot : Pointer) (word : NativeWord64Memory.Word) :
    NativeReferenceMachine.State :=
  ⟨NativePointerMachine.push world.pointers slot,world.nextTag,world.leases,world.references,
    world.births,NativeWord64Memory.encode word :: world.outputs⟩

def pointerWorld (world : NativeReferenceMachine.State) (slot pointer : Pointer) : NativeReferenceMachine.State :=
  {world with pointers := NativePointerMachine.push (NativePointerMachine.push world.pointers slot) pointer}

theorem Header.capacity_execute {world reference capacity length buffer}
    (header : Header world reference capacity length buffer) :
    NativeReferenceMachine.execute world (.access (world.references.idxOf reference) 0 (.read 8 8)) =
      some (wordWorld world header.lease.pointer capacity) := by
  have shifted := NativeResidentVecBorrow.pointerAt_zero header.lease.pointer
  have stored : NativeWord64Memory.load world.pointers.heap.memory header.lease.pointer = some capacity := by
    simpa only [shifted,Option.bind_some] using header.fields.capacityStored
  have allowed := header.field_allowed 0 header.lease.pointer shifted (by decide)
  have bounded : 0 + 8 ≤ header.lease.layout.size := by rw [header.shape]; decide
  have preparation : NativeReferenceMachine.prepare world header.lease.pointer header.lease.pointer.address =
      some (NativePointerMachine.push world.pointers header.lease.pointer) := by
    simp only [NativeReferenceMachine.prepare,List.getElem?_idxOf header.pointerResident,ite_true,
      NativePointerMachine.execute,Option.map_some]
  have loaded := (NativeWord64Memory.load_iff_bytes _ _ _).mp stored
  simp only [NativeReferenceMachine.execute,NativeReferenceMachine.access,
    List.getElem?_idxOf header.referenceResident,Option.bind_some,header.registered,
    NativeReferenceMachine.Access.mode,NativeReferenceMachine.Access.layout,true_or,bounded,and_self,ite_true,
    shifted,allowed,preparation,NativeReferenceMachine.perform,NativePointerMachine.push,loaded,Option.map_some,wordWorld]

theorem Header.capacity_eval {world reference capacity length buffer}
    (header : Header world reference capacity length buffer) :
    NativeRawVecReference.eval world (.reference false reference 2) .capacity =
      .value (.usize capacity) (wordWorld world header.lease.pointer capacity) := by
  simp only [NativeRawVecReference.eval,NativeRawVecReference.objectOfCount,ite_true,header.resolve,
    NativeRawVecFields.capacityAccess,header.capacity_execute,wordWorld,List.getElem?_cons_zero,
    Option.bind_eq_bind',Option.bind_some,NativeWord64Memory.decode_encode]
  rw [ite_eq_left header.fields.capacityBound]

def Header.after_capacity {world reference capacity length buffer}
    (header : Header world reference capacity length buffer) :
    Header (wordWorld world header.lease.pointer capacity) reference capacity length buffer :=
  ⟨header.lease,header.valid,header.frontier,header.tag,header.shape,header.referenceResident,
    List.mem_cons_self,header.fields⟩

theorem Header.pointer_execute {world reference capacity length buffer}
    (header : Header world reference capacity length buffer) (slot : Pointer)
    (shifted : NativeByteRange.pointerAt header.lease.pointer 8 = some slot) :
    NativeReferenceMachine.execute world (.access (world.references.idxOf reference) 8 .loadPointer) =
      some (pointerWorld world slot buffer) := by
  have stored : NativePointerByteMemory.load world.pointers.heap slot = some buffer := by
    simpa only [shifted,Option.bind_some] using header.fields.pointerStored
  have allowed := header.field_allowed 8 slot shifted (by decide)
  have bounded : 8 + 8 ≤ header.lease.layout.size := by rw [header.shape]
  have scratch : (⟨slot.address,header.lease.pointer.provenance⟩ : Pointer) = slot := by
    rw [← (NativeByteRange.pointerAt_fields _ _ _ shifted).2]
  have preparation : NativeReferenceMachine.prepare world header.lease.pointer slot.address =
      some (NativePointerMachine.push world.pointers slot) := by
    simp only [NativeReferenceMachine.prepare,List.getElem?_idxOf header.pointerResident,ite_true,
      NativePointerMachine.execute,Option.map_some,scratch]
  simp only [NativeReferenceMachine.execute,NativeReferenceMachine.access,
    List.getElem?_idxOf header.referenceResident,Option.bind_some,header.registered,
    NativeReferenceMachine.Access.mode,NativeReferenceMachine.Access.layout,true_or,bounded,and_self,ite_true,
    shifted,allowed,preparation,NativeReferenceMachine.perform,NativePointerMachine.execute,NativePointerMachine.push,
    List.getElem?_cons_zero,stored,Option.map_some,NativeReferenceMachine.setPointers,pointerWorld]

def Header.after_pointer {world reference capacity length buffer}
    (header : Header world reference capacity length buffer) (slot : Pointer) :
    Header (pointerWorld world slot buffer) reference capacity length buffer :=
  ⟨header.lease,header.valid,header.frontier,header.tag,header.shape,header.referenceResident,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ header.pointerResident),header.fields⟩

theorem Header.pointer_eval {world reference capacity length buffer}
    (header : Header world reference capacity length buffer) :
    ∃ next, NativeRawVecReference.eval world (.reference false reference 2) .pointer =
      .value (.raw ⟨buffer,none⟩) next ∧
      Nonempty (Header next reference capacity length buffer) ∧ next.leases = world.leases ∧ next.pointers.heap = world.pointers.heap ∧ buffer ∈ next.pointers.registers := by
  have stored := header.fields.pointerStored
  cases shifted : NativeByteRange.pointerAt header.lease.pointer 8 with
  | none => simp only [shifted,Option.bind_none] at stored; cases stored
  | some slot =>
    refine ⟨pointerWorld world slot buffer,?_,⟨header.after_pointer slot⟩,rfl,rfl,List.mem_cons_self⟩
    simp only [NativeRawVecReference.eval,NativeRawVecReference.objectOfCount,ite_true,header.resolve,
      NativeRawVecFields.pointerAccess,header.pointer_execute slot shifted,pointerWorld,NativePointerMachine.push,
      List.getElem?_cons_zero]
    rw [ite_eq_left header.fields.nonnull]

def markerWorld (world : NativeReferenceMachine.State) (slot : Pointer) : NativeReferenceMachine.State :=
  ⟨NativePointerMachine.push world.pointers slot,world.nextTag,world.leases,world.references,world.births,[] :: world.outputs⟩

theorem Header.marker_eval {world reference capacity length buffer}
    (header : Header world reference capacity length buffer) :
    ∃ next, NativeRawVecReference.eval world (.reference false reference 2) .marker =
      .value .unit next ∧ next.leases = world.leases ∧ next.pointers.heap = world.pointers.heap := by
  have stored := header.fields.lengthStored
  cases shifted : NativeByteRange.pointerAt header.lease.pointer 16 with
  | none => simp only [shifted,Option.bind_none] at stored; cases stored
  | some slot =>
    obtain ⟨address,origin⟩ := NativeByteRange.pointerAt_fields _ _ _ shifted
    have geometry : NativeByteRange.Geometry slot ⟨0,1⟩ := by
      refine ⟨by decide,?_,by simp only [Nat.mod_one],?_⟩
      · omega
      · change slot.address.val + 0 < 2^64
        simpa only [Nat.add_zero] using slot.address.isLt
    have loaded := NativeByteRange.empty_range world.pointers.heap.memory slot 1 geometry
    have contained : Contained slot ⟨0,1⟩ header.lease := by
      refine ⟨origin,?_,?_⟩
      · rw [address]; omega
      · rw [header.shape]
        change slot.address.val + 0 ≤ header.lease.pointer.address.val + 16
        omega
    have allowed := shared_through_allowed (NativeReferenceMachine.ledger world) header.valid header.lease
      header.frontier slot ⟨0,1⟩ contained
    rw [← header.tag] at allowed
    have bounded : 16 + 0 ≤ header.lease.layout.size := by rw [header.shape]
    have scratch : (⟨slot.address,header.lease.pointer.provenance⟩ : Pointer) = slot := by rw [← origin]
    have preparation : NativeReferenceMachine.prepare world header.lease.pointer slot.address =
        some (NativePointerMachine.push world.pointers slot) := by
      simp only [NativeReferenceMachine.prepare,List.getElem?_idxOf header.pointerResident,ite_true,
        NativePointerMachine.execute,Option.map_some,scratch]
    have actual : NativeReferenceMachine.execute world (.access (world.references.idxOf reference) 16 (.read 0 1)) =
        some (markerWorld world slot) := by
      simp only [NativeReferenceMachine.execute,NativeReferenceMachine.access,
        List.getElem?_idxOf header.referenceResident,Option.bind_some,header.registered,
        NativeReferenceMachine.Access.mode,NativeReferenceMachine.Access.layout,true_or,bounded,and_self,ite_true,
        shifted,allowed,preparation,NativeReferenceMachine.perform,NativePointerMachine.push,loaded,Option.map_some,markerWorld]
    refine ⟨markerWorld world slot,?_,rfl,rfl⟩
    simp only [NativeRawVecReference.eval,NativeRawVecReference.objectOfCount,ite_true,header.resolve,
      NativeRawVecFields.markerAccess,actual]

/-- The actual shared borrow constructs the read conditions for the callee. -/
theorem rawvec_header_complete (world : NativeReferenceMachine.State)
    (reference : NativeReferenceMachine.Reference) (lease : Lease)
    (capacity length : NativeWord64Memory.Word) (buffer : Pointer)
    (reachable : NativeReferenceMachine.Reachable world)
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) lease)
    (tag : reference.tag = lease.tag) (shape : lease.layout = ⟨16,8⟩)
    (referenceResident : reference ∈ world.references) (pointerResident : lease.pointer ∈ world.pointers.registers)
    (fields : NativeResidentVecBorrow.Contents world.pointers.heap lease.pointer capacity length buffer)
    (bytes : List NativeByteMemory.Byte)
    (initialized : NativeByteRange.loadRange world.pointers.heap.memory lease.pointer ⟨16,8⟩ = some bytes) :
    ∃ next, NativeRawVecBorrow.reborrow world (.reference true reference 2) .whole =
        .value (.reference false ⟨world.nextTag⟩ 2) next ∧
      Nonempty (Header next ⟨world.nextTag⟩ capacity length buffer) ∧ NativeReferenceMachine.Reachable next := by
  have valid := NativeReferenceMachine.reachable_wellFormed world reachable
  obtain ⟨next,borrowed,available⟩ := rawvec_whole_complete world reference lease
    ⟨valid.1.1,valid.2.1⟩ frontier tag shape referenceResident pointerResident bytes initialized
  have original : NativeResidentVecBorrow.Resident world (.reference true reference 2)
      lease.pointer capacity length buffer := by
    have registered : NativeByteBorrow.lookup world.leases reference.tag = some lease := by
      rw [tag]; exact frontier.2.1
    exact ⟨true,reference,2,lease,rfl,referenceResident,registered,rfl,frontier.1,
      Or.inr ⟨rfl,shape⟩,pointerResident,fields⟩
  have resident := NativeResidentVecBorrow.rawvec_reborrow original borrowed
  have nextReach := NativeRawVecBorrow.reborrow_reachable world (.reference true reference 2) .whole reachable
  rw [borrowed] at nextReach
  have nextValid := NativeReferenceMachine.reachable_wellFormed next nextReach
  obtain ⟨mutable,child,count,childLease,valueEq,member,registered,baseEq,mode,childShape,present,contents⟩ := resident
  cases valueEq
  have leaseEq : childLease = ⟨world.nextTag,some lease.tag,lease.pointer,⟨16,8⟩,.shared⟩ :=
    Option.some.inj (registered.symm.trans available.2.1)
  subst childLease
  exact ⟨next,borrowed,⟨⟨_,nextValid.2.1,available,rfl,rfl,member,present,contents⟩⟩,nextReach⟩

end FormalProof4FHE.HasteBoots.NativeRawVecSharedCompleteness
