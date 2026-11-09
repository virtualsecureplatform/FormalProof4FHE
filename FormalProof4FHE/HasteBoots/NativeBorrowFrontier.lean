module
public import FormalProof4FHE.HasteBoots.NativeByteRangeCompleteness
@[expose] public section

/-! A logical alias condition sufficient for exclusive subrange borrowing.
Ancestors may overlap; every other live lease is physically disjoint. This does
not assert a native Rust lifetime or compiler correspondence. -/
namespace FormalProof4FHE.HasteBoots.NativeBorrowFrontier
open NativeByteBorrow (State Lease ParentPath LedgerValid Overlap)
open NativePointerStorage (Pointer)
open NativeByteMemory (Layout)

/-- Physical containment with unchanged complete pointer origin. -/
def Contained (pointer : Pointer) (layout : Layout) (parent : Lease) : Prop :=
  pointer.provenance = parent.pointer.provenance ∧ parent.pointer.address.val ≤ pointer.address.val ∧
    pointer.address.val + layout.size ≤ parent.pointer.address.val + parent.layout.size

/-- The selected exclusive lease has no overlapping descendant or unrelated
live lease. Its ancestors remain available for checked reborrows. -/
def ExclusiveFrontier (state : State) (lease : Lease) : Prop :=
  lease.mode = .exclusive ∧ NativeByteBorrow.lookup state.leases lease.tag = some lease ∧
    ∀ other ∈ state.leases, other.tag = lease.tag ∨ ParentPath state.leases other.tag lease.tag ∨
      ¬ Overlap lease.pointer lease.layout other.pointer other.layout

theorem disjoint_subrange (parent other : Lease) (pointer : Pointer) (layout : Layout)
    (contained : Contained pointer layout parent)
    (separate : ¬ Overlap parent.pointer parent.layout other.pointer other.layout) :
    ¬ Overlap pointer layout other.pointer other.layout := by
  intro overlapping
  apply separate
  unfold Overlap at *
  obtain ⟨_,start,finish⟩ := contained
  omega

theorem singleton_frontier (state : State) (lease : Lease) (only : state.leases = [lease])
    (exclusive : lease.mode = .exclusive) : ExclusiveFrontier state lease := by
  refine ⟨exclusive,?_,?_⟩
  · simp only [only,NativeByteBorrow.lookup,ite_true]
  · intro other member
    rw [only] at member
    have same := List.mem_singleton.mp member
    exact Or.inl (congrArg Lease.tag same)

theorem frontier_transport (before after : State) (lease : Lease) (frontier : ExclusiveFrontier before lease)
    (same : after.leases = before.leases) : ExclusiveFrontier after lease := by
  simpa only [ExclusiveFrontier,same] using frontier

theorem through_allowed (state : State) (valid : LedgerValid state) (lease : Lease)
    (frontier : ExclusiveFrontier state lease) (mode : NativeByteBorrow.Mode) (pointer : Pointer) (layout : Layout)
    (contained : Contained pointer layout lease) :
    NativeByteBorrow.throughAllowed state lease.tag mode pointer layout = true := by
  simp only [NativeByteBorrow.throughAllowed,List.all_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  intro other member
  rcases frontier.2.2 other member with same | ancestor | separate
  · exact Or.inl (Or.inl same)
  · have age := (valid.1 lease (NativeByteBorrow.lookup_selected _ _ _ frontier.2.1).1).1
    exact Or.inl (Or.inr (NativeByteBorrow.ancestor_complete state valid other.tag lease.tag ancestor state.nextTag age))
  · exact Or.inr (Or.inr (disjoint_subrange lease other pointer layout contained separate))

theorem parent_allowed (state : State) (valid : LedgerValid state) (lease : Lease)
    (frontier : ExclusiveFrontier state lease) (mode : NativeByteBorrow.Mode) (pointer : Pointer) (layout : Layout)
    (contained : Contained pointer layout lease) :
    NativeByteBorrow.parentAllowed state (some lease.tag) mode pointer layout = true := by
  have age := (valid.1 lease (NativeByteBorrow.lookup_selected _ _ _ frontier.2.1).1).1
  have checked : lease.tag < state.nextTag ∧ (mode = .shared ∨ lease.mode = .exclusive) ∧
      pointer.provenance = lease.pointer.provenance ∧ lease.pointer.address.val ≤ pointer.address.val ∧
      pointer.address.val + layout.size ≤ lease.pointer.address.val + lease.layout.size :=
    ⟨age,Or.inr frontier.1,contained⟩
  simp only [NativeByteBorrow.parentAllowed,frontier.2.1,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨checked,through_allowed state valid lease frontier mode pointer layout contained⟩

theorem path_cons_fresh (state : State) (valid : LedgerValid state) (fresh : Lease)
    (tag : fresh.tag = state.nextTag) (older child : Nat) (path : ParentPath state.leases older child) :
    ParentPath (fresh :: state.leases) older child := by
  have keep : ∀ child lease, NativeByteBorrow.lookup state.leases child = some lease →
      NativeByteBorrow.lookup (fresh :: state.leases) child = some lease := by
    intro child lease found
    obtain ⟨member,same⟩ := NativeByteBorrow.lookup_selected _ _ _ found
    have bound := (valid.1 lease member).1
    have different : fresh.tag ≠ child := by rw [tag]; omega
    simp only [NativeByteBorrow.lookup,ite_eq_right different,found]
  induction path with
  | direct child lease found parent => exact .direct _ _ _ (keep _ _ found) parent
  | trans middle child lease found parent previous ih => exact .trans _ _ _ _ (keep _ _ found) parent ih

/-- A successful fresh exclusive child becomes the available frontier. Existing
ancestors are retained as ancestors, rather than incorrectly required disjoint. -/
theorem borrow_frontier (state next : State) (valid : LedgerValid state) (parent : Lease)
    (frontier : ExclusiveFrontier state parent) (pointer : Pointer) (layout : Layout) (tag : Nat)
    (borrowed : NativeByteBorrow.borrow state (some parent.tag) .exclusive pointer layout = some (tag,next)) :
    ExclusiveFrontier next ⟨tag,some parent.tag,pointer,layout,.exclusive⟩ := by
  obtain ⟨fresh,_,_,leases,allowed,_⟩ := NativeByteBorrow.borrow_success state _ .exclusive pointer layout tag next borrowed
  obtain ⟨selected,found,_,_,origin,start,finish,_⟩ := NativeByteBorrow.parent_checked state parent.tag .exclusive pointer layout allowed
  have same := Option.some.inj (found.symm.trans frontier.2.1)
  subst selected
  let child : Lease := ⟨tag,some parent.tag,pointer,layout,.exclusive⟩
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

/-- An initialized layout with the logical alias condition issues a real child
reference. This also covers aligned record layouts, not only byte slices. -/
theorem grant_initialized (world : NativeReferenceMachine.State)
    (valid : NativeByteBorrow.WellFormed (NativeReferenceMachine.ledger world)) (lease : Lease)
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) lease)
    (pointer : Pointer) (layout : Layout) (output : List NativeByteMemory.Byte)
    (contained : Contained pointer layout lease)
    (loaded : NativeByteRange.loadRange world.pointers.heap.memory pointer layout = some output) :
    ∃ next, NativeReferenceMachine.grant world (some lease.tag) .exclusive pointer layout = some next ∧
      ExclusiveFrontier (NativeReferenceMachine.ledger next)
        ⟨world.nextTag,some lease.tag,pointer,layout,.exclusive⟩ := by
  have allowed := parent_allowed (NativeReferenceMachine.ledger world) valid.2 lease frontier
    .exclusive pointer layout contained
  let ledgerNext : State := ⟨world.pointers.heap.memory,world.nextTag + 1,
    ⟨world.nextTag,some lease.tag,pointer,layout,.exclusive⟩ :: world.leases⟩
  have borrowed : NativeByteBorrow.borrow (NativeReferenceMachine.ledger world)
      (some lease.tag) .exclusive pointer layout = some (world.nextTag,ledgerNext) := by
    simp only [NativeByteBorrow.borrow,allowed,ite_true]
    change (NativeByteRange.loadRange world.pointers.heap.memory pointer layout).map _ = _
    simp only [loaded,Option.map_some]
    rfl
  let next : NativeReferenceMachine.State :=
    ⟨world.pointers,ledgerNext.nextTag,ledgerNext.leases,⟨world.nextTag⟩ :: world.references,
      ⟨world.nextTag,some lease.tag,pointer,layout,.exclusive⟩ :: world.births,world.outputs⟩
  have issued : NativeReferenceMachine.grant world (some lease.tag) .exclusive pointer layout = some next := by
    rw [NativeReferenceMachine.grant,borrowed]
    rfl
  exact ⟨next,issued,borrow_frontier (NativeReferenceMachine.ledger world) ledgerNext valid.2
    lease frontier pointer layout world.nextTag borrowed⟩

/-- Stored Vec fields suffice for the full aligned header reborrow. -/
theorem vec_header_grant_complete (world : NativeReferenceMachine.State) (index : Nat)
    (descriptor : NativeResidentVec.Descriptor world index)
    (valid : NativeByteBorrow.WellFormed (NativeReferenceMachine.ledger world))
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    ∃ next, NativeReferenceMachine.grant world (some descriptor.lease.tag) .exclusive
        descriptor.lease.pointer ⟨24,8⟩ = some next ∧
      ExclusiveFrontier (NativeReferenceMachine.ledger next)
        ⟨world.nextTag,some descriptor.lease.tag,descriptor.lease.pointer,⟨24,8⟩,.exclusive⟩ := by
  obtain ⟨bytes,loaded⟩ := descriptor.header_initialized valid.1
  apply grant_initialized world valid descriptor.lease frontier _ _ bytes _ loaded
  rw [Contained,descriptor.extent]
  exact ⟨rfl,Nat.le_refl _,Nat.le_refl _⟩

/-- A bounded initialized subrange can actually be borrowed, and the fresh
child retains the logical alias condition needed for subsequent indexing. -/
theorem borrow_subrange (state : State) (valid : NativeByteBorrow.WellFormed state) (lease : Lease)
    (frontier : ExclusiveFrontier state lease) (size offset requested : Nat)
    (shape : lease.layout = ⟨size,1⟩) (output : List NativeByteMemory.Byte)
    (loaded : NativeByteRange.loadRange state.memory lease.pointer ⟨size,1⟩ = some output)
    (bounded : offset + requested ≤ size) :
    ∃ pointer next, NativeByteRange.pointerAt lease.pointer offset = some pointer ∧
      NativeByteBorrow.borrow state (some lease.tag) .exclusive pointer ⟨requested,1⟩ = some (state.nextTag,next) ∧
      ExclusiveFrontier next ⟨state.nextTag,some lease.tag,pointer,⟨requested,1⟩,.exclusive⟩ := by
  obtain ⟨pointer,shifted,read⟩ := NativeByteRangeCompleteness.loadRange_subrange state.memory valid.1
    lease.pointer size offset requested output loaded bounded
  obtain ⟨address,origin⟩ := NativeByteRange.pointerAt_fields lease.pointer offset pointer shifted
  have contained : Contained pointer ⟨requested,1⟩ lease := by
    refine ⟨origin,?_,?_⟩
    · rw [address]; omega
    · rw [address,shape]; change lease.pointer.address.val + offset + requested ≤ lease.pointer.address.val + size; omega
  have allowed := parent_allowed state valid.2 lease frontier .exclusive pointer ⟨requested,1⟩ contained
  let next : State := ⟨state.memory,state.nextTag + 1,⟨state.nextTag,some lease.tag,pointer,⟨requested,1⟩,.exclusive⟩ :: state.leases⟩
  have borrowed : NativeByteBorrow.borrow state (some lease.tag) .exclusive pointer ⟨requested,1⟩ = some (state.nextTag,next) := by
    simp only [NativeByteBorrow.borrow,allowed,ite_true,read,Option.map_some,next]
  exact ⟨pointer,next,shifted,borrowed,borrow_frontier state next valid.2 lease frontier pointer ⟨requested,1⟩ state.nextTag borrowed⟩

/-- The same sufficient conditions issue an actual closed-machine reference;
reference and birth registers are minted by the existing grant operation. -/
theorem grant_subrange (world : NativeReferenceMachine.State)
    (valid : NativeByteBorrow.WellFormed (NativeReferenceMachine.ledger world)) (lease : Lease)
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) lease) (size offset requested : Nat)
    (shape : lease.layout = ⟨size,1⟩) (output : List NativeByteMemory.Byte)
    (loaded : NativeByteRange.loadRange world.pointers.heap.memory lease.pointer ⟨size,1⟩ = some output)
    (bounded : offset + requested ≤ size) :
    ∃ pointer next, NativeByteRange.pointerAt lease.pointer offset = some pointer ∧
      NativeReferenceMachine.grant world (some lease.tag) .exclusive pointer ⟨requested,1⟩ = some next ∧
      ExclusiveFrontier (NativeReferenceMachine.ledger next)
        ⟨world.nextTag,some lease.tag,pointer,⟨requested,1⟩,.exclusive⟩ := by
  obtain ⟨pointer,ledgerNext,shifted,borrowed,available⟩ :=
    borrow_subrange (NativeReferenceMachine.ledger world) valid lease frontier size offset requested shape output loaded bounded
  let next : NativeReferenceMachine.State :=
    ⟨world.pointers,ledgerNext.nextTag,ledgerNext.leases,⟨world.nextTag⟩ :: world.references,
      ⟨world.nextTag,some lease.tag,pointer,⟨requested,1⟩,.exclusive⟩ :: world.births,world.outputs⟩
  have issued : NativeReferenceMachine.grant world (some lease.tag) .exclusive pointer ⟨requested,1⟩ = some next := by
    rw [NativeReferenceMachine.grant,borrowed]
    rfl
  have memorySame := (NativeByteBorrow.borrow_success (NativeReferenceMachine.ledger world) (some lease.tag)
    .exclusive pointer ⟨requested,1⟩ world.nextTag ledgerNext borrowed).2.1
  have ledgerSame : NativeReferenceMachine.ledger next = ledgerNext := by
    cases ledgerNext
    cases memorySame
    rfl
  exact ⟨pointer,next,shifted,issued,by rw [ledgerSame]; exact available⟩


/-- Initialized elements and a logical alias condition suffice for the actual
closed-machine index operation, including address preparation and child grant. -/
theorem index_complete (world : NativeReferenceMachine.State)
    (valid : NativeByteBorrow.WellFormed (NativeReferenceMachine.ledger world))
    (slice : NativeByteSliceIndex.Slice) (lease : Lease)
    (registered : NativeByteBorrow.lookup world.leases slice.reference.tag = some lease)
    (referenceResident : slice.reference ∈ world.references)
    (pointerResident : lease.pointer ∈ world.pointers.registers)
    (shape : lease.layout = ⟨slice.length.val,1⟩)
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) lease)
    (output : List NativeByteMemory.Byte)
    (loaded : NativeByteRange.loadRange world.pointers.heap.memory lease.pointer ⟨slice.length.val,1⟩ = some output)
    (offset : NativeWord64Memory.Word) (bounded : offset.val < slice.length.val) :
    ∃ pointer next, NativeByteSliceIndex.index world slice offset = .value ⟨world.nextTag⟩ next ∧
      NativeByteRange.pointerAt lease.pointer offset.val = some pointer ∧
      ExclusiveFrontier (NativeReferenceMachine.ledger next)
        ⟨world.nextTag,some lease.tag,pointer,⟨1,1⟩,.exclusive⟩ := by
  have tag := (NativeByteBorrow.lookup_selected _ _ _ registered).2
  have selected : NativeByteSliceIndex.select world slice =
      some ⟨world.references.idxOf slice.reference,world.pointers.registers.idxOf lease.pointer,lease⟩ := by
    simp only [NativeByteSliceIndex.select,registered,Option.bind_eq_bind',Option.bind_some,
      List.getElem?_idxOf referenceResident,List.getElem?_idxOf pointerResident,shape,frontier.1,and_self,ite_true]
  obtain ⟨pointer,shifted,_⟩ := NativeByteRangeCompleteness.loadRange_subrange _ valid.1 lease.pointer
    slice.length.val offset.val 1 output loaded (by omega)
  let prepared : NativeReferenceMachine.State := {world with pointers := NativePointerMachine.push world.pointers pointer}
  have provenance := (NativeByteRange.pointerAt_fields lease.pointer offset.val pointer shifted).2
  have scratch : (⟨pointer.address,lease.pointer.provenance⟩ : Pointer) = pointer := by rw [← provenance]
  have preparation : NativeReferenceMachine.execute world
      (.raw (.withAddress (world.pointers.registers.idxOf lease.pointer) pointer.address)) = some prepared := by
    simp only [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,ite_true,
      NativePointerMachine.execute,List.getElem?_idxOf pointerResident,Option.map_some,
      NativeReferenceMachine.setPointers,scratch,prepared]
  obtain ⟨point,next,atPoint,issued,available⟩ := grant_subrange prepared valid lease frontier slice.length.val offset.val 1
    shape output loaded (by omega)
  have same : point = pointer := Option.some.inj (atPoint.symm.trans shifted)
  subst point
  have granted : NativeReferenceMachine.execute prepared
      (.reborrow (world.references.idxOf slice.reference) 0 .exclusive ⟨1,1⟩) = some next := by
    simp only [NativeReferenceMachine.execute,prepared,NativePointerMachine.push,
      List.getElem?_idxOf referenceResident,List.getElem?_cons_zero,Option.bind_some]
    simpa only [tag,prepared,NativePointerMachine.push] using issued
  refine ⟨pointer,next,?_,shifted,available⟩
  simp only [NativeByteSliceIndex.index,bounded,ite_true,selected,shifted,preparation,granted,prepared]

end FormalProof4FHE.HasteBoots.NativeBorrowFrontier
