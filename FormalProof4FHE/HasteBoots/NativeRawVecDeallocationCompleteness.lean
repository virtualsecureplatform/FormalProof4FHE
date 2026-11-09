module
public import FormalProof4FHE.HasteBoots.NativeRawVecSharedCompleteness
public import FormalProof4FHE.HasteBoots.NativeVecBytePrefix
public import FormalProof4FHE.HasteBoots.NativeScopeRestoration
@[expose] public section

/-! Completion at the retained allocator-subobject and specified free boundary.
The external allocator implementation and native calling convention are separate
obligations. Buffer ownership and separation from live loans are explicit. -/
namespace FormalProof4FHE.HasteBoots.NativeRawVecDeallocationCompleteness
open NativeReferenceMachine (State Reference)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeByteBorrow (Lease)
open NativeVecBytePrefix (Available)

/-- Sufficient conditions at an exclusive resident RawVec method input. -/
structure Ready (world : State) (reference : Reference) (capacity length : Word) (buffer : Pointer) where
  lease : Lease
  reachable : NativeReferenceMachine.Reachable world
  frontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger world) lease
  tag : reference.tag = lease.tag
  shape : lease.layout = ⟨16,8⟩
  referenceResident : reference ∈ world.references
  pointerResident : lease.pointer ∈ world.pointers.registers
  fields : NativeResidentVecBorrow.Contents world.pointers.heap lease.pointer capacity length buffer
  initialized : ∃ bytes, NativeByteRange.loadRange world.pointers.heap.memory lease.pointer ⟨16,8⟩ = some bytes

theorem Ready.resident {world reference capacity length buffer} (ready : Ready world reference capacity length buffer) :
    NativeResidentVecBorrow.Resident world (.reference true reference 2) ready.lease.pointer capacity length buffer := by
  have registered : NativeByteBorrow.lookup world.leases reference.tag = some ready.lease := by
    rw [ready.tag]; exact ready.frontier.2.1
  exact ⟨true,reference,2,ready.lease,rfl,ready.referenceResident,registered,rfl,ready.frontier.1,
    Or.inr ⟨rfl,ready.shape⟩,ready.pointerResident,ready.fields⟩

theorem Ready.shared {world reference capacity length buffer} (ready : Ready world reference capacity length buffer) :
    ∃ next, NativeRawVecBorrow.reborrow world (.reference true reference 2) .whole =
        .value (.reference false ⟨world.nextTag⟩ 2) next ∧
      Nonempty (NativeRawVecSharedCompleteness.Header next ⟨world.nextTag⟩ capacity length buffer) ∧
      NativeReferenceMachine.Reachable next := by
  obtain ⟨bytes,loaded⟩ := ready.initialized
  exact NativeRawVecSharedCompleteness.rawvec_header_complete world reference ready.lease capacity length buffer
    ready.reachable ready.frontier ready.tag ready.shape ready.referenceResident ready.pointerResident ready.fields bytes loaded

/-- The allocator subobject is empty: overlapping header loans do not prevent
its shared borrow. Its resident parent still determines the complete origin. -/
theorem allocator_complete (world : State) (reference : Reference) (lease : Lease)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger world))
    (registered : NativeByteBorrow.lookup world.leases reference.tag = some lease)
    (exclusive : lease.mode = .exclusive) (shape : lease.layout = ⟨16,8⟩)
    (referenceResident : reference ∈ world.references) (pointerResident : lease.pointer ∈ world.pointers.registers) :
    ∃ slot next, NativeByteRange.pointerAt lease.pointer 16 = some slot ∧
      NativeRawVecBorrow.reborrow world (.reference true reference 2) .allocator =
        .value (.reference false ⟨world.nextTag⟩ 0) next ∧
      next.nextTag = world.nextTag + 1 ∧
      next.leases = ⟨world.nextTag,some reference.tag,slot,⟨0,1⟩,.shared⟩ :: world.leases ∧
      next.pointers.heap = world.pointers.heap := by
  have member := (NativeByteBorrow.lookup_selected _ _ _ registered).1
  have parentGeometry := (valid.1 lease member).2.1
  have noWrap : lease.pointer.address.val + 16 < 2^64 := by
    simpa only [shape] using parentGeometry.2.2.2
  let slot : Pointer := ⟨⟨lease.pointer.address.val + 16,noWrap⟩,lease.pointer.provenance⟩
  have shifted : NativeByteRange.pointerAt lease.pointer 16 = some slot := by
    simp only [NativeByteRange.pointerAt,noWrap,↓reduceDIte,slot]
  let prepared : State := {world with pointers := NativePointerMachine.push world.pointers slot}
  have selected : NativeRawVecBorrow.parent world (.reference true reference 2) =
      some (world.references.idxOf reference,world.pointers.registers.idxOf lease.pointer,lease) := by
    simp only [NativeRawVecBorrow.parent,ne_eq,not_true_eq_false,ite_false,registered,
      Option.bind_eq_bind',Option.bind_some,exclusive,NativeSliceLLBC.mode,shape,
      List.getElem?_idxOf referenceResident,List.getElem?_idxOf pointerResident,and_self,ite_true]
  have address : NativeReferenceMachine.execute world
      (.raw (.withAddress (world.pointers.registers.idxOf lease.pointer) slot.address)) = some prepared := by
    simp only [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,ite_true,
      NativePointerMachine.execute,List.getElem?_idxOf pointerResident,Option.map_some,
      NativeReferenceMachine.setPointers,prepared,slot,NativePointerMachine.push]
  have through : NativeByteBorrow.throughAllowed (NativeReferenceMachine.ledger prepared)
      reference.tag .shared slot ⟨0,1⟩ = true := by
    simp only [NativeByteBorrow.throughAllowed,List.all_eq_true]
    intro other _
    have compatible : NativeByteBorrow.Compatible .shared slot ⟨0,1⟩ other := by
      right
      simp only [NativeByteBorrow.Overlap]
      omega
    simp only [decide_eq_true compatible,Bool.or_true]
  have registeredPrepared : NativeByteBorrow.lookup (NativeReferenceMachine.ledger prepared).leases reference.tag =
      some lease := registered
  have tagBound : reference.tag < world.nextTag := by
    have age : lease.tag < world.nextTag := (valid.1 lease member).1
    have same := (NativeByteBorrow.lookup_selected _ _ _ registered).2
    omega
  have checked : reference.tag < (NativeReferenceMachine.ledger prepared).nextTag ∧
      (NativeByteBorrow.Mode.shared = .shared ∨ lease.mode = .exclusive) ∧
      slot.provenance = lease.pointer.provenance ∧ lease.pointer.address.val ≤ slot.address.val ∧
      slot.address.val + 0 ≤ lease.pointer.address.val + lease.layout.size := by
    refine ⟨tagBound,Or.inl rfl,rfl,?_,?_⟩ <;> simp only [slot,shape] <;> omega
  have allowed : NativeByteBorrow.parentAllowed (NativeReferenceMachine.ledger prepared)
      (some reference.tag) .shared slot ⟨0,1⟩ = true := by
    rw [NativeByteBorrow.parentAllowed,registeredPrepared]
    change decide (reference.tag < (NativeReferenceMachine.ledger prepared).nextTag ∧
      (NativeByteBorrow.Mode.shared = .shared ∨ lease.mode = .exclusive) ∧
      slot.provenance = lease.pointer.provenance ∧ lease.pointer.address.val ≤ slot.address.val ∧
      slot.address.val + 0 ≤ lease.pointer.address.val + lease.layout.size) &&
      NativeByteBorrow.throughAllowed (NativeReferenceMachine.ledger prepared) reference.tag .shared slot ⟨0,1⟩ = true
    rw [decide_eq_true checked,through]
    rfl
  have geometry : NativeByteRange.Geometry slot ⟨0,1⟩ := by
    refine ⟨by decide,?_,by simp only [Nat.mod_one],?_⟩
    · change lease.pointer.address.val + 16 ≠ 0
      omega
    · exact noWrap
  have loaded : NativeByteRange.loadRange (NativeReferenceMachine.ledger prepared).memory slot ⟨0,1⟩ = some [] :=
    NativeByteRange.empty_range prepared.pointers.heap.memory slot 1 geometry
  let next : State := ⟨prepared.pointers,world.nextTag + 1,
    ⟨world.nextTag,some reference.tag,slot,⟨0,1⟩,.shared⟩ :: world.leases,
    ⟨world.nextTag⟩ :: world.references,
    ⟨world.nextTag,some reference.tag,slot,⟨0,1⟩,.shared⟩ :: world.births,world.outputs⟩
  have issued : NativeReferenceMachine.grant prepared (some reference.tag) .shared slot ⟨0,1⟩ = some next := by
    simp only [NativeReferenceMachine.grant,NativeByteBorrow.borrow,allowed,ite_true,loaded,Option.map_some]
    rfl
  have actual : NativeReferenceMachine.execute prepared
      (.reborrow (world.references.idxOf reference) 0 .shared ⟨0,1⟩) = some next := by
    simp only [NativeReferenceMachine.execute,prepared,NativePointerMachine.push,
      List.getElem?_idxOf referenceResident,List.getElem?_cons_zero,Option.bind_some]
    exact issued
  refine ⟨slot,next,shifted,?_,rfl,rfl,rfl⟩
  simp only [NativeRawVecBorrow.reborrow,selected,NativeRawVecBorrow.Target.offset,shifted,address,
    NativeRawVecBorrow.Target.layout,actual,NativeRawVecBorrow.Target.count]
  rfl

theorem available_same_loans (before after : State) (pointer : Pointer) (size : Nat)
    (available : Available before pointer size) (same : after.leases = before.leases) : Available after pointer size := by
  simpa only [Available,same] using available

/-- Adding an empty allocator loan preserves full-capacity buffer separation. -/
theorem available_allocator (before after : State) (pointer slot : Pointer) (size tag parent : Nat)
    (available : Available before pointer size)
    (leases : after.leases = ⟨tag,some parent,slot,⟨0,1⟩,.shared⟩ :: before.leases) : Available after pointer size := by
  intro lease member
  rw [leases] at member
  rcases List.mem_cons.mp member with rfl | prior
  · simp only [NativeByteBorrow.Overlap]
    omega
  · exact available lease prior

/-- A contained header reborrow preserves physical buffer separation. -/
theorem available_child (before after : State) (pointer : Pointer) (size : Nat) (parent child : Lease)
    (available : Available before pointer size) (resident : parent ∈ before.leases)
    (contained : NativeBorrowFrontier.Contained child.pointer child.layout parent)
    (leases : after.leases = child :: before.leases) : Available after pointer size := by
  intro lease member
  rw [leases] at member
  rcases List.mem_cons.mp member with rfl | prior
  · have separate := available parent resident
    intro overlapping
    apply separate
    obtain ⟨_,start,finish⟩ := contained
    unfold NativeByteBorrow.Overlap at *
    omega
  · exact available lease prior

theorem available_grant (before after : State) (pointer : Pointer) (size parent : Nat)
    (mode : NativeByteBorrow.Mode) (childPointer : Pointer) (childLayout : NativeByteMemory.Layout)
    (available : Available before pointer size)
    (granted : NativeReferenceMachine.grant before (some parent) mode childPointer childLayout = some after) :
    Available after pointer size := by
  obtain ⟨tag,ledger,borrowed,_,_,leases,_⟩ := NativeReferenceMachine.grant_success before after _ mode _ _ granted
  obtain ⟨_,_,_,newLeases,allowed,_⟩ := NativeByteBorrow.borrow_success
    (NativeReferenceMachine.ledger before) _ mode childPointer childLayout tag ledger borrowed
  obtain ⟨parentLease,found,_,_,origin,start,finish,_⟩ := NativeByteBorrow.parent_checked
    (NativeReferenceMachine.ledger before) parent mode childPointer childLayout allowed
  apply available_child before after pointer size parentLease ⟨tag,some parent,childPointer,childLayout,mode⟩ available
    (NativeByteBorrow.lookup_selected _ _ _ found).1 ⟨origin,start,finish⟩
  exact leases.trans newLeases

theorem available_reborrow (before after : State) (pointer : Pointer) (size : Nat)
    (value output : NativeSliceLLBC.Value) (target : NativeRawVecBorrow.Target)
    (available : Available before pointer size)
    (borrowed : NativeRawVecBorrow.reborrow before value target = .value output after) : Available after pointer size := by
  obtain ⟨index,register,lease,childPointer,prepared,_,_,address,issued,_⟩ :=
    NativeRawVecBorrow.reborrow_success before after value output target borrowed
  have same : prepared.leases = before.leases := by
    simp [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,
      NativePointerMachine.execute,Option.map_map] at address
    obtain ⟨stored,_,same⟩ := address
    cases same
    rfl
  have ready := available_same_loans before prepared pointer size available same
  simp only [NativeReferenceMachine.execute,Option.bind_eq_some_iff] at issued
  obtain ⟨reference,_,stored,_,granted⟩ := issued
  exact available_grant prepared after pointer size reference.tag .shared stored target.layout ready granted

/-- Ownership of the exact live block and separation from all active loans
suffice for the actual specified byte/shadow free. -/
theorem free_complete (world : State) (pointer : Pointer) (size : Word)
    (positive : 0 < size.val) (nonnull : pointer.address.val ≠ 0)
    (layout : (NativeByteMemory.Layout.mk size.val 1).Valid)
    (resident : pointer ∈ world.pointers.registers) (available : Available world pointer size.val)
    (block : NativeByteMemory.Block) (member : block ∈ world.pointers.heap.memory.blocks)
    (base : block.pointer = pointer) (extent : block.layout = ⟨size.val,1⟩) :
    ∃ next, NativeByteDeallocation.execute world ⟨pointer,none⟩ size 1 = some next ∧
      NativePointerByteMemory.deallocate world.pointers.heap pointer ⟨size.val,1⟩ = some next.pointers.heap ∧
      next.leases = world.leases ∧ next.nextTag = world.nextTag := by
  obtain ⟨remaining,released⟩ := NativeResidentVec.release_owned_member world.pointers.heap.memory.blocks block member
  let heap : NativePointerByteMemory.State :=
    ⟨{world.pointers.heap.memory with blocks := remaining},
      world.pointers.heap.shadow.filter (fun cell => decide (cell.owner ≠ block.origin))⟩
  have freed : NativePointerByteMemory.deallocate world.pointers.heap pointer ⟨size.val,1⟩ = some heap := by
    rw [← base,← extent]
    have memory : NativeByteMemory.deallocate world.pointers.heap.memory block.pointer block.layout =
        some {world.pointers.heap.memory with blocks := remaining} := by
      simp only [NativeByteMemory.deallocate,released,Option.map_some]
    simp only [NativePointerByteMemory.deallocate,show block.pointer.provenance = some block.origin from rfl,
      Option.bind_eq_bind',Option.bind_some,memory,pure,heap]
  have allowed : NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger world) .exclusive pointer ⟨size.val,1⟩ = true := by
    simp only [NativeByteBorrow.rawAllowed,List.all_eq_true,decide_eq_true_eq]
    intro lease present
    exact Or.inr (available lease present)
  let next : State := {world with pointers := {world.pointers with heap}}
  refine ⟨next,?_,freed,rfl,rfl⟩
  have operands : ((none : Option Word) = none ∧ pointer.address.val ≠ 0) ∧ 0 < size.val ∧
      (NativeByteMemory.Layout.mk size.val (1 : Word).val).Valid := ⟨⟨rfl,nonnull⟩,positive,layout⟩
  rw [NativeByteDeallocation.execute,ite_eq_left operands,ite_eq_left (List.getElem?_idxOf resident)]
  simp only [NativeReferenceMachine.execute,NativeReferenceMachine.rawPermissions,
    NativeReferenceMachine.rawPermission,List.getElem?_idxOf resident,Option.any_some]
  simp only [show (1 : Word).val = 1 from rfl]
  rw [ite_eq_left allowed]
  simp only [NativePointerMachine.execute,List.getElem?_idxOf resident,Option.bind_some,
    freed,Option.map_some,NativeReferenceMachine.setPointers,NativePointerMachine.setHeap,next]

/-- RawVec reborrows only prepend fresh loans, including on a retained
address-preparation prefix that fails to issue a child. -/
theorem reborrow_extends (world : State) (value : NativeSliceLLBC.Value) (target : NativeRawVecBorrow.Target) :
    NativeScopeRestoration.Extends world (NativeRawVecBorrow.reborrow world value target).world := by
  cases selected : NativeRawVecBorrow.parent world value with
  | none => simp only [NativeRawVecBorrow.reborrow,selected,NativeRawVecFields.Result.world]; exact .refl _
  | some entry =>
    rcases entry with ⟨index,register,lease⟩
    cases shifted : NativeByteRange.pointerAt lease.pointer target.offset with
    | none => simp only [NativeRawVecBorrow.reborrow,selected,shifted,NativeRawVecFields.Result.world]; exact .refl _
    | some pointer =>
      cases address : NativeReferenceMachine.execute world (.raw (.withAddress register pointer.address)) with
      | none => simp only [NativeRawVecBorrow.reborrow,selected,shifted,address,NativeRawVecFields.Result.world]; exact .refl _
      | some prepared =>
        have first := NativeScopeRestoration.step world prepared _ address
        cases issued : NativeReferenceMachine.execute prepared (.reborrow index 0 .shared target.layout) with
        | none => simpa only [NativeRawVecBorrow.reborrow,selected,shifted,address,issued,NativeRawVecFields.Result.world] using first
        | some next =>
          have second := NativeScopeRestoration.step prepared next _ issued
          simpa only [NativeRawVecBorrow.reborrow,selected,shifted,address,issued,NativeRawVecFields.Result.world] using first.trans second

/-- Reservation and activation only prepend fresh loans. -/
theorem immediate_extends (world next : State) (input output : NativeSliceLLBC.Value)
    (created : NativeRawVecMutBorrow.immediate world input = .value output next) :
    NativeScopeRestoration.Extends world next := by
  cases reserved : NativeRawVecMutBorrow.reserve world input with
  | invalid failed => simp only [NativeRawVecMutBorrow.immediate,reserved] at created; cases created
  | value reservation prepared =>
    have activated : NativeRawVecMutBorrow.activate prepared reservation = .value output next := by
      simpa only [NativeRawVecMutBorrow.immediate,reserved] using created
    obtain ⟨_,_,_,_,_,_,_,address,_⟩ := NativeRawVecMutBorrow.reserve_success world prepared input reservation reserved
    have first := NativeScopeRestoration.step world prepared _ address
    have second := NativeScopeRestoration.step prepared next _
      (NativeRawVecMutBorrow.activate_success prepared next reservation output activated).1
    exact first.trans second

/-- An immediate exclusive header child retains full-capacity buffer separation. -/
theorem available_immediate (world next : State) (pointer : Pointer) (size : Nat)
    (input output : NativeSliceLLBC.Value) (available : Available world pointer size)
    (created : NativeRawVecMutBorrow.immediate world input = .value output next) : Available next pointer size := by
  cases reserved : NativeRawVecMutBorrow.reserve world input with
  | invalid failed => simp only [NativeRawVecMutBorrow.immediate,reserved] at created; cases created
  | value reservation prepared =>
    have activated : NativeRawVecMutBorrow.activate prepared reservation = .value output next := by
      simpa only [NativeRawVecMutBorrow.immediate,reserved] using created
    have loans := (NativeRawVecMutBorrow.reserve_no_loan world prepared input reservation reserved).2.1
    have preparedAvailable := available_same_loans world prepared pointer size available loans
    have executed := (NativeRawVecMutBorrow.activate_success prepared next reservation output activated).1
    simp only [NativeReferenceMachine.execute,Option.bind_eq_some_iff] at executed
    obtain ⟨reference,_,stored,_,granted⟩ := executed
    exact available_grant prepared next pointer size reference.tag .exclusive stored ⟨16,8⟩ preparedAvailable granted

/-- A successful actual immediate reborrow constructs the next callee's full
readiness conditions, including resident fields and initialized header bytes. -/
theorem Ready.immediate_complete {world reference capacity length buffer}
    (ready : Ready world reference capacity length buffer) :
    ∃ next, NativeRawVecMutBorrow.immediate world (.reference true reference 2) =
        .value (.reference true ⟨world.nextTag⟩ 2) next ∧
      Nonempty (Ready next ⟨world.nextTag⟩ capacity length buffer) ∧ next.pointers.heap = world.pointers.heap := by
  have valid := NativeReferenceMachine.reachable_wellFormed world ready.reachable
  obtain ⟨bytes,loaded⟩ := ready.initialized
  obtain ⟨next,created,frontier⟩ := NativeRawVecBorrowCompleteness.immediate_complete world reference ready.lease
    ⟨valid.1.1,valid.2.1⟩ ready.frontier ready.tag ready.shape ready.referenceResident ready.pointerResident bytes loaded
  have reached := NativeSliceLLBC.reference_runs_reachable world _ ready.reachable
    (NativeRawVecMutBorrow.immediate_projects world (.reference true reference 2))
  rw [created] at reached
  have heap := (NativeRawVecMutBorrow.immediate_heap_projects world (.reference true reference 2)).heap_eq
  rw [created] at heap
  change next.pointers.heap = world.pointers.heap at heap
  have resident := NativeResidentVecBorrow.rawvec_immediate ready.resident created
  obtain ⟨mutable,child,count,lease,valueEq,member,registered,baseEq,mode,shape,present,contents⟩ := resident
  cases valueEq
  have leaseEq : lease = ⟨world.nextTag,some ready.lease.tag,ready.lease.pointer,⟨16,8⟩,.exclusive⟩ :=
    Option.some.inj (registered.symm.trans frontier.2.1)
  subst lease
  have initialized : ∃ bytes, NativeByteRange.loadRange next.pointers.heap.memory ready.lease.pointer ⟨16,8⟩ = some bytes := by
    rw [heap]
    exact ⟨bytes,loaded⟩
  exact ⟨next,created,⟨⟨_,reached,frontier,rfl,rfl,member,present,contents,initialized⟩⟩,heap⟩

/-- Exact incoming loans make unit-return settlement inert. -/
theorem settle_same_loans (entered current : State)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger entered)) (same : current.leases = entered.leases) :
    NativeRecordLLBC.settle entered (.returned (.scalar .unit) current) = .returned (.scalar .unit) current := by
  have none : entered.leases.filter (fun lease => decide (entered.nextTag ≤ lease.tag)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro lease member
    have age : lease.tag < entered.nextTag := (valid.1 lease member).1
    simpa only [decide_eq_true_eq] using (show ¬ entered.nextTag ≤ lease.tag by omega)
  have cleanup : NativeReferenceCleanup.closeScope entered current = ⟨current,[],[]⟩ := by
    simp only [NativeReferenceCleanup.closeScope,NativeReferenceCleanup.scopeTags,same,none,List.map_nil,NativeReferenceCleanup.release]
  simp only [NativeRecordLLBC.settle,NativeReferenceCleanup.settleUnit,cleanup,List.isEmpty_nil,ite_true]

/-- Reachable scope cleanup completes and restores the exact incoming loan
list, without changing the resulting heap. -/
theorem settle_complete (entered current : State)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger entered))
    (extended : NativeScopeRestoration.Extends entered current)
    (reachable : NativeReferenceMachine.Reachable current) :
    ∃ final, NativeRecordLLBC.settle entered (.returned (.scalar .unit) current) = .returned (.scalar .unit) final ∧
      final.leases = entered.leases ∧ final.pointers.heap = current.pointers.heap ∧ NativeReferenceMachine.Reachable final := by
  obtain ⟨complete,restored⟩ := NativeScopeRestoration.closeScope_reachable_restores entered current extended valid reachable
  refine ⟨(NativeReferenceCleanup.closeScope entered current).world,?_,restored,
    (NativeReferenceCleanup.closeScope_heap_projects entered current).heap_eq,
    NativeReferenceCleanup.closeScope_reachable entered current reachable⟩
  simp only [NativeRecordLLBC.settle,NativeReferenceCleanup.settleUnit,complete,List.isEmpty_nil,ite_true]

end FormalProof4FHE.HasteBoots.NativeRawVecDeallocationCompleteness
