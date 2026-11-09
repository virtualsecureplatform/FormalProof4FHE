module
public import FormalProof4FHE.HasteBoots.NativeResidentVec
@[expose] public section

/-! Physical Vec contents carried by actual whole/subobject borrow operations.
The source input retains a stable reference tag while register positions shift.
These facts do not establish native construction or lifetime refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeResidentVecBorrow
open NativeReferenceMachine (State Reference)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeByteBorrow (Lease)
open NativeSliceLLBC (Value)

/-- Heap observations are independent of the current reference-register index.
A RawVec view retains the containing Vec length observation without acquiring
permission to access that field through its smaller lease. -/
structure Contents (heap : NativePointerByteMemory.State) (base : Pointer)
    (capacity length : Word) (buffer : Pointer) : Prop where
  capacityStored : ((NativeByteRange.pointerAt base 0).bind
    (NativeWord64Memory.load heap.memory)) = some capacity
  pointerStored : ((NativeByteRange.pointerAt base 8).bind
    (NativePointerByteMemory.load heap)) = some buffer
  lengthStored : ((NativeByteRange.pointerAt base 16).bind
    (NativeWord64Memory.load heap.memory)) = some length
  capacityBound : capacity.val < 2^63
  lengthBound : length.val ≤ capacity.val
  nonnull : buffer.address.val ≠ 0

def Resident (world : State) (value : Value) (base : Pointer) (capacity length : Word) (buffer : Pointer) : Prop :=
  ∃ mutable reference count lease,
    value = .reference mutable reference count ∧ reference ∈ world.references ∧
    NativeByteBorrow.lookup world.leases reference.tag = some lease ∧ lease.pointer = base ∧
    lease.mode = NativeSliceLLBC.mode mutable ∧
    ((count = 3 ∧ lease.layout = ⟨24,8⟩) ∨ (count = 2 ∧ lease.layout = ⟨16,8⟩)) ∧
    base ∈ world.pointers.registers ∧ Contents world.pointers.heap base capacity length buffer

theorem pointerAt_zero (pointer : Pointer) : NativeByteRange.pointerAt pointer 0 = some pointer := by
  simp only [NativeByteRange.pointerAt, Nat.add_zero, dite_eq_left pointer.address.isLt]

theorem descriptor_contents {world : State} {index : Nat} (descriptor : NativeResidentVec.Descriptor world index) :
    Contents world.pointers.heap descriptor.lease.pointer descriptor.capacity descriptor.length descriptor.buffer := by
  refine ⟨?_,?_,?_,descriptor.capacityBound,descriptor.lengthBound,descriptor.nonnull⟩
  · simp only [descriptor.capacityAt, Option.bind_some, descriptor.capacityStored]
  · simp only [descriptor.pointerAt, Option.bind_some, descriptor.pointerStored]
  · simp only [descriptor.lengthAt, Option.bind_some, descriptor.lengthStored]

theorem descriptor_resident {world : State} {index : Nat} (descriptor : NativeResidentVec.Descriptor world index) :
    Resident world (.reference true descriptor.reference 3) descriptor.lease.pointer
      descriptor.capacity descriptor.length descriptor.buffer := by
  exact ⟨true,descriptor.reference,3,descriptor.lease,rfl,List.mem_of_getElem? descriptor.resident,
    descriptor.registered,rfl,descriptor.exclusive,Or.inl ⟨rfl,descriptor.extent⟩,
    List.mem_of_getElem? descriptor.baseResident,descriptor_contents descriptor⟩

theorem Contents.heap_frame {before after : NativePointerByteMemory.State} {base buffer : Pointer} {capacity length : Word}
    (contents : Contents before base capacity length buffer) (same : after = before) :
    Contents after base capacity length buffer := same ▸ contents

/-- A newly granted reference carries the exact selected pointer, layout and
mode. This uses the actual allocation/borrow checks, rather than a supplied tag. -/
theorem grant_resident (world next : State) (parent : Option Nat) (mutable : Bool)
    (base buffer : Pointer) (capacity length count : Word) (layout : NativeByteMemory.Layout)
    (shape : (count = 3 ∧ layout = ⟨24,8⟩) ∨ (count = 2 ∧ layout = ⟨16,8⟩))
    (member : base ∈ world.pointers.registers)
    (contents : Contents world.pointers.heap base capacity length buffer)
    (granted : NativeReferenceMachine.grant world parent (NativeSliceLLBC.mode mutable) base layout = some next) :
    Resident next (.reference mutable ⟨world.nextTag⟩ count) base capacity length buffer := by
  obtain ⟨tag,ledger,borrowed,pointers,tags,leases,references,_⟩ :=
    NativeReferenceMachine.grant_success world next parent (NativeSliceLLBC.mode mutable) base layout granted
  obtain ⟨fresh,_,_,leaseEq,_⟩ := NativeByteBorrow.borrow_success (NativeReferenceMachine.ledger world)
    parent (NativeSliceLLBC.mode mutable) base layout tag ledger borrowed
  change tag = world.nextTag at fresh
  refine ⟨mutable,⟨world.nextTag⟩,count,⟨world.nextTag,parent,base,layout,NativeSliceLLBC.mode mutable⟩,
    rfl,?_,?_,rfl,rfl,shape,?_,?_⟩
  · rw [references,fresh]; exact List.mem_cons_self
  · rw [leases,leaseEq,fresh]; simp only [NativeByteBorrow.lookup, ite_true]
  · rw [pointers]; exact member
  · exact contents.heap_frame (congrArg NativePointerMachine.State.heap pointers)

theorem Resident.reframe {world next : State} {value : Value} {base buffer : Pointer} {capacity length : Word}
    (resident : Resident world value base capacity length buffer)
    (heap : next.pointers.heap = world.pointers.heap)
    (references : next.references = world.references) (leases : next.leases = world.leases)
    (registers : ∀ pointer ∈ world.pointers.registers, pointer ∈ next.pointers.registers) :
    Resident next value base capacity length buffer := by
  obtain ⟨mutable,reference,count,lease,valueEq,member,registered,baseEq,mode,shape,present,contents⟩ := resident
  exact ⟨mutable,reference,count,lease,valueEq,references ▸ member,leases ▸ registered,
    baseEq,mode,shape,registers base present,contents.heap_frame heap⟩

/-- Reads add scratch/value registers while retaining the incoming loan and
its physical contents. This also covers zero-byte marker reads. -/
theorem access_resident {world next : State} {value : Value} {base buffer : Pointer} {capacity length : Word}
    (resident : Resident world value base capacity length buffer) (index offset : Nat)
    (action : NativeReferenceMachine.Access)
    (readonly : NativeHeapFrame.readOnly (.access index offset action) = true)
    (executed : NativeReferenceMachine.execute world (.access index offset action) = some next) :
    Resident next value base capacity length buffer := by
  obtain ⟨_,lease,slot,prepared,_,_,_,_,_,_,preparation,performed⟩ :=
    NativeReferenceMachine.access_success world next index offset action executed
  have preparedEq := (NativeReferenceMachine.prepare_success world lease.pointer slot.address prepared preparation).2
  cases action with
  | writeBytes alignment bytes => cases readonly
  | storePointer register => cases readonly
  | read size alignment =>
    simp only [NativeReferenceMachine.perform, Option.map_eq_some_iff] at performed
    obtain ⟨bytes,_,same⟩ := performed
    subst next
    apply resident.reframe
    · rw [preparedEq]; rfl
    · rfl
    · rfl
    · intro pointer member
      rw [preparedEq]
      exact List.mem_cons_of_mem _ member
  | loadPointer =>
    simp only [NativeReferenceMachine.perform, Option.map_eq_some_iff] at performed
    obtain ⟨pointers,actual,same⟩ := performed
    subst next
    simp only [NativePointerMachine.execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at actual
    obtain ⟨location,_,loaded,_,same⟩ := actual
    subst pointers
    apply resident.reframe
    · change prepared.heap = world.pointers.heap
      rw [preparedEq]; rfl
    · rfl
    · rfl
    · intro pointer member
      change pointer ∈ loaded :: prepared.registers
      apply List.mem_cons_of_mem
      rw [preparedEq]
      exact List.mem_cons_of_mem _ member

theorem lookup_filter_other (leases : List Lease) (tag removed : Nat) (different : tag ≠ removed) :
    NativeByteBorrow.lookup (leases.filter (fun lease => decide (lease.tag ≠ removed))) tag =
      NativeByteBorrow.lookup leases tag := by
  induction leases with
  | nil => rfl
  | cons head tail ih =>
    by_cases deleted : head.tag = removed
    · have excluded : decide (head.tag ≠ removed) = false := by simp only [deleted,ne_eq,not_true_eq_false,decide_false]
      have differentHead : head.tag ≠ tag := by rw [deleted]; exact Ne.symm different
      rw [List.filter_cons,excluded]
      simp only [Bool.false_eq_true,ite_false,NativeByteBorrow.lookup,differentHead,ih]
    · have retained : decide (head.tag ≠ removed) = true := by simpa only [decide_eq_true_eq] using deleted
      rw [List.filter_cons,retained]
      by_cases selected : head.tag = tag
      · simp only [ite_true,NativeByteBorrow.lookup,selected]
      · simp only [ite_true,NativeByteBorrow.lookup,selected,ite_false,ih]

theorem ends_lookup (world next : State) (tags : List Nat) (ended : NativeReferenceCleanup.Ends world tags next)
    (tag : Nat) (kept : tag ∉ tags) : NativeByteBorrow.lookup next.leases tag = NativeByteBorrow.lookup world.leases tag := by
  induction ended with
  | nil => rfl
  | cons actual later ih =>
    rw [ih (fun member => kept (List.mem_cons_of_mem _ member)),NativeReferenceCleanup.endTag_leases _ _ _ actual]
    exact lookup_filter_other _ tag _ (fun same => kept (List.mem_cons.mpr (Or.inl same)))

theorem closeScope_lookup (entered current : State) (tag : Nat) (older : tag < entered.nextTag) :
    NativeByteBorrow.lookup (NativeReferenceCleanup.closeScope entered current).world.leases tag =
      NativeByteBorrow.lookup current.leases tag := by
  apply ends_lookup current _ _ (NativeReferenceCleanup.release_ends current (NativeReferenceCleanup.scopeTags entered current)) tag
  intro member
  have full : tag ∈ NativeReferenceCleanup.scopeTags entered current := by
    rw [NativeReferenceCleanup.release_partition current (NativeReferenceCleanup.scopeTags entered current)]
    exact List.mem_append_left _ member
  simp only [NativeReferenceCleanup.scopeTags,List.mem_map,List.mem_filter,decide_eq_true_eq] at full
  obtain ⟨lease,⟨_,newer⟩,same⟩ := full
  omega

/-- Incoming references survive cleanup even when a younger loan blocks its
completion. No assumption of a successful cleanup is needed. -/
theorem closeScope_resident {world entered : State} {base buffer : Pointer} {capacity length count : Word}
    {mutable : Bool} {reference : Reference}
    (resident : Resident world (.reference mutable reference count) base capacity length buffer)
    (older : reference.tag < entered.nextTag) :
    Resident (NativeReferenceCleanup.closeScope entered world).world (.reference mutable reference count)
      base capacity length buffer := by
  obtain ⟨flag,ref,extent,lease,same,member,registered,baseEq,mode,shape,present,contents⟩ := resident
  cases same
  have frame := NativeReferenceCleanup.release_frame world (NativeReferenceCleanup.scopeTags entered world)
  have pointers := congrArg NativeReferenceMachine.State.pointers frame
  have references := congrArg NativeReferenceMachine.State.references frame
  change (NativeReferenceCleanup.closeScope entered world).world.pointers = world.pointers at pointers
  change (NativeReferenceCleanup.closeScope entered world).world.references = world.references at references
  refine ⟨mutable,reference,count,lease,rfl,?_,?_,baseEq,mode,shape,?_,?_⟩
  · rw [references]; exact member
  · rw [closeScope_lookup entered world reference.tag older]; exact registered
  · rw [pointers]; exact present
  · exact contents.heap_frame (congrArg NativePointerMachine.State.heap pointers)

/-- Granting a fresh child does not replace an older incoming lease. -/
theorem grant_preserves {world next : State} {base buffer : Pointer} {capacity length count : Word}
    {mutable : Bool} {reference : Reference}
    (resident : Resident world (.reference mutable reference count) base capacity length buffer)
    (older : reference.tag < world.nextTag) (parent : Option Nat) (mode : NativeByteBorrow.Mode)
    (pointer : Pointer) (layout : NativeByteMemory.Layout)
    (granted : NativeReferenceMachine.grant world parent mode pointer layout = some next) :
    Resident next (.reference mutable reference count) base capacity length buffer := by
  obtain ⟨flag,ref,extent,lease,same,member,registered,baseEq,leaseMode,shape,present,contents⟩ := resident
  cases same
  obtain ⟨tag,ledger,borrowed,pointers,_,leases,references,_⟩ :=
    NativeReferenceMachine.grant_success world next parent mode pointer layout granted
  obtain ⟨fresh,_,_,leaseEq,_⟩ := NativeByteBorrow.borrow_success (NativeReferenceMachine.ledger world)
    parent mode pointer layout tag ledger borrowed
  change tag = world.nextTag at fresh
  refine ⟨mutable,reference,count,lease,rfl,?_,?_,baseEq,leaseMode,shape,?_,?_⟩
  · rw [references]; exact List.mem_cons_of_mem _ member
  · rw [leases,leaseEq,fresh]
    simp only [NativeByteBorrow.lookup,show world.nextTag ≠ reference.tag by omega,ite_false]
    exact registered
  · rw [pointers]; exact present
  · exact contents.heap_frame (congrArg NativePointerMachine.State.heap pointers)

theorem reborrow_step_preserves {world next : State} {base buffer : Pointer} {capacity length count : Word}
    {mutable : Bool} {reference : Reference}
    (resident : Resident world (.reference mutable reference count) base capacity length buffer)
    (older : reference.tag < world.nextTag) (parent register : Nat) (mode : NativeByteBorrow.Mode)
    (layout : NativeByteMemory.Layout)
    (issued : NativeReferenceMachine.execute world (.reborrow parent register mode layout) = some next) :
    Resident next (.reference mutable reference count) base capacity length buffer := by
  simp only [NativeReferenceMachine.execute,Option.bind_eq_some_iff] at issued
  obtain ⟨parentReference,_,pointer,_,granted⟩ := issued
  exact grant_preserves resident older (some parentReference.tag) mode pointer layout granted

/-- Parent selection binds the borrowed base to the incoming stable reference. -/
theorem vec_parent_base {world : State} {value : Value} {base buffer : Pointer} {capacity length : Word}
    (resident : Resident world value base capacity length buffer)
    (index register : Nat) (selected : Lease)
    (parent : NativeVecReference.parent world value = some (index,register,selected)) :
    selected.pointer = base ∧ world.pointers.registers[register]? = some base := by
  obtain ⟨mutable,reference,count,lease,valueEq,_,registered,pointerEq,_,_,_,_⟩ := resident
  subst value
  cases mutable with
  | false => simp only [NativeVecReference.parent] at parent; cases parent
  | true =>
    simp only [NativeVecReference.parent, Option.bind_eq_bind', registered, Option.bind_some] at parent
    split at parent
    · cases parent
    · split at parent
      next valid => cases parent; exact ⟨pointerEq,by rw [← pointerEq]; exact valid.2.2.2⟩
      next => cases parent

theorem rawvec_parent_base {world : State} {value : Value} {base buffer : Pointer} {capacity length : Word}
    (resident : Resident world value base capacity length buffer)
    (index register : Nat) (selected : Lease)
    (parent : NativeRawVecBorrow.parent world value = some (index,register,selected)) :
    selected.pointer = base ∧ world.pointers.registers[register]? = some base := by
  obtain ⟨mutable,reference,count,lease,valueEq,_,registered,pointerEq,_,_,_,_⟩ := resident
  subst value
  simp only [NativeRawVecBorrow.parent, Option.bind_eq_bind', registered, Option.bind_some] at parent
  split at parent
  · cases parent
  · split at parent
    next valid => cases parent; exact ⟨pointerEq,by rw [← pointerEq]; exact valid.2.2.2⟩
    next => cases parent

/-- Exact state of the successful address step used by the retained reborrow. -/
theorem address_step (world prepared : State) (register : Nat) (base : Pointer)
    (selected : world.pointers.registers[register]? = some base)
    (executed : NativeReferenceMachine.execute world (.raw (.withAddress register base.address)) = some prepared) :
    prepared = {world with pointers := NativePointerMachine.push world.pointers base} := by
  simp only [NativeReferenceMachine.execute, NativeReferenceMachine.rawPermissions, ite_true,
    NativePointerMachine.execute, selected, Option.map_some] at executed
  cases executed
  rfl

/-- Both Vec whole-object and RawVec-field borrows preserve the same header
contents and produce a resident child at the original storage base. -/
theorem vec_reborrow {world next : State} {value output : Value} {base buffer : Pointer} {capacity length : Word}
    (resident : Resident world value base capacity length buffer) (target : NativeVecReference.Target)
    (borrowed : NativeVecReference.reborrow world value target = .value output next) :
    Resident next output base capacity length buffer := by
  have contents := resident
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,observed⟩ := contents
  obtain ⟨index,register,lease,pointer,prepared,parent,shifted,address,issued,outputEq⟩ :=
    NativeVecReference.reborrow_success world next value output target borrowed
  obtain ⟨baseEq,selected⟩ := vec_parent_base resident index register lease parent
  have pointerEq : pointer = base := by
    have offset : target.offset = 0 := by cases target <;> rfl
    rw [baseEq,offset,pointerAt_zero] at shifted
    exact (Option.some.inj shifted).symm
  subst pointer
  have preparedEq := address_step world prepared register base selected address
  rw [preparedEq] at issued outputEq
  simp only [NativeReferenceMachine.execute, NativePointerMachine.push, List.getElem?_cons_zero,
    Option.bind_some, Option.bind_eq_some_iff] at issued
  obtain ⟨reference,_,granted⟩ := issued
  rw [outputEq]
  apply grant_resident {world with pointers := NativePointerMachine.push world.pointers base} next
    (some reference.tag) true base buffer capacity length target.count target.layout
  · cases target
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr ⟨rfl,rfl⟩
  · exact List.mem_cons_self
  · exact observed
  · exact granted

/-- The shared RawVec whole-object borrow changes the loan, not its buffer. -/
theorem rawvec_reborrow {world next : State} {value output : Value} {base buffer : Pointer} {capacity length : Word}
    (resident : Resident world value base capacity length buffer)
    (borrowed : NativeRawVecBorrow.reborrow world value .whole = .value output next) :
    Resident next output base capacity length buffer := by
  have contents := resident
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,observed⟩ := contents
  obtain ⟨index,register,lease,pointer,prepared,parent,shifted,address,issued,outputEq⟩ :=
    NativeRawVecBorrow.reborrow_success world next value output .whole borrowed
  obtain ⟨baseEq,selected⟩ := rawvec_parent_base resident index register lease parent
  have pointerEq : pointer = base := by
    rw [baseEq,show NativeRawVecBorrow.Target.whole.offset = 0 from rfl,pointerAt_zero] at shifted
    exact (Option.some.inj shifted).symm
  subst pointer
  have preparedEq := address_step world prepared register base selected address
  rw [preparedEq] at issued outputEq
  simp only [NativeReferenceMachine.execute, NativePointerMachine.push, List.getElem?_cons_zero,
    Option.bind_some, Option.bind_eq_some_iff] at issued
  obtain ⟨reference,_,granted⟩ := issued
  rw [outputEq]
  exact grant_resident {world with pointers := NativePointerMachine.push world.pointers base} next
    (some reference.tag) false base buffer capacity length 2 ⟨16,8⟩ (Or.inr ⟨rfl,rfl⟩)
    List.mem_cons_self observed granted

/-- Reservation keeps the old reference resident and binds its selected base. -/
theorem rawvec_reserve {world prepared : State} {value : Value} {base buffer : Pointer} {capacity length : Word}
    (resident : Resident world value base capacity length buffer) (reservation : NativeRawVecMutBorrow.Reservation)
    (reserved : NativeRawVecMutBorrow.reserve world value = .value reservation prepared) :
    reservation.pointer = base ∧ Resident prepared value base capacity length buffer := by
  obtain ⟨index,register,lease,reference,count,_,parent,address,_,reservationEq⟩ :=
    NativeRawVecMutBorrow.reserve_success world prepared value reservation reserved
  obtain ⟨baseEq,selected⟩ := rawvec_parent_base resident index register lease parent
  rw [baseEq] at address
  have preparedEq := address_step world prepared register base selected address
  refine ⟨by rw [reservationEq]; exact baseEq,?_⟩
  apply resident.reframe
  · rw [preparedEq]; rfl
  · rw [preparedEq]
  · rw [preparedEq]
  · intro pointer member
    rw [preparedEq]
    exact List.mem_cons_of_mem _ member

theorem rawvec_activate {world next : State} {value output : Value} {base buffer : Pointer} {capacity length : Word}
    (resident : Resident world value base capacity length buffer) (reservation : NativeRawVecMutBorrow.Reservation)
    (pointerEq : reservation.pointer = base)
    (activated : NativeRawVecMutBorrow.activate world reservation = .value output next) :
    Resident next output base capacity length buffer := by
  have selected : world.pointers.registers[world.pointers.registers.idxOf reservation.pointer]? = some reservation.pointer := by
    simp only [NativeRawVecMutBorrow.activate] at activated
    split at activated
    next valid => exact valid.2
    next => cases activated
  obtain ⟨issued,outputEq⟩ := NativeRawVecMutBorrow.activate_success world next reservation output activated
  simp only [NativeReferenceMachine.execute, selected, Option.bind_some, Option.bind_eq_some_iff] at issued
  obtain ⟨reference,_,granted⟩ := issued
  rw [pointerEq] at granted
  obtain ⟨_,_,_,_,_,_,_,_,_,_,member,contents⟩ := resident
  rw [outputEq]
  exact grant_resident world next (some reference.tag) true base buffer capacity length 2 ⟨16,8⟩
    (Or.inr ⟨rfl,rfl⟩) member contents granted

theorem rawvec_immediate {world next : State} {value output : Value} {base buffer : Pointer} {capacity length : Word}
    (resident : Resident world value base capacity length buffer)
    (borrowed : NativeRawVecMutBorrow.immediate world value = .value output next) :
    Resident next output base capacity length buffer := by
  cases reserved : NativeRawVecMutBorrow.reserve world value with
  | invalid prepared => simp only [NativeRawVecMutBorrow.immediate, reserved] at borrowed; cases borrowed
  | value reservation prepared =>
    obtain ⟨pointerEq,carried⟩ := rawvec_reserve resident reservation reserved
    exact rawvec_activate carried reservation pointerEq (by simpa only [NativeRawVecMutBorrow.immediate, reserved] using borrowed)

theorem pointer_access_preserves {world next : State} {input : Value} {base buffer pointer : Pointer} {capacity length : Word}
    (resident : Resident world input base capacity length buffer) (index : Nat)
    (read : NativeRawVecFields.pointerAccess world index = .value pointer next) :
    Resident next input base capacity length buffer := by
  cases actual : NativeReferenceMachine.execute world (.access index 8 .loadPointer) with
  | none => simp only [NativeRawVecFields.pointerAccess, actual] at read; cases read
  | some changed =>
    cases found : changed.pointers.registers[0]? with
    | none => simp only [NativeRawVecFields.pointerAccess, actual, found] at read; cases read
    | some loaded =>
      simp only [NativeRawVecFields.pointerAccess, actual, found] at read
      split at read
      · cases read; exact access_resident resident index 8 .loadPointer rfl actual
      · cases read

theorem capacity_access_preserves {world next : State} {input : Value} {base buffer : Pointer} {capacity length value : Word}
    (resident : Resident world input base capacity length buffer) (index : Nat)
    (read : NativeRawVecFields.capacityAccess world index = .value value next) :
    Resident next input base capacity length buffer := by
  cases actual : NativeReferenceMachine.execute world (.access index 0 (.read 8 8)) with
  | none => simp only [NativeRawVecFields.capacityAccess, actual] at read; cases read
  | some changed =>
    cases decoded : changed.outputs[0]? >>= NativeWord64Memory.decode with
    | none => simp only [NativeRawVecFields.capacityAccess, actual, decoded] at read; cases read
    | some word =>
      simp only [NativeRawVecFields.capacityAccess, actual, decoded] at read
      split at read
      · cases read; exact access_resident resident index 0 (.read 8 8) rfl actual
      · cases read

/-- The child reference reads the original buffer, even after its index changes. -/
theorem pointer_access {world next : State} {base buffer pointer : Pointer} {capacity length count : Word}
    {mutable : Bool} {reference : Reference}
    (resident : Resident world (.reference mutable reference count) base capacity length buffer)
    (index : Nat) (selected : world.references[index]? = some reference)
    (read : NativeRawVecFields.pointerAccess world index = .value pointer next) : pointer = buffer := by
  obtain ⟨mutableFlag,ref,extent,lease,same,_,registered,baseEq,_,_,_,contents⟩ := resident
  cases same
  cases actual : NativeReferenceMachine.execute world (.access index 8 .loadPointer) with
  | none => simp only [NativeRawVecFields.pointerAccess, actual] at read; cases read
  | some changed =>
    cases found : changed.pointers.registers[0]? with
    | none => simp only [NativeRawVecFields.pointerAccess, actual, found] at read; cases read
    | some loaded =>
      simp only [NativeRawVecFields.pointerAccess, actual, found] at read
      split at read
      · cases read
        obtain ⟨chosen,source,slot,value,residentRef,sourceLease,shifted,stored,registers,_⟩ :=
          NativeResidentVec.access_pointer_observation world next index 8 actual
        have refEq := Option.some.inj (residentRef.symm.trans selected)
        subst chosen
        have leaseEq := Option.some.inj (sourceLease.symm.trans registered)
        subst source
        rw [baseEq] at shifted
        have observed := contents.pointerStored
        rw [shifted,Option.bind_some,stored] at observed
        rw [registers,List.getElem?_cons_zero] at found
        exact (Option.some.inj found).symm.trans (Option.some.inj observed)
      · cases read

theorem capacity_access {world next : State} {base buffer : Pointer} {capacity length count value : Word}
    {mutable : Bool} {reference : Reference}
    (resident : Resident world (.reference mutable reference count) base capacity length buffer)
    (index : Nat) (selected : world.references[index]? = some reference)
    (read : NativeRawVecFields.capacityAccess world index = .value value next) : value = capacity := by
  obtain ⟨mutableFlag,ref,extent,lease,same,_,registered,baseEq,_,_,_,contents⟩ := resident
  cases same
  cases actual : NativeReferenceMachine.execute world (.access index 0 (.read 8 8)) with
  | none => simp only [NativeRawVecFields.capacityAccess, actual] at read; cases read
  | some changed =>
    cases decoded : changed.outputs[0]? >>= NativeWord64Memory.decode with
    | none => simp only [NativeRawVecFields.capacityAccess, actual, decoded] at read; cases read
    | some word =>
      simp only [NativeRawVecFields.capacityAccess, actual, decoded] at read
      split at read
      · cases read
        obtain ⟨chosen,source,slot,residentRef,sourceLease,shifted,stored⟩ :=
          NativeResidentVec.access_word_observation world next index 0 value actual decoded
        have refEq := Option.some.inj (residentRef.symm.trans selected)
        subst chosen
        have leaseEq := Option.some.inj (sourceLease.symm.trans registered)
        subst source
        rw [baseEq] at shifted
        have observed := contents.capacityStored
        rw [shifted,Option.bind_some,stored] at observed
        exact Option.some.inj observed
      · cases read

theorem rawvec_pointer {world next : State} {input output : Value} {base buffer : Pointer} {capacity length : Word}
    (resident : Resident world input base capacity length buffer)
    (read : NativeRawVecReference.eval world input .pointer = .value output next) :
    output = .raw ⟨buffer,none⟩ := by
  have original := resident
  obtain ⟨mutable,reference,count,lease,valueEq,_⟩ := resident
  subst input
  cases mutable with
  | true => cases read
  | false =>
    cases counted : NativeRawVecReference.objectOfCount count with
    | none => simp only [NativeRawVecReference.eval, counted] at read; cases read
    | some object =>
      cases resolved : NativeRawVecReference.resolve world reference object with
      | none => simp only [NativeRawVecReference.eval, counted, resolved] at read; cases read
      | some index =>
        have selected := (NativeRawVecReference.resolve_success world reference object index resolved).2.1
        cases actual : NativeRawVecFields.pointerAccess world index with
        | invalid changed => simp only [NativeRawVecReference.eval, counted, resolved, actual] at read; cases read
        | value pointer changed =>
          have same := pointer_access original index selected actual
          simp only [NativeRawVecReference.eval, counted, resolved, actual] at read
          cases read
          rw [same]

theorem rawvec_capacity {world next : State} {input output : Value} {base buffer : Pointer} {capacity length : Word}
    (resident : Resident world input base capacity length buffer)
    (read : NativeRawVecReference.eval world input .capacity = .value output next) :
    output = .usize capacity := by
  have original := resident
  obtain ⟨mutable,reference,count,lease,valueEq,_⟩ := resident
  subst input
  cases mutable with
  | true => cases read
  | false =>
    cases counted : NativeRawVecReference.objectOfCount count with
    | none => simp only [NativeRawVecReference.eval, counted] at read; cases read
    | some object =>
      cases resolved : NativeRawVecReference.resolve world reference object with
      | none => simp only [NativeRawVecReference.eval, counted, resolved] at read; cases read
      | some index =>
        have selected := (NativeRawVecReference.resolve_success world reference object index resolved).2.1
        cases actual : NativeRawVecFields.capacityAccess world index with
        | invalid changed => simp only [NativeRawVecReference.eval, counted, resolved, actual] at read; cases read
        | value value changed =>
          have same := capacity_access original index selected actual
          simp only [NativeRawVecReference.eval, counted, resolved, actual] at read
          cases read
          rw [same]

/-- A source capacity read carries enough residency for the following read,
without assuming register positions remain fixed. -/
theorem rawvec_capacity_preserves {world next : State} {input output : Value} {base buffer : Pointer} {capacity length : Word}
    (resident : Resident world input base capacity length buffer)
    (read : NativeRawVecReference.eval world input .capacity = .value output next) :
    Resident next input base capacity length buffer := by
  have original := resident
  obtain ⟨mutable,reference,count,lease,valueEq,_⟩ := resident
  subst input
  cases mutable with
  | true => cases read
  | false =>
    cases counted : NativeRawVecReference.objectOfCount count with
    | none => simp only [NativeRawVecReference.eval, counted] at read; cases read
    | some object =>
      cases resolved : NativeRawVecReference.resolve world reference object with
      | none => simp only [NativeRawVecReference.eval, counted, resolved] at read; cases read
      | some index =>
        cases actual : NativeRawVecFields.capacityAccess world index with
        | invalid changed => simp only [NativeRawVecReference.eval, counted, resolved, actual] at read; cases read
        | value value changed =>
          simp only [NativeRawVecReference.eval, counted, resolved, actual] at read
          cases read
          exact capacity_access_preserves original index actual

theorem rawvec_pointer_preserves {world next : State} {input output : Value} {base buffer : Pointer} {capacity length : Word}
    (resident : Resident world input base capacity length buffer)
    (read : NativeRawVecReference.eval world input .pointer = .value output next) :
    Resident next input base capacity length buffer := by
  have original := resident
  obtain ⟨mutable,reference,count,lease,valueEq,_⟩ := resident
  subst input
  cases mutable with
  | true => cases read
  | false =>
    cases counted : NativeRawVecReference.objectOfCount count with
    | none => simp only [NativeRawVecReference.eval, counted] at read; cases read
    | some object =>
      cases resolved : NativeRawVecReference.resolve world reference object with
      | none => simp only [NativeRawVecReference.eval, counted, resolved] at read; cases read
      | some index =>
        cases actual : NativeRawVecFields.pointerAccess world index with
        | invalid changed => simp only [NativeRawVecReference.eval, counted, resolved, actual] at read; cases read
        | value pointer changed =>
          simp only [NativeRawVecReference.eval, counted, resolved, actual] at read
          cases read
          exact pointer_access_preserves original index actual

theorem rawvec_marker (world next : State) (input output : Value)
    (read : NativeRawVecReference.eval world input .marker = .value output next) : output = .unit := by
  cases input with
  | unit => cases read
  | usize word => cases read
  | raw pointer => cases read
  | reference mutable reference count =>
    cases mutable with
    | true => cases read
    | false =>
      cases counted : NativeRawVecReference.objectOfCount count with
      | none => simp only [NativeRawVecReference.eval, counted] at read; cases read
      | some object =>
        cases resolved : NativeRawVecReference.resolve world reference object with
        | none => simp only [NativeRawVecReference.eval, counted, resolved] at read; cases read
        | some index =>
          cases actual : NativeRawVecFields.markerAccess world index with
          | invalid changed => simp only [NativeRawVecReference.eval, counted, resolved, actual] at read; cases read
          | value marker changed =>
            simp only [NativeRawVecReference.eval, counted, resolved, actual] at read
            cases read
            rfl

/-- Canonical caller selection follows from the resident shared view itself. -/
theorem shared_rawvec_decode {world : State} {base buffer : Pointer} {capacity length : Word} {reference : Reference}
    (resident : Resident world (.reference false reference 2) base capacity length buffer) :
    NativeRawVecReference.decode world (world.references.idxOf reference) .inner = some (.reference false reference 2) := by
  obtain ⟨mutable,ref,count,lease,same,member,registered,_,mode,shape,_,_⟩ := resident
  cases same
  have layout : lease.layout = ⟨16,8⟩ := by
    rcases shape with ⟨impossible,_⟩ | ⟨_,layout⟩
    · exact False.elim ((by decide : (2 : Word) ≠ 3) impossible)
    · exact layout
  have selected := NativeRawVecReference.select_complete .inner world (world.references.idxOf reference) reference lease
    (List.getElem?_idxOf member) registered mode layout
  simp only [NativeRawVecReference.decode,selected,Option.map_some,NativeRawVecReference.Object.count]

end FormalProof4FHE.HasteBoots.NativeResidentVecBorrow
