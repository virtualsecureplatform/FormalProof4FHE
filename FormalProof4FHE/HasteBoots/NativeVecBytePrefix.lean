module
public import FormalProof4FHE.HasteBoots.NativeByteTraversalCompleteness
@[expose] public section

/-! Checked Vec byte-prefix preparation from resident fields, initialized
elements and explicit physical separation. Native Rust construction, compiler
and lifetime correspondence remain separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeVecBytePrefix
open NativeReferenceMachine (State Reference)
open NativeByteBorrow (Lease)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeResidentVec (Descriptor InitializedElements)
open NativeBorrowFrontier (ExclusiveFrontier)

/-- Separation covers allocation capacity, independently of initialization. -/
def Available (world : State) (pointer : Pointer) (size : Nat) : Prop :=
  ∀ lease ∈ world.leases, ¬ NativeByteBorrow.Overlap pointer ⟨size,1⟩ lease.pointer lease.layout

theorem Available.mono {world : State} {pointer : Pointer} {size requested : Nat}
    (available : Available world pointer size) (bounded : requested ≤ size) : Available world pointer requested := by
  intro lease member overlapping
  apply available lease member
  unfold NativeByteBorrow.Overlap at *
  dsimp only at overlapping ⊢
  omega

theorem root_frontier (before after : NativeByteBorrow.State) (pointer : Pointer) (layout : NativeByteMemory.Layout) (tag : Nat)
    (borrowed : NativeByteBorrow.borrow before none .exclusive pointer layout = some (tag,after)) :
    ExclusiveFrontier after ⟨tag,none,pointer,layout,.exclusive⟩ := by
  obtain ⟨_,_,_,leases,_,_⟩ := NativeByteBorrow.borrow_success before none .exclusive pointer layout tag after borrowed
  refine ⟨rfl,?_,?_⟩
  · simp only [leases,NativeByteBorrow.lookup,ite_true]
  · intro lease member
    rw [leases] at member
    rcases List.mem_cons.mp member with same | old
    · exact Or.inl (congrArg Lease.tag same)
    · exact Or.inr (Or.inr (NativeByteBorrow.root_exclusive_separated before pointer layout tag after borrowed lease old))

/-- The actual raw-slice issuance creates the initialized, available resident
slice required by the unbounded traversal theorem. -/
theorem raw_issue_ready (world : State) (pointer : Pointer) (length : Word)
    (reachable : NativeReferenceMachine.Reachable world) (resident : pointer ∈ world.pointers.registers)
    (available : Available world pointer length.val) (bytes : List NativeByteMemory.Byte)
    (loaded : NativeByteRange.loadRange world.pointers.heap.memory pointer ⟨length.val,1⟩ = some bytes) :
    ∃ next, NativeSliceLLBC.issue world true (.raw ⟨pointer,some length⟩) .byte =
      some (.reference true ⟨world.nextTag⟩ length,next) ∧
      NativeByteTraversalCompleteness.Ready next ⟨⟨world.nextTag⟩,length⟩ := by
  have allowed : NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger world) .exclusive pointer ⟨length.val,1⟩ = true := by
    apply List.all_eq_true.mpr
    intro lease member
    exact decide_eq_true (Or.inr (available lease member))
  let ledger : NativeByteBorrow.State := ⟨world.pointers.heap.memory,world.nextTag + 1,
    ⟨world.nextTag,none,pointer,⟨length.val,1⟩,.exclusive⟩ :: world.leases⟩
  have borrowed : NativeByteBorrow.borrow (NativeReferenceMachine.ledger world) none .exclusive pointer ⟨length.val,1⟩ =
      some (world.nextTag,ledger) := by
    rw [NativeByteBorrow.borrow,NativeByteBorrow.parentAllowed,allowed]
    simp only [ite_true,NativeReferenceMachine.ledger,loaded,Option.map_some,ledger]
  let next : State := ⟨world.pointers,world.nextTag + 1,ledger.leases,⟨world.nextTag⟩ :: world.references,
    ⟨world.nextTag,none,pointer,⟨length.val,1⟩,.exclusive⟩ :: world.births,world.outputs⟩
  have granted : NativeReferenceMachine.grant world none .exclusive pointer ⟨length.val,1⟩ = some next := by
    rw [NativeReferenceMachine.grant,borrowed]
    rfl
  have issued : NativeSliceLLBC.issue world true (.raw ⟨pointer,some length⟩) .byte =
      some (.reference true ⟨world.nextTag⟩ length,next) := by
    simp only [NativeSliceLLBC.issue,List.getElem?_idxOf resident,ite_true,NativeReferenceMachine.execute,
      Option.bind_some,NativeSliceLLBC.mode,NativeSliceLLBC.layout,NativeSliceLLBC.Element.width,Nat.one_mul,
      granted,Option.map_some]
  refine ⟨next,issued,?_,⟨world.nextTag,none,pointer,⟨length.val,1⟩,.exclusive⟩,?_,?_,resident,rfl,?_,bytes,loaded⟩
  · exact NativeSliceLLBC.reference_runs_reachable world next reachable (NativeSliceLLBC.issue_projects _ _ _ _ _ issued)
  · simp only [next,ledger,NativeByteBorrow.lookup,ite_true]
  · exact List.mem_cons_self
  · exact root_frontier (NativeReferenceMachine.ledger world) ledger pointer ⟨length.val,1⟩ world.nextTag borrowed

theorem descriptor_issue_ready {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world) (initialized : InitializedElements descriptor)
    (resident : descriptor.buffer ∈ world.pointers.registers)
    (available : Available world descriptor.buffer descriptor.capacity.val) :
    ∃ next, NativeSliceLLBC.issue world true (.raw ⟨descriptor.buffer,some descriptor.length⟩) .byte =
      some (.reference true ⟨world.nextTag⟩ descriptor.length,next) ∧
      NativeByteTraversalCompleteness.Ready next ⟨⟨world.nextTag⟩,descriptor.length⟩ := by
  obtain ⟨bytes,loaded⟩ := initialized
  exact raw_issue_ready world descriptor.buffer descriptor.length reachable resident (available.mono descriptor.lengthBound) bytes loaded

theorem header_parent (world : State) (reference : Reference) (lease : Lease)
    (registered : NativeByteBorrow.lookup world.leases reference.tag = some lease)
    (referenceResident : reference ∈ world.references) (pointerResident : lease.pointer ∈ world.pointers.registers)
    (exclusive : lease.mode = .exclusive) (shape : lease.layout = ⟨24,8⟩) :
    NativeVecReference.parent world (.reference true reference 3) =
      some (world.references.idxOf reference,world.pointers.registers.idxOf lease.pointer,lease) := by
  simp [NativeVecReference.parent,registered,exclusive,shape,List.getElem?_idxOf referenceResident,List.getElem?_idxOf pointerResident]

theorem field_contained {world : State} {index : Nat} (descriptor : Descriptor world index)
    (offset : Nat) (slot : Pointer) (shifted : NativeByteRange.pointerAt descriptor.lease.pointer offset = some slot)
    (bounded : offset + 8 ≤ 24) : NativeBorrowFrontier.Contained slot ⟨8,8⟩ descriptor.lease := by
  obtain ⟨address,origin⟩ := NativeByteRange.pointerAt_fields _ _ _ shifted
  refine ⟨origin,?_,?_⟩
  · rw [address]; omega
  · rw [descriptor.extent]
    change slot.address.val + 8 ≤ descriptor.lease.pointer.address.val + 24
    rw [address]; omega

theorem field_allowed {world : State} {index : Nat} (descriptor : Descriptor world index)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger world))
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease)
    (offset : Nat) (slot : Pointer) (shifted : NativeByteRange.pointerAt descriptor.lease.pointer offset = some slot)
    (bounded : offset + 8 ≤ 24) :
    NativeByteBorrow.throughAllowed (NativeReferenceMachine.ledger world) descriptor.reference.tag .shared slot ⟨8,8⟩ = true := by
  have allowed := NativeBorrowFrontier.through_allowed _ valid descriptor.lease frontier .shared slot ⟨8,8⟩
    (field_contained descriptor offset slot shifted bounded)
  have tag := (NativeByteBorrow.lookup_selected _ _ _ descriptor.registered).2
  simpa only [tag] using allowed

def pointerWorld {world : State} {index : Nat} (descriptor : Descriptor world index) : State :=
  {world with pointers := NativePointerMachine.push (NativePointerMachine.push world.pointers descriptor.pointerSlot) descriptor.buffer}

def lengthWorld {world : State} {index : Nat} (descriptor : Descriptor world index) : State :=
  ⟨NativePointerMachine.push (pointerWorld descriptor).pointers descriptor.lengthSlot,world.nextTag,world.leases,
    world.references,world.births,NativeWord64Memory.encode descriptor.length :: world.outputs⟩

theorem pointer_execute {world : State} {index : Nat} (descriptor : Descriptor world index)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger world))
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    NativeReferenceMachine.execute world (.access (world.references.idxOf descriptor.reference) 8 .loadPointer) =
      some (pointerWorld descriptor) := by
  have allowed := field_allowed descriptor valid frontier 8 descriptor.pointerSlot descriptor.pointerAt (by decide)
  have bounded : 8 + 8 ≤ descriptor.lease.layout.size := by rw [descriptor.extent]; decide
  have scratch : (⟨descriptor.pointerSlot.address,descriptor.lease.pointer.provenance⟩ : Pointer) = descriptor.pointerSlot := by
    rw [← (NativeByteRange.pointerAt_fields _ _ _ descriptor.pointerAt).2]
  let prepared := NativePointerMachine.push world.pointers descriptor.pointerSlot
  have preparation : NativeReferenceMachine.prepare world descriptor.lease.pointer descriptor.pointerSlot.address = some prepared := by
    simp only [NativeReferenceMachine.prepare,descriptor.baseResident,ite_true,NativePointerMachine.execute,Option.map_some,scratch]
    rfl
  simp only [NativeReferenceMachine.execute,NativeReferenceMachine.access,
    List.getElem?_idxOf (List.mem_of_getElem? descriptor.resident),Option.bind_some,descriptor.registered,
    NativeReferenceMachine.Access.mode,NativeReferenceMachine.Access.layout,true_or,bounded,and_self,ite_true,
    descriptor.pointerAt,allowed,preparation,NativeReferenceMachine.perform,NativePointerMachine.execute,prepared,
    NativePointerMachine.push,List.getElem?_cons_zero,descriptor.pointerStored,Option.map_some,
    NativeReferenceMachine.setPointers,pointerWorld]

theorem pointer_field_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger world))
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    NativeVecReference.readField world (.reference true descriptor.reference 3) .pointer =
      .value (.raw ⟨descriptor.buffer,none⟩) (pointerWorld descriptor) := by
  have selected := header_parent world descriptor.reference descriptor.lease descriptor.registered
    (List.mem_of_getElem? descriptor.resident) (List.mem_of_getElem? descriptor.baseResident) descriptor.exclusive descriptor.extent
  simp only [NativeVecReference.readField,selected,NativeRawVecFields.pointerAccess,pointer_execute descriptor valid frontier,
    pointerWorld,NativePointerMachine.push,List.getElem?_cons_zero]
  rw [ite_eq_left descriptor.nonnull]

theorem length_execute {world : State} {index : Nat} (descriptor : Descriptor world index)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger world))
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    NativeReferenceMachine.execute (pointerWorld descriptor)
      (.access (world.references.idxOf descriptor.reference) 16 (.read 8 8)) = some (lengthWorld descriptor) := by
  have allowed := field_allowed descriptor valid frontier 16 descriptor.lengthSlot descriptor.lengthAt (by decide)
  have bounded : 16 + 8 ≤ descriptor.lease.layout.size := by rw [descriptor.extent]
  have scratch : (⟨descriptor.lengthSlot.address,descriptor.lease.pointer.provenance⟩ : Pointer) = descriptor.lengthSlot := by
    rw [← (NativeByteRange.pointerAt_fields _ _ _ descriptor.lengthAt).2]
  have baseMember : descriptor.lease.pointer ∈ (pointerWorld descriptor).pointers.registers :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_getElem? descriptor.baseResident))
  let prepared := NativePointerMachine.push (pointerWorld descriptor).pointers descriptor.lengthSlot
  have preparation : NativeReferenceMachine.prepare (pointerWorld descriptor) descriptor.lease.pointer descriptor.lengthSlot.address = some prepared := by
    simp only [NativeReferenceMachine.prepare,List.getElem?_idxOf baseMember,ite_true,NativePointerMachine.execute,Option.map_some,scratch]
    rfl
  have selected : (pointerWorld descriptor).references[world.references.idxOf descriptor.reference]? = some descriptor.reference :=
    List.getElem?_idxOf (List.mem_of_getElem? descriptor.resident)
  have registered : NativeByteBorrow.lookup (pointerWorld descriptor).leases descriptor.reference.tag = some descriptor.lease := descriptor.registered
  have loaded := (NativeWord64Memory.load_iff_bytes _ _ _).mp descriptor.lengthStored
  change NativeByteBorrow.throughAllowed (NativeReferenceMachine.ledger (pointerWorld descriptor)) descriptor.reference.tag .shared descriptor.lengthSlot ⟨8,8⟩ = true at allowed
  rw [NativeReferenceMachine.execute,NativeReferenceMachine.access,selected]
  simp only [Option.bind_some,registered,NativeReferenceMachine.Access.mode,NativeReferenceMachine.Access.layout,
    true_or,bounded,and_self,ite_true,descriptor.lengthAt]
  simp only [allowed,ite_true,preparation,Option.bind_some]
  simp only [NativeReferenceMachine.perform,prepared,NativePointerMachine.push,
    pointerWorld,loaded,Option.map_some,lengthWorld]

theorem length_field_complete {world : State} {index : Nat} (descriptor : Descriptor world index)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger world))
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    NativeVecReference.readField (pointerWorld descriptor) (.reference true descriptor.reference 3) .length =
      .value (.usize descriptor.length) (lengthWorld descriptor) := by
  have baseMember : descriptor.lease.pointer ∈ (pointerWorld descriptor).pointers.registers :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_getElem? descriptor.baseResident))
  have selected := header_parent (pointerWorld descriptor) descriptor.reference descriptor.lease descriptor.registered
    (List.mem_of_getElem? descriptor.resident) baseMember descriptor.exclusive descriptor.extent
  change NativeVecReference.parent (pointerWorld descriptor) (.reference true descriptor.reference 3) =
    some (world.references.idxOf descriptor.reference,(pointerWorld descriptor).pointers.registers.idxOf descriptor.lease.pointer,descriptor.lease) at selected
  simp only [NativeVecReference.readField,selected,NativeVecReference.lengthAccess,
    length_execute descriptor valid frontier,lengthWorld,List.getElem?_cons_zero,Option.bind_eq_bind',Option.bind_some,NativeWord64Memory.decode_encode]

/-- Reading the actual pointer and length fields supplies a complete buffer
register and leaves the initialized-element and separation facts unchanged. -/
theorem fields_issue_ready {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world) (initialized : InitializedElements descriptor)
    (available : Available world descriptor.buffer descriptor.capacity.val)
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    ∃ next, NativeSliceLLBC.issue (lengthWorld descriptor) true (.raw ⟨descriptor.buffer,some descriptor.length⟩) .byte =
      some (.reference true ⟨world.nextTag⟩ descriptor.length,next) ∧
      NativeByteTraversalCompleteness.Ready next ⟨⟨world.nextTag⟩,descriptor.length⟩ := by
  have valid := NativeReferenceMachine.reachable_wellFormed world reachable
  have first := NativeReferenceMachine.Reachable.step reachable _ (pointer_execute descriptor valid.2.1 frontier)
  have second := NativeReferenceMachine.Reachable.step first _ (length_execute descriptor valid.2.1 frontier)
  have resident : descriptor.buffer ∈ (lengthWorld descriptor).pointers.registers := List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨bytes,loaded⟩ := initialized
  exact raw_issue_ready (lengthWorld descriptor) descriptor.buffer descriptor.length second resident
    (available.mono descriptor.lengthBound) bytes loaded


theorem lengthWorld_reachable {world : State} {index : Nat} (descriptor : Descriptor world index)
    (reachable : NativeReferenceMachine.Reachable world)
    (frontier : ExclusiveFrontier (NativeReferenceMachine.ledger world) descriptor.lease) :
    NativeReferenceMachine.Reachable (lengthWorld descriptor) := by
  have valid := NativeReferenceMachine.reachable_wellFormed world reachable
  have first : NativeReferenceMachine.Reachable (pointerWorld descriptor) :=
    .step reachable _ (pointer_execute descriptor valid.2.1 frontier)
  exact .step first _ (length_execute descriptor valid.2.1 frontier)

/-- The real field-read scope has created no loans; its cutoff therefore ends
nothing and retains the complete post-read world. -/
theorem length_scope {world : State} {index : Nat} (descriptor : Descriptor world index)
    (valid : NativeByteBorrow.LedgerValid (NativeReferenceMachine.ledger world)) :
    NativeReferenceCleanup.closeScope world (lengthWorld descriptor) = ⟨lengthWorld descriptor,[],[]⟩ := by
  have noNew : world.leases.filter (fun lease => decide (world.nextTag ≤ lease.tag)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro lease member
    have age : lease.tag < world.nextTag := (valid.1 lease member).1
    simpa only [decide_eq_true_eq] using (show ¬ world.nextTag ≤ lease.tag by omega)
  simp only [NativeReferenceCleanup.closeScope,NativeReferenceCleanup.scopeTags,lengthWorld,noNew,List.map_nil,NativeReferenceCleanup.release]

end FormalProof4FHE.HasteBoots.NativeVecBytePrefix
