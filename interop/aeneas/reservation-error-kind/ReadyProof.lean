namespace HasteBootsReservationErrorKind
open FormalProof4FHE.HasteBoots
open NativeReferenceMachine (State Reference)
open NativeReservationErrorFields (Kind)

structure Ready (world : State) (index : Nat) (kind : Kind) where
  descriptor : NativeReservationErrorRead.Readable world index kind
  checked : NativeByteRange.checkRange world.pointers.heap.memory descriptor.lease.pointer ⟨16,8⟩ = true

def borrowedWorld (world : State) (parent : Reference) (pointer : NativePointerStorage.Pointer) : State :=
  {world with
    nextTag := world.nextTag+1
    leases := ⟨world.nextTag,some parent.tag,pointer,⟨16,8⟩,.shared⟩ :: world.leases
    references := ⟨world.nextTag⟩ :: world.references
    births := ⟨world.nextTag,some parent.tag,pointer,⟨16,8⟩,.shared⟩ :: world.births}

theorem raw_to_through (world : State) (tag : Nat) (pointer : NativePointerStorage.Pointer)
    (allowed : NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger world) .shared pointer ⟨16,8⟩ = true) :
    NativeByteBorrow.throughAllowed (NativeReferenceMachine.ledger world) tag .shared pointer ⟨16,8⟩ = true := by
  simp only [NativeByteBorrow.throughAllowed,List.all_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  intro lease member
  exact Or.inr (NativeByteBorrow.rawAllowed_selected _ _ _ _ allowed lease member)

theorem descriptor_parent_allowed (world : State) (index : Nat) (kind : Kind)
    (descriptor : NativeReservationErrorRead.Readable world index kind) (valid : NativeReferenceMachine.WellFormed world) :
    NativeByteBorrow.parentAllowed (NativeReferenceMachine.ledger world) (some descriptor.reference.tag) .shared descriptor.lease.pointer ⟨16,8⟩ = true := by
  obtain ⟨member,same⟩ := NativeByteBorrow.lookup_selected world.leases descriptor.reference.tag descriptor.lease descriptor.registered
  have older : descriptor.reference.tag < world.nextTag := by
    have before := (valid.2.1.1 descriptor.lease member).1
    change descriptor.lease.tag < world.nextTag at before
    rw [same] at before
    exact before
  have permitted := raw_to_through world descriptor.reference.tag descriptor.lease.pointer descriptor.allowed
  have registered : NativeByteBorrow.lookup (NativeReferenceMachine.ledger world).leases descriptor.reference.tag = some descriptor.lease := descriptor.registered
  have checked : descriptor.reference.tag < (NativeReferenceMachine.ledger world).nextTag ∧
      (NativeByteBorrow.Mode.shared = .shared ∨ descriptor.lease.mode = .exclusive) ∧
      descriptor.lease.pointer.provenance = descriptor.lease.pointer.provenance ∧
      descriptor.lease.pointer.address.val ≤ descriptor.lease.pointer.address.val ∧
      descriptor.lease.pointer.address.val + 16 ≤ descriptor.lease.pointer.address.val + descriptor.lease.layout.size := by
    refine ⟨older,Or.inl rfl,rfl,Nat.le_refl _,?_⟩
    rw [descriptor.extent]
  simp only [NativeByteBorrow.parentAllowed,registered]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simpa only using decide_eq_true checked,permitted⟩

theorem ready_reborrow (world : State) (index : Nat) (kind : Kind) (ready : Ready world index kind)
    (valid : NativeReferenceMachine.WellFormed world) :
    reborrow world (.scalar (.reference false ready.descriptor.reference 2)) =
      .value (.scalar (.reference false ⟨world.nextTag⟩ 2))
        (borrowedWorld world ready.descriptor.reference ready.descriptor.lease.pointer) := by
  let descriptor := ready.descriptor
  have refFound := List.getElem?_idxOf (List.mem_of_getElem? descriptor.resident)
  have pointerFound := List.getElem?_idxOf descriptor.baseResident
  have parent : NativeRawVecBorrow.parent world (.reference false descriptor.reference 2) =
      some (world.references.idxOf descriptor.reference,world.pointers.registers.idxOf descriptor.lease.pointer,descriptor.lease) := by
    simp [NativeRawVecBorrow.parent,descriptor.registered,descriptor.shared,descriptor.extent,refFound,pointerFound,NativeSliceLLBC.mode]
  have issued := NativeByteBorrowStorage.borrow_complete (NativeReferenceMachine.ledger world) (some descriptor.reference.tag)
    .shared descriptor.lease.pointer ⟨16,8⟩ (descriptor_parent_allowed world index kind descriptor valid) ready.checked
  have step : NativeStorageBorrowMachine.execute world
      (.storageBorrow (some (world.references.idxOf descriptor.reference)) (world.pointers.registers.idxOf descriptor.lease.pointer) .shared ⟨16,8⟩) =
      some (borrowedWorld world descriptor.reference descriptor.lease.pointer) := by
    simp only [NativeStorageBorrowMachine.execute,NativeStorageBorrowMachine.parentTag,refFound,Option.map_some,Option.bind_some,
      pointerFound,NativeStorageBorrowMachine.grant,issued,Option.map_some]
    rfl
  dsimp only [descriptor] at parent step
  simp only [reborrow,parent,step]

theorem borrowed_readable (world : State) (index : Nat) (kind : Kind) (ready : Ready world index kind) :
    Nonempty (NativeReservationErrorRead.Readable (borrowedWorld world ready.descriptor.reference ready.descriptor.lease.pointer) 0 kind) := by
  let descriptor := ready.descriptor
  refine ⟨⟨⟨world.nextTag⟩,⟨world.nextTag,some descriptor.reference.tag,descriptor.lease.pointer,⟨16,8⟩,.shared⟩,
    rfl,?_,rfl,rfl,descriptor.baseResident,?_,descriptor.stored⟩⟩
  · simp [borrowedWorld,NativeByteBorrow.lookup,descriptor]
  · change NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger (borrowedWorld world descriptor.reference descriptor.lease.pointer)) .shared descriptor.lease.pointer ⟨16,8⟩ = true
    simp only [NativeByteBorrow.rawAllowed,NativeReferenceMachine.ledger,borrowedWorld,List.all_cons,Bool.and_eq_true]
    exact ⟨decide_eq_true (Or.inl ⟨rfl,rfl⟩),descriptor.allowed⟩

theorem root_ready_complete (world : State) (index : Nat) (kind : Kind) (ready : Ready world index kind)
    (valid : NativeReferenceMachine.WellFormed world) (kindValid : NativeReservationErrorLocal.Valid kind) :
    ∃ final, rootInvoke world (.scalar (.reference false ready.descriptor.reference 2)) =
      .returned (NativeReservationErrorLocal.kindValue tags kind) final ∧
      authority (borrowedWorld world ready.descriptor.reference ready.descriptor.lease.pointer) final := by
  obtain ⟨descriptor⟩ := borrowed_readable world index kind ready
  obtain ⟨final,called⟩ := NativeReservationErrorRead.getKind_complete tags _ 0 kind descriptor kindValid
  have childReference : descriptor.reference = ⟨world.nextTag⟩ := by
    have found := descriptor.resident
    change some (⟨world.nextTag⟩ : Reference) = some descriptor.reference at found
    exact Option.some.inj found.symm
  rw [childReference] at called
  have getter : invoke (borrowedWorld world ready.descriptor.reference ready.descriptor.lease.pointer)
      (.scalar (.reference false ⟨world.nextTag⟩ 2)) = .returned (NativeReservationErrorLocal.kindValue tags kind) final := by
    rw [getter_equiv]
    rw [called]
    rfl
  have preserved := invoke_authority (borrowedWorld world ready.descriptor.reference ready.descriptor.lease.pointer)
    (.scalar (.reference false ⟨world.nextTag⟩ 2))
  rw [getter] at preserved
  exact ⟨final,root_call_returns world _ final ready.descriptor.reference kind kindValid (ready_reborrow world index kind ready valid) getter,preserved⟩

theorem grant_checked (world next : State) (pointer : NativePointerStorage.Pointer) (index : Nat) (kind : Kind)
    (granted : NativeStorageBorrowMachine.grant world none .shared pointer ⟨16,8⟩ = some next)
    (descriptor : NativeReservationErrorRead.Readable next index kind)
    (atZero : index = 0) : NativeByteRange.checkRange next.pointers.heap.memory descriptor.lease.pointer ⟨16,8⟩ = true := by
  subst index
  obtain ⟨tag,ledger,actual,pointers,_,leases,references,_⟩ := NativeStorageBorrowMachine.grant_success world next none .shared pointer ⟨16,8⟩ granted
  obtain ⟨_,_,_,newLeases,_,checked⟩ := NativeByteBorrowStorage.borrow_success _ _ _ _ _ _ _ actual
  have refEq : descriptor.reference = ⟨tag⟩ := by
    have found := descriptor.resident
    rw [references] at found
    exact Option.some.inj found.symm
  have lookup : NativeByteBorrow.lookup next.leases descriptor.reference.tag = some ⟨tag,none,pointer,⟨16,8⟩,.shared⟩ := by
    rw [refEq,leases,newLeases]
    simp [NativeByteBorrow.lookup]
  have leaseEq : descriptor.lease = ⟨tag,none,pointer,⟨16,8⟩,.shared⟩ := Option.some.inj (descriptor.registered.symm.trans lookup)
  rw [leaseEq,pointers]
  exact checked

theorem snapshot_ready (world next : State) (base : NativePointerStorage.Address) (value result : NativeRecordValues.Value)
    (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue tags world base value = .value result next) :
    ∃ kind, value = NativeReservationErrorLocal.encode tags kind ∧ NativeReservationErrorLocal.Valid kind ∧
      ∃ ready : Ready next 0 kind, result = .scalar (.reference false ready.descriptor.reference 2) := by
  obtain ⟨kind,decoded,kindValid,⟨descriptor⟩⟩ := NativeReservationErrorRead.snapshot_readable tags world next base value result valid executed
  obtain ⟨_,_,written,_,_,_,borrowing⟩ := NativeReservationErrorLocal.snapshot_trace tags world next base value result executed
  simp only [NativeStorageBorrowMachine.execute,NativeStorageBorrowMachine.parentTag,Option.bind_some,Option.bind_eq_some_iff] at borrowing
  obtain ⟨pointer,_,granted⟩ := borrowing
  have checked := grant_checked written next pointer 0 kind granted descriptor rfl
  obtain ⟨_,reference,_,_,selected,resultEq⟩ := NativeReservationErrorLocal.snapshotValue_success tags world next base value result executed
  obtain ⟨_,found,_⟩ := NativeRawVecFields.select_success next 0 reference selected
  have same : reference = descriptor.reference := Option.some.inj (found.symm.trans descriptor.resident)
  subst reference
  exact ⟨kind,NativeReservationErrorLocal.decode_sound tags value kind decoded,kindValid,⟨descriptor,checked⟩,resultEq⟩

end HasteBootsReservationErrorKind
