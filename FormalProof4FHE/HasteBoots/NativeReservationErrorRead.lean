module
public import FormalProof4FHE.HasteBoots.NativeReservationErrorLocal
public import FormalProof4FHE.HasteBoots.NativeBorrowFrontier
@[expose] public section

/-! Read completeness for the actual shared loan issued by an error-local
snapshot. Byte residency and alias permission are separate hypotheses, both
derived from execution. Native stack, type and lifetime refinement remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeReservationErrorRead
open NativeReferenceMachine (State Reference)
open NativePointerStorage (Pointer)
open NativeByteBorrow (Lease)
open NativeReservationErrorFields (Kind wordAccess)
open NativeReservationErrorLocal (Stored Valid Tags)
open NativeWord64Memory (Word)

structure Readable (world : State) (index : Nat) (kind : Kind) where
  reference : Reference
  lease : Lease
  resident : world.references[index]? = some reference
  registered : NativeByteBorrow.lookup world.leases reference.tag = some lease
  shared : lease.mode = .shared
  extent : lease.layout = ⟨16,8⟩
  baseResident : lease.pointer ∈ world.pointers.registers
  allowed : NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger world) .shared lease.pointer ⟨16,8⟩ = true
  stored : Stored world.pointers.heap.memory lease.pointer kind

theorem subrange_allowed (world : State) (reference : Reference) (lease : Lease)
    (allowed : NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger world) .shared lease.pointer ⟨16,8⟩ = true)
    (offset : Nat) (slot : Pointer) (bounded : offset + 8 ≤ 16)
    (shifted : NativeByteRange.pointerAt lease.pointer offset = some slot) :
    NativeByteBorrow.throughAllowed (NativeReferenceMachine.ledger world) reference.tag .shared slot ⟨8,8⟩ = true := by
  have fields := NativeByteRange.pointerAt_fields lease.pointer offset slot shifted
  have contained : NativeBorrowFrontier.Contained slot ⟨8,8⟩
      ⟨0,none,lease.pointer,⟨16,8⟩,.shared⟩ := by
    refine ⟨fields.2,?_,?_⟩ <;> dsimp only <;> have position := fields.1 <;> omega
  simp only [NativeByteBorrow.throughAllowed,List.all_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  intro other member
  have compatible := NativeByteBorrow.rawAllowed_selected _ _ _ _ allowed other member
  rcases compatible with modes | separate
  · exact Or.inr (Or.inl modes)
  · exact Or.inr (Or.inr (NativeBorrowFrontier.disjoint_subrange _ other slot ⟨8,8⟩ contained separate))

theorem word_complete (world : State) (index : Nat) (kind : Kind) (descriptor : Readable world index kind)
    (offset : Nat) (slot : Pointer) (word : Word) (bounded : offset + 8 ≤ 16)
    (shifted : NativeByteRange.pointerAt descriptor.lease.pointer offset = some slot)
    (loaded : NativeWord64Memory.load world.pointers.heap.memory slot = some word) :
    ∃ next, wordAccess world index offset = .value word next ∧ Nonempty (Readable next index kind) := by
  obtain ⟨bytes,bytesLoaded,decoded⟩ := Option.bind_eq_some_iff.mp loaded
  let prepared := NativePointerMachine.push world.pointers slot
  let next : State := {world with pointers := prepared,outputs := bytes :: world.outputs}
  have provenance := (NativeByteRange.pointerAt_fields descriptor.lease.pointer offset slot shifted).2
  have scratch : (⟨slot.address,descriptor.lease.pointer.provenance⟩ : Pointer) = slot := by rw [← provenance]
  have preparation : NativeReferenceMachine.prepare world descriptor.lease.pointer slot.address = some prepared := by
    simp only [NativeReferenceMachine.prepare,List.getElem?_idxOf descriptor.baseResident,ite_true,
      NativePointerMachine.execute,Option.map_some,scratch]
    rfl
  have permission := subrange_allowed world descriptor.reference descriptor.lease descriptor.allowed offset slot bounded shifted
  have bound : offset + 8 ≤ descriptor.lease.layout.size := by rw [descriptor.extent]; exact bounded
  have executed : NativeReferenceMachine.execute world (.access index offset (.read 8 8)) = some next := by
    simp only [NativeReferenceMachine.execute,NativeReferenceMachine.access,descriptor.resident,Option.bind_some,
      descriptor.registered,NativeReferenceMachine.Access.mode,NativeReferenceMachine.Access.layout,true_or,bound,
      and_self,ite_true,shifted,permission,preparation,NativeReferenceMachine.perform,prepared,
      NativePointerMachine.push,bytesLoaded,Option.map_some,next]
  refine ⟨next,NativeReservationErrorFields.wordAccess_complete world next index offset word executed ?_,?_⟩
  · change NativeWord64Memory.decode bytes = some word
    exact decoded
  · exact ⟨⟨descriptor.reference,descriptor.lease,descriptor.resident,descriptor.registered,descriptor.shared,
      descriptor.extent,List.mem_cons_of_mem slot descriptor.baseResident,descriptor.allowed,descriptor.stored⟩⟩

theorem read_complete (world : State) (index : Nat) (kind : Kind) (descriptor : Readable world index kind)
    (valid : Valid kind) : ∃ next, NativeReservationErrorFields.read world index = .value kind next := by
  have selected := NativeRawVecFields.select_complete world index descriptor.reference descriptor.lease
    descriptor.resident descriptor.registered descriptor.shared descriptor.extent
  have atZero : NativeByteRange.pointerAt descriptor.lease.pointer 0 = some descriptor.lease.pointer := by
    simp [NativeByteRange.pointerAt,descriptor.lease.pointer.address.isLt]
  cases kind with
  | capacityOverflow =>
    obtain ⟨next,loaded,_⟩ := word_complete world index .capacityOverflow descriptor 0 descriptor.lease.pointer 0
      (by decide) atZero descriptor.stored
    exact ⟨next,NativeReservationErrorFields.overflow_complete world next index descriptor.reference selected loaded⟩
  | allocationError size alignment =>
    have first := descriptor.stored.1
    obtain ⟨middle,alignmentRead,⟨middleDescriptor⟩⟩ := word_complete world index (.allocationError size alignment)
      descriptor 0 descriptor.lease.pointer alignment (by decide) atZero first
    obtain ⟨slot,atSlot,sizeStored⟩ := middleDescriptor.stored.2
    obtain ⟨next,sizeRead,_⟩ := word_complete middle index (.allocationError size alignment) middleDescriptor 8 slot size
      (by decide) atSlot sizeStored
    exact ⟨next,NativeReservationErrorFields.allocation_complete world middle next index descriptor.reference size alignment
      selected alignmentRead valid.1 sizeRead valid.2⟩

theorem grant_readable (world next : State) (pointer : Pointer) (kind : Kind)
    (baseResident : pointer ∈ world.pointers.registers)
    (granted : NativeStorageBorrowMachine.grant world none .shared pointer ⟨16,8⟩ = some next)
    (stored : Stored next.pointers.heap.memory pointer kind) : Nonempty (Readable next 0 kind) := by
  obtain ⟨tag,ledger,actual,pointers,counter,leases,references,births⟩ :=
    NativeStorageBorrowMachine.grant_success world next none .shared pointer ⟨16,8⟩ granted
  obtain ⟨_,_,_,newLeases,allowed,_⟩ := NativeByteBorrowStorage.borrow_success _ _ _ _ _ _ _ actual
  have lookup : NativeByteBorrow.lookup next.leases tag = some ⟨tag,none,pointer,⟨16,8⟩,.shared⟩ := by
    rw [leases,newLeases]
    simp [NativeByteBorrow.lookup]
  refine ⟨⟨⟨tag⟩,⟨tag,none,pointer,⟨16,8⟩,.shared⟩,?_,lookup,rfl,rfl,?_,?_,stored⟩⟩
  · rw [references]; rfl
  · rw [pointers]; exact baseResident
  · change NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger next) .shared pointer ⟨16,8⟩ = true
    change NativeByteBorrow.rawAllowed (NativeReferenceMachine.ledger world) .shared pointer ⟨16,8⟩ = true at allowed
    simp only [NativeByteBorrow.rawAllowed,NativeReferenceMachine.ledger,leases,newLeases,List.all_cons,Bool.and_eq_true]
    refine ⟨?_,allowed⟩
    exact decide_eq_true (Or.inl ⟨rfl,rfl⟩)

theorem snapshot_readable (tags : Tags) (world next : State) (base : NativePointerStorage.Address)
    (value result : NativeRecordValues.Value) (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue tags world base value = .value result next) :
    ∃ kind, NativeReservationErrorLocal.decode tags value = some kind ∧ Valid kind ∧ Nonempty (Readable next 0 kind) := by
  obtain ⟨kind,allocated,written,decoded,allocation,writing,borrowing⟩ :=
    NativeReservationErrorLocal.snapshot_trace tags world next base value result executed
  have allocatedValid := NativeStorageBorrowMachine.execute_wellFormed world allocated valid _ allocation
  obtain ⟨pointer,registered,registers,stored⟩ :=
    NativeReservationErrorLocal.write_execution_fields allocated written kind allocatedValid.1.1 writing
  have finalHeap := NativeStorageBorrowMachine.storage_heap written next none 0 .shared ⟨16,8⟩ borrowing
  simp only [NativeStorageBorrowMachine.execute,NativeStorageBorrowMachine.parentTag,Option.bind_some,Option.bind_eq_some_iff] at borrowing
  obtain ⟨actualPointer,selected,granted⟩ := borrowing
  have same : actualPointer = pointer := by rw [registers,registered] at selected; exact Option.some.inj selected.symm
  subst actualPointer
  have baseMember : pointer ∈ written.pointers.registers := by rw [registers]; exact List.mem_of_getElem? registered
  refine ⟨kind,decoded,NativeReservationErrorLocal.decode_valid tags value kind decoded,
    grant_readable written next pointer kind baseMember granted ?_⟩
  rw [finalHeap]
  exact stored

theorem snapshot_read_complete (tags : Tags) (world next : State) (base : NativePointerStorage.Address)
    (value result : NativeRecordValues.Value) (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue tags world base value = .value result next) :
    ∃ kind final, value = NativeReservationErrorLocal.encode tags kind ∧
      NativeReservationErrorFields.read next 0 = .value kind final := by
  obtain ⟨kind,decoded,kindValid,⟨descriptor⟩⟩ := snapshot_readable tags world next base value result valid executed
  obtain ⟨final,read⟩ := read_complete next 0 kind descriptor kindValid
  exact ⟨kind,final,NativeReservationErrorLocal.decode_sound tags value kind decoded,read⟩

theorem snapshotLocal_read_complete (tags : Tags) (frame : NativeRecordLLBC.Frame) (index : Nat)
    (base : NativePointerStorage.Address) (next : State) (result : NativeRecordValues.Value)
    (valid : NativeReferenceMachine.WellFormed frame.world)
    (executed : NativeReservationErrorLocal.snapshotLocal tags frame index base = .value result next) :
    ∃ value kind final, NativeRecordLLBC.read frame index [] = some value ∧
      value = NativeReservationErrorLocal.encode tags kind ∧ NativeReservationErrorFields.read next 0 = .value kind final := by
  cases selected : NativeRecordLLBC.read frame index [] with
  | none => simp only [NativeReservationErrorLocal.snapshotLocal,selected] at executed; cases executed
  | some value =>
    simp only [NativeReservationErrorLocal.snapshotLocal,selected] at executed
    obtain ⟨kind,final,same,read⟩ := snapshot_read_complete tags frame.world next base value result valid executed
    exact ⟨value,kind,final,rfl,same,read⟩

def resolveOperand (world : State) : NativeRecordValues.Value → Option Nat
  | .scalar (.reference false reference count) =>
      if count = 2 then NativeRawVecReference.resolve world reference .inner else none
  | _ => none

def getKind (tags : Tags) (world : State) (value : NativeRecordValues.Value) : NativeRawVecFields.Result NativeRecordValues.Value :=
  match resolveOperand world value with
  | none => .invalid world
  | some index => match NativeReservationErrorFields.read world index with
    | .invalid next => .invalid next
    | .value kind next => .value (NativeReservationErrorLocal.kindValue tags kind) next

theorem getKind_complete (tags : Tags) (world : State) (index : Nat) (kind : Kind)
    (descriptor : Readable world index kind) (valid : Valid kind) :
    ∃ next, getKind tags world (.scalar (.reference false descriptor.reference 2)) =
      .value (NativeReservationErrorLocal.kindValue tags kind) next := by
  have member := List.mem_of_getElem? descriptor.resident
  have resolved := NativeRawVecReference.resolve_complete world descriptor.reference .inner descriptor.lease
    member descriptor.registered descriptor.shared descriptor.extent
  let shifted : Readable world (world.references.idxOf descriptor.reference) kind :=
    ⟨descriptor.reference,descriptor.lease,List.getElem?_idxOf member,descriptor.registered,descriptor.shared,
      descriptor.extent,descriptor.baseResident,descriptor.allowed,descriptor.stored⟩
  obtain ⟨next,read⟩ := read_complete world _ kind shifted valid
  refine ⟨next,?_⟩
  simp only [getKind,resolveOperand,ite_true,resolved,read]

theorem getKind_projects (tags : Tags) (world : State) (value : NativeRecordValues.Value) :
    NativeStorageBorrowMachine.Runs world (getKind tags world value).world := by
  cases resolved : resolveOperand world value with
  | none => simp only [getKind,resolved,NativeRawVecFields.Result.world]; exact .refl _
  | some index =>
    have projected := NativeStorageBorrowMachine.read_projects world index
    cases actual : NativeReservationErrorFields.read world index <;>
      simpa only [getKind,resolved,actual,NativeRawVecFields.Result.world] using projected

theorem getKind_heap (tags : Tags) (world : State) (value : NativeRecordValues.Value) :
    (getKind tags world value).world.pointers.heap = world.pointers.heap := by
  cases resolved : resolveOperand world value with
  | none => simp only [getKind,resolved,NativeRawVecFields.Result.world]
  | some index =>
    have kept := NativeReservationErrorFields.read_heap world index
    cases actual : NativeReservationErrorFields.read world index <;>
      simpa only [getKind,resolved,actual,NativeRawVecFields.Result.world] using kept

theorem getKind_reachable (tags : Tags) (world : State) (value : NativeRecordValues.Value)
    (reachable : NativeStorageBorrowMachine.Reachable world) :
    NativeStorageBorrowMachine.Reachable (getKind tags world value).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _ reachable (getKind_projects tags world value)

theorem snapshot_getKind_complete (tags : Tags) (world next : State) (base : NativePointerStorage.Address)
    (value result : NativeRecordValues.Value) (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue tags world base value = .value result next) :
    ∃ kind final, value = NativeReservationErrorLocal.encode tags kind ∧
      getKind tags next result = .value (NativeReservationErrorLocal.kindValue tags kind) final := by
  obtain ⟨kind,decoded,kindValid,⟨descriptor⟩⟩ := snapshot_readable tags world next base value result valid executed
  obtain ⟨_,reference,_,_,selected,resultEq⟩ := NativeReservationErrorLocal.snapshotValue_success tags world next base value result executed
  obtain ⟨_,found,_⟩ := NativeRawVecFields.select_success next 0 reference selected
  have same : reference = descriptor.reference := Option.some.inj (found.symm.trans descriptor.resident)
  subst reference
  obtain ⟨final,read⟩ := getKind_complete tags next 0 kind descriptor kindValid
  exact ⟨kind,final,NativeReservationErrorLocal.decode_sound tags value kind decoded,by rw [resultEq]; exact read⟩

theorem snapshotLocal_getKind_complete (tags : Tags) (frame : NativeRecordLLBC.Frame) (index : Nat)
    (base : NativePointerStorage.Address) (next : State) (result : NativeRecordValues.Value)
    (valid : NativeReferenceMachine.WellFormed frame.world)
    (executed : NativeReservationErrorLocal.snapshotLocal tags frame index base = .value result next) :
    ∃ kind final, NativeRecordLLBC.read frame index [] = some (NativeReservationErrorLocal.encode tags kind) ∧
      getKind tags next result = .value (NativeReservationErrorLocal.kindValue tags kind) final := by
  cases selected : NativeRecordLLBC.read frame index [] with
  | none => simp only [NativeReservationErrorLocal.snapshotLocal,selected] at executed; cases executed
  | some value =>
    simp only [NativeReservationErrorLocal.snapshotLocal,selected] at executed
    obtain ⟨kind,final,same,read⟩ := snapshot_getKind_complete tags frame.world next base value result valid executed
    exact ⟨kind,final,congrArg some same,read⟩

theorem encoded_kind_unique (tags : Tags) (first second : Kind)
    (same : NativeReservationErrorLocal.encode tags first = NativeReservationErrorLocal.encode tags second) : first = second := by
  cases first <;> cases second <;>
    simp_all [NativeReservationErrorLocal.encode,NativeReservationErrorLocal.kindValue,NativeReservationErrorLocal.layoutValue]

theorem snapshot_getKind_decoded (tags : Tags) (world next : State) (base : NativePointerStorage.Address)
    (value result : NativeRecordValues.Value) (kind : Kind) (valid : NativeReferenceMachine.WellFormed world)
    (decoded : NativeReservationErrorLocal.decode tags value = some kind)
    (executed : NativeReservationErrorLocal.snapshotValue tags world base value = .value result next) :
    ∃ final, getKind tags next result = .value (NativeReservationErrorLocal.kindValue tags kind) final := by
  obtain ⟨actual,final,same,getter⟩ := snapshot_getKind_complete tags world next base value result valid executed
  have expected := NativeReservationErrorLocal.decode_sound tags value kind decoded
  have identical := encoded_kind_unique tags actual kind (same.symm.trans expected)
  subst actual
  exact ⟨final,getter⟩

end FormalProof4FHE.HasteBoots.NativeReservationErrorRead
