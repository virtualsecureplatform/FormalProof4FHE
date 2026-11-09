module
public import FormalProof4FHE.HasteBoots.NativeSliceLLBC
@[expose] public section

/-! Checked resident reads for the retained 16-byte RawVecInner object. Capacity
is at offset zero and the complete stored pointer is at offset eight. This is a
byte/shadow bridge, not a Rust body, ABI, compiler or lifetime correspondence. -/
namespace FormalProof4FHE.HasteBoots.NativeRawVecFields
open NativeReferenceMachine (State Reference)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)

/-- Select a resident shared reference with the complete source object layout. -/
def select (world : State) (index : Nat) : Option Reference := do
  let reference ← world.references[index]?
  let lease ← NativeByteBorrow.lookup world.leases reference.tag
  if lease.mode = .shared ∧ lease.layout = ⟨16,8⟩ then some reference else none

inductive Result (α : Type) where
  | value (value : α) (world : State)
  | invalid (world : State)
  deriving DecidableEq

def Result.world {α : Type} : Result α → State
  | .value _ world | .invalid world => world

/-- Reject a high-bit capacity after retaining the actual eight-byte read. The
check is not a native validity theorem for the source's constrained carrier. -/
def capacityAccess (world : State) (index : Nat) : Result Word :=
  match NativeReferenceMachine.execute world (.access index 0 (.read 8 8)) with
  | none => .invalid world
  | some next => match next.outputs[0]? >>= NativeWord64Memory.decode with
    | none => .invalid next
    | some value => if value.val < 2^63 then .value value next else .invalid next

def capacity (world : State) (index : Nat) : Result Word :=
  match select world index with
  | none => .invalid world
  | some _ => capacityAccess world index

/-- Recover complete provenance from the pointer shadow, never from address bits.
A rejected null value retains the executed pointer load. -/
def pointerAccess (world : State) (index : Nat) : Result Pointer :=
  match NativeReferenceMachine.execute world (.access index 8 .loadPointer) with
  | none => .invalid world
  | some next => match next.pointers.registers[0]? with
    | none => .invalid next
    | some value => if value.address.val ≠ 0 then .value value next else .invalid next

def pointer (world : State) (index : Nat) : Result Pointer :=
  match select world index with
  | none => .invalid world
  | some _ => pointerAccess world index

theorem select_success (world : State) (index : Nat) (reference : Reference)
    (selected : select world index = some reference) :
    ∃ lease, world.references[index]? = some reference ∧
      NativeByteBorrow.lookup world.leases reference.tag = some lease ∧
      lease.mode = .shared ∧ lease.layout = ⟨16,8⟩ := by
  simp only [select, Option.bind_eq_bind', Option.bind_eq_some_iff] at selected
  obtain ⟨reference, found, lease, registered, selected⟩ := selected
  split at selected
  next valid => cases selected; exact ⟨lease,found,registered,valid⟩
  next => cases selected

theorem select_complete (world : State) (index : Nat) (reference : Reference) (lease : NativeByteBorrow.Lease)
    (found : world.references[index]? = some reference)
    (registered : NativeByteBorrow.lookup world.leases reference.tag = some lease)
    (shared : lease.mode = .shared) (layout : lease.layout = ⟨16,8⟩) :
    select world index = some reference := by
  simp only [select, found, Option.bind_eq_bind', Option.bind_some, registered, shared, layout, and_self, ite_true]

theorem capacity_projects (world : State) (index : Nat) :
    NativeReferenceMachine.Runs world (capacity world index).world := by
  cases selected : select world index with
  | none => simp only [capacity, selected, Result.world]; exact .refl _
  | some reference =>
    cases actual : NativeReferenceMachine.execute world (.access index 0 (.read 8 8)) with
    | none => simp only [capacity, capacityAccess, selected, actual, Result.world]; exact .refl _
    | some next =>
      have first := NativeReferenceMachine.Runs.step (.refl world) _ actual
      cases decoded : next.outputs[0]? >>= NativeWord64Memory.decode with
      | none => simpa only [capacity, capacityAccess, selected, actual, decoded, Result.world] using first
      | some value =>
        by_cases valid : value.val < 2^63 <;>
          simpa only [capacity, capacityAccess, selected, actual, decoded, valid, ite_true, ite_false, Result.world] using first

theorem pointer_projects (world : State) (index : Nat) :
    NativeReferenceMachine.Runs world (pointer world index).world := by
  cases selected : select world index with
  | none => simp only [pointer, selected, Result.world]; exact .refl _
  | some reference =>
    cases actual : NativeReferenceMachine.execute world (.access index 8 .loadPointer) with
    | none => simp only [pointer, pointerAccess, selected, actual, Result.world]; exact .refl _
    | some next =>
      have first := NativeReferenceMachine.Runs.step (.refl world) _ actual
      cases found : next.pointers.registers[0]? with
      | none => simpa only [pointer, pointerAccess, selected, actual, found, Result.world] using first
      | some value =>
        simp only [pointer, pointerAccess, selected, actual, found]
        split <;> exact first

theorem capacity_success (world next : State) (index : Nat) (value : Word)
    (loaded : capacity world index = .value value next) :
    (∃ reference, select world index = some reference) ∧
      NativeReferenceMachine.execute world (.access index 0 (.read 8 8)) = some next ∧
      (next.outputs[0]? >>= NativeWord64Memory.decode) = some value ∧ value.val < 2^63 := by
  cases selected : select world index with
  | none => simp only [capacity, selected] at loaded; cases loaded
  | some reference =>
    cases actual : NativeReferenceMachine.execute world (.access index 0 (.read 8 8)) with
    | none => simp only [capacity, capacityAccess, selected, actual] at loaded; cases loaded
    | some changed =>
      cases decoded : changed.outputs[0]? >>= NativeWord64Memory.decode with
      | none => simp only [capacity, capacityAccess, selected, actual, decoded] at loaded; cases loaded
      | some word =>
        by_cases valid : word.val < 2^63
        · simp only [capacity, capacityAccess, selected, actual, decoded, valid, ite_true] at loaded
          cases loaded
          exact ⟨⟨reference, rfl⟩,rfl,decoded,valid⟩
        · simp only [capacity, capacityAccess, selected, actual, decoded, valid, ite_false] at loaded; cases loaded

theorem pointer_success (world next : State) (index : Nat) (value : Pointer)
    (loaded : pointer world index = .value value next) :
    (∃ reference, select world index = some reference) ∧
      NativeReferenceMachine.execute world (.access index 8 .loadPointer) = some next ∧
      next.pointers.registers[0]? = some value ∧ value.address.val ≠ 0 := by
  cases selected : select world index with
  | none => simp only [pointer, selected] at loaded; cases loaded
  | some reference =>
    cases actual : NativeReferenceMachine.execute world (.access index 8 .loadPointer) with
    | none => simp only [pointer, pointerAccess, selected, actual] at loaded; cases loaded
    | some changed =>
      cases found : changed.pointers.registers[0]? with
      | none => simp only [pointer, pointerAccess, selected, actual, found] at loaded; cases loaded
      | some raw =>
        simp only [pointer, pointerAccess, selected, actual, found] at loaded
        split at loaded
        next valid =>
          cases loaded
          exact ⟨⟨reference, rfl⟩,rfl,found,valid⟩
        next => cases loaded

theorem capacity_reachable (world : State) (index : Nat) (reachable : NativeReferenceMachine.Reachable world) :
    NativeReferenceMachine.Reachable (capacity world index).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (capacity_projects world index)

theorem pointer_reachable (world : State) (index : Nat) (reachable : NativeReferenceMachine.Reachable world) :
    NativeReferenceMachine.Reachable (pointer world index).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (pointer_projects world index)

theorem capacity_effect (world next : State) (index : Nat) (value : Word)
    (loaded : capacity world index = .value value next) :
    ∃ (lease : NativeByteBorrow.Lease) (slot : Pointer) (bytes : List NativeByteMemory.Byte),
      NativeByteRange.pointerAt lease.pointer 0 = some slot ∧
      NativeByteRange.loadRange world.pointers.heap.memory slot ⟨8,8⟩ = some bytes ∧
      NativeWord64Memory.encode value = bytes ∧ next.outputs = bytes :: world.outputs ∧
      next.pointers.heap = world.pointers.heap ∧ next.pointers.registers = slot :: world.pointers.registers ∧
      next.pointers.history = world.pointers.history ∧ next.nextTag = world.nextTag ∧
      next.leases = world.leases ∧ next.references = world.references ∧ next.births = world.births := by
  obtain ⟨_, actual, decoded, _⟩ := capacity_success world next index value loaded
  obtain ⟨selected, lease, slot, prepared, _, _, _, _, shifted, _, preparedEq, performed⟩ :=
    NativeReferenceMachine.access_success world next index 0 (.read 8 8) actual
  have fields := NativeByteRange.pointerAt_fields lease.pointer 0 slot shifted
  have preparedState := (NativeReferenceMachine.prepare_success world lease.pointer slot.address prepared preparedEq).2
  have pointerEq : NativePointerStorage.Pointer.mk slot.address lease.pointer.provenance = slot := by
    rw [← fields.2]
  simp only [NativeReferenceMachine.perform, Option.map_eq_some_iff] at performed
  obtain ⟨bytes, bytesEq, same⟩ := performed
  cases same
  rw [preparedState] at bytesEq
  change NativeByteRange.loadRange world.pointers.heap.memory slot ⟨8,8⟩ = some bytes at bytesEq
  change NativeWord64Memory.decode bytes = some value at decoded
  refine ⟨lease,slot,bytes,shifted,bytesEq,NativeWord64Memory.encode_decode bytes value decoded,rfl,?_,?_,?_,rfl,rfl,rfl,rfl⟩
  · rw [preparedState]; rfl
  · rw [preparedState, pointerEq]; rfl
  · rw [preparedState]; rfl

theorem pointer_effect (world next : State) (index : Nat) (value : Pointer)
    (loaded : pointer world index = .value value next) :
    ∃ (lease : NativeByteBorrow.Lease) (slot : Pointer) (owner : NativePointerStorage.Origin),
      NativeByteRange.pointerAt lease.pointer 8 = some slot ∧
      slot.provenance = some owner ∧
      NativeWord64Memory.load world.pointers.heap.memory slot = some value.address ∧
      NativePointerShadow.uniform world.pointers.heap.shadow owner slot.address.val 8 = some value.provenance ∧
      next.outputs = world.outputs ∧ next.pointers.heap = world.pointers.heap ∧
      next.pointers.registers = value :: slot :: world.pointers.registers ∧
      next.pointers.history = world.pointers.history ∧ next.nextTag = world.nextTag ∧
      next.leases = world.leases ∧ next.references = world.references ∧ next.births = world.births := by
  obtain ⟨_, actual, headEq, _⟩ := pointer_success world next index value loaded
  obtain ⟨selected, lease, slot, prepared, _, _, _, _, shifted, _, preparedEq, performed⟩ :=
    NativeReferenceMachine.access_success world next index 8 .loadPointer actual
  have fields := NativeByteRange.pointerAt_fields lease.pointer 8 slot shifted
  have preparedState := (NativeReferenceMachine.prepare_success world lease.pointer slot.address prepared preparedEq).2
  have pointerEq : NativePointerStorage.Pointer.mk slot.address lease.pointer.provenance = slot := by
    rw [← fields.2]
  simp only [NativeReferenceMachine.perform, Option.map_eq_some_iff] at performed
  obtain ⟨pointers, executed, same⟩ := performed
  cases same
  simp only [NativePointerMachine.execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at executed
  obtain ⟨location, locationEq, recovered, recoveredEq, same⟩ := executed
  cases same
  change some recovered = some value at headEq
  cases headEq
  have locationSame : location = slot := by
    rw [preparedState, pointerEq] at locationEq
    exact Option.some.inj locationEq.symm
  subst location
  rw [preparedState] at recoveredEq
  change NativePointerByteMemory.load world.pointers.heap slot = some value at recoveredEq
  obtain ⟨owner, ownerEq, wordEq, shadowEq⟩ := NativePointerByteMemory.load_success world.pointers.heap slot value recoveredEq
  refine ⟨lease,slot,owner,shifted,ownerEq,wordEq,shadowEq,rfl,?_,?_,?_,rfl,rfl,rfl,rfl⟩
  · rw [preparedState]; rfl
  · rw [preparedState, pointerEq]; rfl
  · rw [preparedState]; rfl

theorem capacity_failure_prefix (world next : State) (index : Nat)
    (failed : capacity world index = .invalid next) :
    next = world ∨ NativeReferenceMachine.execute world (.access index 0 (.read 8 8)) = some next := by
  cases selected : select world index with
  | none => simp only [capacity, selected] at failed; cases failed; exact Or.inl rfl
  | some reference =>
    cases actual : NativeReferenceMachine.execute world (.access index 0 (.read 8 8)) with
    | none => simp only [capacity, capacityAccess, selected, actual] at failed; cases failed; exact Or.inl rfl
    | some changed =>
      cases decoded : changed.outputs[0]? >>= NativeWord64Memory.decode with
      | none => simp only [capacity, capacityAccess, selected, actual, decoded] at failed; cases failed; exact Or.inr rfl
      | some value =>
        simp only [capacity, capacityAccess, selected, actual, decoded] at failed
        split at failed
        · cases failed
        · cases failed; exact Or.inr rfl

theorem pointer_failure_prefix (world next : State) (index : Nat)
    (failed : pointer world index = .invalid next) :
    next = world ∨ NativeReferenceMachine.execute world (.access index 8 .loadPointer) = some next := by
  cases selected : select world index with
  | none => simp only [pointer, selected] at failed; cases failed; exact Or.inl rfl
  | some reference =>
    cases actual : NativeReferenceMachine.execute world (.access index 8 .loadPointer) with
    | none => simp only [pointer, pointerAccess, selected, actual] at failed; cases failed; exact Or.inl rfl
    | some changed =>
      cases found : changed.pointers.registers[0]? with
      | none => simp only [pointer, pointerAccess, selected, actual, found] at failed; cases failed; exact Or.inr rfl
      | some value =>
        simp only [pointer, pointerAccess, selected, actual, found] at failed
        split at failed
        · cases failed
        · cases failed; exact Or.inr rfl

theorem capacityAccess_projects (world : State) (index : Nat) :
    NativeReferenceMachine.Runs world (capacityAccess world index).world := by
  cases actual : NativeReferenceMachine.execute world (.access index 0 (.read 8 8)) with
  | none => simp only [capacityAccess, actual, Result.world]; exact .refl _
  | some next =>
    have first := NativeReferenceMachine.Runs.step (.refl world) _ actual
    cases decoded : next.outputs[0]? >>= NativeWord64Memory.decode with
    | none => simpa only [capacityAccess, actual, decoded, Result.world] using first
    | some value =>
      simp only [capacityAccess, actual, decoded]
      split <;> exact first

theorem pointerAccess_projects (world : State) (index : Nat) :
    NativeReferenceMachine.Runs world (pointerAccess world index).world := by
  cases actual : NativeReferenceMachine.execute world (.access index 8 .loadPointer) with
  | none => simp only [pointerAccess, actual, Result.world]; exact .refl _
  | some next =>
    have first := NativeReferenceMachine.Runs.step (.refl world) _ actual
    cases found : next.pointers.registers[0]? with
    | none => simpa only [pointerAccess, actual, found, Result.world] using first
    | some value =>
      simp only [pointerAccess, actual, found]
      split <;> exact first

end FormalProof4FHE.HasteBoots.NativeRawVecFields
