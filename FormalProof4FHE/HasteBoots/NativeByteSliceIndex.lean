module
public import FormalProof4FHE.HasteBoots.NativeReferenceCleanup
@[expose] public section

/-! Mutable byte-slice indexing through existing reference and raw registers.
Every intermediate world is retained on failure. This is a checked primitive
model, not a Rust indexing, aliasing or compiler refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeByteSliceIndex
open NativeReferenceMachine (State Reference)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)

structure Slice where
  reference : Reference
  length : Word
  deriving DecidableEq

structure Selection where
  parent : Nat
  raw : Nat
  lease : NativeByteBorrow.Lease
  deriving DecidableEq

/-- Length metadata is checked against the actual resident byte-slice lease. -/
def select (world : State) (slice : Slice) : Option Selection := do
  let lease ← NativeByteBorrow.lookup world.leases slice.reference.tag
  let parent := world.references.idxOf slice.reference
  let raw := world.pointers.registers.idxOf lease.pointer
  if world.references[parent]? = some slice.reference ∧
      world.pointers.registers[raw]? = some lease.pointer ∧
      lease.layout = ⟨slice.length.val, 1⟩ ∧ lease.mode = .exclusive then
    some ⟨parent, raw, lease⟩
  else none

inductive Result where
  | value (reference : Reference) (world : State)
  | invalid (world : State)
  deriving DecidableEq

def Result.world : Result → State
  | .value _ world | .invalid world => world

/-- Both provenance recovery and the child grant are closed-machine operations.
The child address is computed only after the source index passes its bounds. -/
def index (world : State) (slice : Slice) (offset : Word) : Result :=
  if offset.val < slice.length.val then
    match select world slice with
    | none => .invalid world
    | some selected => match NativeByteRange.pointerAt selected.lease.pointer offset.val with
      | none => .invalid world
      | some pointer => match NativeReferenceMachine.execute world (.raw (.withAddress selected.raw pointer.address)) with
        | none => .invalid world
        | some prepared => match NativeReferenceMachine.execute prepared (.reborrow selected.parent 0 .exclusive ⟨1,1⟩) with
          | none => .invalid prepared
          | some next => .value ⟨prepared.nextTag⟩ next
  else .invalid world

/-- A raw borrow recovers an existing complete pointer. It neither invents
provenance nor creates or ends a ledger lease. -/
def rawByte (world : State) (reference : Reference) : Option Pointer := do
  let lease ← NativeByteBorrow.lookup world.leases reference.tag
  let parent := world.references.idxOf reference
  let raw := world.pointers.registers.idxOf lease.pointer
  if world.references[parent]? = some reference ∧ world.pointers.registers[raw]? = some lease.pointer ∧
      lease.layout = ⟨1,1⟩ ∧ lease.mode = .exclusive then
    some lease.pointer
  else none

theorem select_success (world : State) (slice : Slice) (selected : Selection) (found : select world slice = some selected) :
    NativeByteBorrow.lookup world.leases slice.reference.tag = some selected.lease ∧
    world.references[selected.parent]? = some slice.reference ∧
    world.pointers.registers[selected.raw]? = some selected.lease.pointer ∧
    selected.lease.layout = ⟨slice.length.val, 1⟩ ∧ selected.lease.mode = .exclusive := by
  simp only [select, Option.bind_eq_bind', Option.bind_eq_some_iff] at found
  obtain ⟨lease, actual, found⟩ := found
  split at found
  · cases found
    exact ⟨actual, ‹_›⟩
  · cases found

theorem index_success (world next : State) (slice : Slice) (offset : Word) (reference : Reference)
    (indexed : index world slice offset = .value reference next) :
    offset.val < slice.length.val ∧ ∃ selected pointer prepared,
      select world slice = some selected ∧
      NativeByteRange.pointerAt selected.lease.pointer offset.val = some pointer ∧
      NativeReferenceMachine.execute world (.raw (.withAddress selected.raw pointer.address)) = some prepared ∧
      NativeReferenceMachine.execute prepared (.reborrow selected.parent 0 .exclusive ⟨1,1⟩) = some next ∧
      reference = ⟨prepared.nextTag⟩ := by
  unfold index at indexed
  split at indexed
  · rename_i bounded
    split at indexed
    · cases indexed
    · rename_i selected actual
      split at indexed
      · cases indexed
      · rename_i pointer shifted
        split at indexed
        · cases indexed
        · rename_i prepared preparedEq
          split at indexed
          · cases indexed
          · cases indexed
            exact ⟨bounded, selected, pointer, prepared, actual, shifted, preparedEq, ‹_›, rfl⟩
  · cases indexed

theorem index_projects (world : State) (slice : Slice) (offset : Word) :
    NativeReferenceMachine.Runs world (index world slice offset).world := by
  unfold index
  split
  · split
    · exact .refl _
    · split
      · exact .refl _
      · split
        · exact .refl _
        · rename_i prepared actual
          have first := NativeReferenceMachine.Runs.step (.refl world) _ actual
          split
          · exact first
          · exact .step first _ ‹_›
  · exact .refl _

theorem rawByte_registered (world : State) (reference : Reference) (pointer : Pointer)
    (recovered : rawByte world reference = some pointer) :
    pointer ∈ world.pointers.registers ∧ ∃ lease,
      NativeByteBorrow.lookup world.leases reference.tag = some lease ∧
      lease.pointer = pointer ∧ lease.layout = ⟨1,1⟩ ∧ lease.mode = .exclusive := by
  simp only [rawByte, Option.bind_eq_bind', Option.bind_eq_some_iff] at recovered
  obtain ⟨lease, found, recovered⟩ := recovered
  split at recovered
  · rename_i checked
    cases recovered
    exact ⟨List.mem_of_getElem? checked.2.1, lease, found, rfl, checked.2.2⟩
  · cases recovered

theorem prepare_selected (world prepared : State) (selected : Selection) (pointer : Pointer)
    (registered : world.pointers.registers[selected.raw]? = some selected.lease.pointer)
    (advanced : pointer.provenance = selected.lease.pointer.provenance)
    (executed : NativeReferenceMachine.execute world (.raw (.withAddress selected.raw pointer.address)) = some prepared) :
    prepared = {world with pointers := NativePointerMachine.push world.pointers pointer} := by
  simp only [NativeReferenceMachine.execute, NativeReferenceMachine.rawPermissions, ite_true,
    NativePointerMachine.execute, registered, Option.map_some] at executed
  cases executed
  cases pointer with
  | mk address provenance =>
    simp only at advanced
    subst provenance
    rfl

theorem index_grant (world next : State) (slice : Slice) (offset : Word) (reference : Reference)
    (indexed : index world slice offset = .value reference next) :
    ∃ selected pointer,
      select world slice = some selected ∧
      pointer.address.val = selected.lease.pointer.address.val + offset.val ∧
      pointer.provenance = selected.lease.pointer.provenance ∧
      next.pointers = NativePointerMachine.push world.pointers pointer ∧
      reference = ⟨world.nextTag⟩ ∧ next.nextTag = world.nextTag + 1 ∧
      next.leases = ⟨world.nextTag, some slice.reference.tag, pointer, ⟨1,1⟩, .exclusive⟩ :: world.leases ∧
      next.references = ⟨world.nextTag⟩ :: world.references := by
  obtain ⟨_, selected, pointer, prepared, selection, shifted, preparedEq, reborrowed, tagEq⟩ := index_success world next slice offset reference indexed
  obtain ⟨_, parent, raw, _, _⟩ := select_success world slice selected selection
  obtain ⟨address, provenance⟩ := NativeByteRange.pointerAt_fields _ _ _ shifted
  have preparedSame := prepare_selected world prepared selected pointer raw provenance preparedEq
  subst prepared
  simp only [NativeReferenceMachine.execute, parent, NativePointerMachine.push, List.getElem?_cons_zero,
    Option.bind] at reborrowed
  obtain ⟨tag, borrowed, actual, pointers, counter, leases, references, _⟩ :=
    NativeReferenceMachine.grant_success _ next _ _ _ _ reborrowed
  obtain ⟨fresh, _, raised, newLeases, _, _⟩ := NativeByteBorrow.borrow_success _ _ _ _ _ tag borrowed actual
  refine ⟨selected, pointer, selection, address, provenance, pointers, ?_, ?_, ?_, ?_⟩
  · simpa only [fresh, NativeReferenceMachine.ledger] using tagEq
  · exact counter.trans raised
  · simpa only [fresh, NativeReferenceMachine.ledger] using leases.trans newLeases
  · simpa only [fresh, NativeReferenceMachine.ledger] using references

theorem index_heap_frame (world : State) (slice : Slice) (offset : Word) :
    (index world slice offset).world.pointers.heap = world.pointers.heap := by
  unfold index
  split
  · split
    · rfl
    · rename_i selected selection
      have raw := (select_success world slice selected selection).2.2.1
      split
      · rfl
      · rename_i pointer shifted
        split
        · rfl
        · rename_i prepared preparedEq
          have provenance := (NativeByteRange.pointerAt_fields _ _ _ shifted).2
          have same := prepare_selected world prepared selected pointer raw provenance preparedEq
          split
          · rw [same]; rfl
          · rename_i next granted
            rw [same] at granted
            have equal := (NativeReferenceMachine.grant_success _ next _ _ _ _ (by
              simpa only [NativeReferenceMachine.execute, (select_success world slice selected selection).2.1,
                NativePointerMachine.push, List.getElem?_cons_zero, Option.bind] using granted)).choose_spec.choose_spec.2.1
            have heapEq := congrArg NativePointerMachine.State.heap equal
            exact heapEq
  · rfl

theorem index_reachable (world : State) (reachable : NativeReferenceMachine.Reachable world) (slice : Slice) (offset : Word) :
    NativeReferenceMachine.Reachable (index world slice offset).world :=
  NativeSliceLLBC.reference_runs_reachable _ _ reachable (index_projects world slice offset)

theorem index_wellFormed (world : State) (valid : NativeReferenceMachine.WellFormed world) (slice : Slice) (offset : Word) :
    NativeReferenceMachine.WellFormed (index world slice offset).world :=
  NativeSliceLLBC.reference_runs_wellFormed _ _ valid (index_projects world slice offset)

end FormalProof4FHE.HasteBoots.NativeByteSliceIndex
