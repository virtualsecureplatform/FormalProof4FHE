module
public import FormalProof4FHE.HasteBoots.NativeByteRange
@[expose] public section

/-! Checked byte-borrow ledger with shared/exclusive access and reborrows.
Tags are ghost state, not runtime secrets or caller-supplied proof certificates.
This is not yet a Rust aliasing/reference or compiler refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeByteBorrow
open NativePointerStorage (Pointer)
open NativeByteMemory (Byte Layout)

inductive Mode where
  | shared
  | exclusive
  deriving DecidableEq

structure Lease where
  tag : Nat
  parent : Option Nat
  pointer : Pointer
  layout : Layout
  mode : Mode
  deriving DecidableEq

structure State where
  memory : NativeByteMemory.State
  nextTag : Nat
  leases : List Lease
  deriving DecidableEq

def empty : State := ⟨NativeByteMemory.empty, 0, []⟩

def lookup : List Lease → Nat → Option Lease
  | [], _ => none
  | lease :: tail, tag => if lease.tag = tag then some lease else lookup tail tag

/-- Physical byte overlap is independent of ghost allocation/tag identities. -/
def Overlap (pointer : Pointer) (layout : Layout) (other : Pointer) (otherLayout : Layout) : Prop :=
  0 < layout.size ∧ 0 < otherLayout.size ∧
    pointer.address.val < other.address.val + otherLayout.size ∧
    other.address.val < pointer.address.val + layout.size

instance (pointer : Pointer) (layout : Layout) (other : Pointer) (otherLayout : Layout) :
    Decidable (Overlap pointer layout other otherLayout) := by
  unfold Overlap
  infer_instance

def Compatible (mode : Mode) (pointer : Pointer) (layout : Layout) (lease : Lease) : Prop :=
  (mode = .shared ∧ lease.mode = .shared) ∨ ¬ Overlap pointer layout lease.pointer lease.layout

instance (mode : Mode) (pointer : Pointer) (layout : Layout) (lease : Lease) :
    Decidable (Compatible mode pointer layout lease) := by
  unfold Compatible
  infer_instance

def ancestor (leases : List Lease) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, older, child =>
      match lookup leases child with
      | none => false
      | some lease =>
          match lease.parent with
          | none => false
          | some parent => decide (older = parent) || ancestor leases fuel older parent

def rawAllowed (state : State) (mode : Mode) (pointer : Pointer) (layout : Layout) : Bool :=
  state.leases.all (fun lease => decide (Compatible mode pointer layout lease))

def throughAllowed (state : State) (tag : Nat) (mode : Mode) (pointer : Pointer) (layout : Layout) : Bool :=
  state.leases.all (fun lease => decide (lease.tag = tag) || ancestor state.leases state.nextTag lease.tag tag ||
    decide (Compatible mode pointer layout lease))

/-- A child cannot upgrade shared access, escape the parent span, or change its
origin. Ancestor exemptions apply only to a checked resident parent. -/
def parentAllowed (state : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout) : Bool :=
  match parent with
  | none => rawAllowed state mode pointer layout
  | some tag =>
      match lookup state.leases tag with
      | none => false
      | some lease =>
          decide (tag < state.nextTag ∧ (mode = .shared ∨ lease.mode = .exclusive) ∧
            pointer.provenance = lease.pointer.provenance ∧ lease.pointer.address.val ≤ pointer.address.val ∧
            pointer.address.val + layout.size ≤ lease.pointer.address.val + lease.layout.size) &&
          throughAllowed state tag mode pointer layout

def borrow (state : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout) :
    Option (Nat × State) :=
  if parentAllowed state parent mode pointer layout then
    (NativeByteRange.loadRange state.memory pointer layout).map (fun _ =>
      (state.nextTag, ⟨state.memory, state.nextTag + 1,
        ⟨state.nextTag, parent, pointer, layout, mode⟩ :: state.leases⟩))
  else none

/-- Ending a parent waits for its direct children; recursively this keeps the
whole ancestry resident. Tags are not reused. -/
def endBorrow (state : State) (tag : Nat) : Option State :=
  if (lookup state.leases tag).isSome && state.leases.all (fun lease => decide (lease.parent ≠ some tag)) then
    some {state with leases := state.leases.filter (fun lease => decide (lease.tag ≠ tag))}
  else none

def rawRead (state : State) (pointer : Pointer) (layout : Layout) : Option (List Byte) :=
  if rawAllowed state .shared pointer layout then NativeByteRange.loadRange state.memory pointer layout else none

def rawWrite (state : State) (pointer : Pointer) (byte : Byte) : Option State :=
  if rawAllowed state .exclusive pointer ⟨1, 1⟩ then
    (NativeByteMemory.storeByte state.memory pointer byte).map (fun memory => {state with memory})
  else none

def read (state : State) (tag offset size : Nat) : Option (List Byte) :=
  (lookup state.leases tag).bind (fun lease =>
    if offset + size ≤ lease.layout.size then
      (NativeByteRange.pointerAt lease.pointer offset).bind (fun pointer =>
        if throughAllowed state tag .shared pointer ⟨size, 1⟩ then
          NativeByteRange.loadRange state.memory pointer ⟨size, 1⟩
        else none)
    else none)

def write (state : State) (tag offset : Nat) (byte : Byte) : Option State :=
  (lookup state.leases tag).bind (fun lease =>
    if lease.mode = .exclusive ∧ offset < lease.layout.size then
      (NativeByteRange.pointerAt lease.pointer offset).bind (fun pointer =>
        if throughAllowed state tag .exclusive pointer ⟨1, 1⟩ then
          (NativeByteMemory.storeByte state.memory pointer byte).map (fun memory => {state with memory})
        else none)
    else none)

def allocate (state : State) (base : NativePointerStorage.Address) (layout : Layout) : Option (Pointer × State) :=
  (NativeByteMemory.allocate state.memory base layout).map (fun (pointer, memory) => (pointer, {state with memory}))

def deallocate (state : State) (pointer : Pointer) (layout : Layout) : Option State :=
  if rawAllowed state .exclusive pointer layout then
    (NativeByteMemory.deallocate state.memory pointer layout).map (fun memory => {state with memory})
  else none

theorem lookup_selected (leases : List Lease) (tag : Nat) (lease : Lease)
    (found : lookup leases tag = some lease) : lease ∈ leases ∧ lease.tag = tag := by
  induction leases with
  | nil => cases found
  | cons head tail ih =>
    unfold lookup at found
    split at found
    · rename_i same
      cases found
      exact ⟨List.mem_cons_self, same⟩
    · obtain ⟨member, same⟩ := ih found
      exact ⟨List.mem_cons_of_mem head member, same⟩

theorem overlap_symm (pointer other : Pointer) (layout otherLayout : Layout) :
    Overlap pointer layout other otherLayout ↔ Overlap other otherLayout pointer layout := by
  unfold Overlap
  omega

theorem empty_no_overlap (pointer other : Pointer) (alignment : Nat) (layout : Layout) :
    ¬ Overlap pointer ⟨0, alignment⟩ other layout := by
  intro overlap
  exact Nat.not_lt_zero _ overlap.1

theorem rawAllowed_selected (state : State) (mode : Mode) (pointer : Pointer) (layout : Layout)
    (allowed : rawAllowed state mode pointer layout = true) (lease : Lease) (member : lease ∈ state.leases) :
    Compatible mode pointer layout lease := by
  exact of_decide_eq_true (List.all_eq_true.mp allowed lease member)

theorem raw_exclusive_no_overlap (state : State) (pointer : Pointer) (layout : Layout)
    (allowed : rawAllowed state .exclusive pointer layout = true) (lease : Lease) (member : lease ∈ state.leases) :
    ¬ Overlap pointer layout lease.pointer lease.layout := by
  rcases rawAllowed_selected state .exclusive pointer layout allowed lease member with impossible | separate
  · cases impossible.1
  · exact separate

theorem through_selected (state : State) (tag : Nat) (mode : Mode) (pointer : Pointer) (layout : Layout)
    (allowed : throughAllowed state tag mode pointer layout = true) (lease : Lease) (member : lease ∈ state.leases) :
    lease.tag = tag ∨ ancestor state.leases state.nextTag lease.tag tag = true ∨ Compatible mode pointer layout lease := by
  have selected := List.all_eq_true.mp allowed lease member
  simpa only [Bool.or_eq_true, decide_eq_true_eq, or_assoc] using selected

theorem borrow_success (state : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout)
    (tag : Nat) (next : State) (executed : borrow state parent mode pointer layout = some (tag, next)) :
    tag = state.nextTag ∧ next.memory = state.memory ∧ next.nextTag = state.nextTag + 1 ∧
    next.leases = ⟨tag, parent, pointer, layout, mode⟩ :: state.leases ∧
    parentAllowed state parent mode pointer layout = true ∧
    ∃ bytes, NativeByteRange.loadRange state.memory pointer layout = some bytes := by
  unfold borrow at executed
  split at executed
  · rename_i allowed
    cases loaded : NativeByteRange.loadRange state.memory pointer layout with
    | none => simp only [loaded, Option.map_none] at executed; cases executed
    | some bytes =>
      simp only [loaded, Option.map_some] at executed
      cases executed
      exact ⟨rfl, rfl, rfl, rfl, allowed, bytes, rfl⟩
  · cases executed

theorem borrow_geometry (state : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout)
    (tag : Nat) (next : State) (executed : borrow state parent mode pointer layout = some (tag, next)) :
    NativeByteRange.Geometry pointer layout := by
  obtain ⟨bytes, loaded⟩ := (borrow_success state parent mode pointer layout tag next executed).2.2.2.2.2
  exact NativeByteRange.loadRange_geometry state.memory pointer layout bytes loaded

theorem root_exclusive_separated (state : State) (pointer : Pointer) (layout : Layout) (tag : Nat) (next : State)
    (executed : borrow state none .exclusive pointer layout = some (tag, next)) (lease : Lease)
    (member : lease ∈ state.leases) : ¬ Overlap pointer layout lease.pointer lease.layout := by
  have allowed := (borrow_success state none .exclusive pointer layout tag next executed).2.2.2.2.1
  exact raw_exclusive_no_overlap state pointer layout allowed lease member

theorem parent_checked (state : State) (parent : Nat) (mode : Mode) (pointer : Pointer) (layout : Layout)
    (allowed : parentAllowed state (some parent) mode pointer layout = true) :
    ∃ lease, lookup state.leases parent = some lease ∧ parent < state.nextTag ∧
      (mode = .shared ∨ lease.mode = .exclusive) ∧ pointer.provenance = lease.pointer.provenance ∧
      lease.pointer.address.val ≤ pointer.address.val ∧
      pointer.address.val + layout.size ≤ lease.pointer.address.val + lease.layout.size ∧
      throughAllowed state parent mode pointer layout = true := by
  unfold parentAllowed at allowed
  cases found : lookup state.leases parent with
  | none => simp only [found, Bool.false_eq_true] at allowed
  | some lease =>
    simp only [found, Bool.and_eq_true, decide_eq_true_eq] at allowed
    exact ⟨lease, rfl, allowed.1.1, allowed.1.2.1, allowed.1.2.2.1,
      allowed.1.2.2.2.1, allowed.1.2.2.2.2, allowed.2⟩

theorem shared_parent_no_upgrade (state : State) (parent : Nat) (pointer : Pointer) (layout : Layout)
    (lease : Lease) (found : lookup state.leases parent = some lease) (shared : lease.mode = .shared) :
    parentAllowed state (some parent) .exclusive pointer layout = false := by
  cases allowed : parentAllowed state (some parent) .exclusive pointer layout with
  | false => rfl
  | true =>
    obtain ⟨selected, same, _, right, _⟩ := parent_checked state parent .exclusive pointer layout allowed
    have equal : selected = lease := Option.some.inj (same.symm.trans found)
    rcases right with impossible | exclusive
    · cases impossible
    · rw [equal, shared] at exclusive
      cases exclusive

theorem lookup_filtered_tag (leases : List Lease) (tag : Nat) :
    lookup (leases.filter (fun lease => decide (lease.tag ≠ tag))) tag = none := by
  induction leases with
  | nil => rfl
  | cons head tail ih =>
    have normalized := ih
    simp only [decide_not] at normalized
    by_cases same : head.tag = tag <;> simpa [lookup, same] using normalized

theorem endBorrow_success (state : State) (tag : Nat) (next : State)
    (executed : endBorrow state tag = some next) :
    next.memory = state.memory ∧ next.nextTag = state.nextTag ∧
    next.leases = state.leases.filter (fun lease => decide (lease.tag ≠ tag)) ∧
    lookup next.leases tag = none ∧
    ∀ child ∈ state.leases, child.parent ≠ some tag := by
  unfold endBorrow at executed
  split at executed
  · rename_i allowed
    cases executed
    refine ⟨rfl, rfl, rfl, lookup_filtered_tag _ _, ?_⟩
    have joined : (lookup state.leases tag).isSome = true ∧
        state.leases.all (fun lease => decide (lease.parent ≠ some tag)) = true := by
      simpa only [Bool.and_eq_true] using allowed
    exact fun child member => of_decide_eq_true (List.all_eq_true.mp joined.2 child member)
  · cases executed

theorem endBorrow_no_children (state : State) (tag : Nat) (child : Lease)
    (member : child ∈ state.leases) (parent : child.parent = some tag) : endBorrow state tag = none := by
  cases executed : endBorrow state tag with
  | none => rfl
  | some next =>
    exact False.elim ((endBorrow_success state tag next executed).2.2.2.2 child member parent)

theorem ended_read_rejected (state : State) (tag : Nat) (next : State)
    (ended : endBorrow state tag = some next) (offset size : Nat) : read next tag offset size = none := by
  simp only [read, (endBorrow_success state tag next ended).2.2.2.1, Option.bind]

theorem ended_write_rejected (state : State) (tag : Nat) (next : State)
    (ended : endBorrow state tag = some next) (offset : Nat) (byte : Byte) : write next tag offset byte = none := by
  simp only [write, (endBorrow_success state tag next ended).2.2.2.1, Option.bind]

theorem rawWrite_success (state : State) (pointer : Pointer) (byte : Byte) (next : State)
    (executed : rawWrite state pointer byte = some next) :
    rawAllowed state .exclusive pointer ⟨1, 1⟩ = true ∧
    NativeByteMemory.storeByte state.memory pointer byte = some next.memory ∧
    next.nextTag = state.nextTag ∧ next.leases = state.leases := by
  unfold rawWrite at executed
  split at executed
  · rename_i allowed
    cases stored : NativeByteMemory.storeByte state.memory pointer byte with
    | none => simp only [stored, Option.map_none] at executed; cases executed
    | some memory =>
      simp only [stored, Option.map_some] at executed
      cases executed
      exact ⟨allowed, rfl, rfl, rfl⟩
  · cases executed

theorem write_success (state : State) (tag offset : Nat) (byte : Byte) (next : State)
    (executed : write state tag offset byte = some next) :
    ∃ lease pointer, lookup state.leases tag = some lease ∧ lease.mode = .exclusive ∧ offset < lease.layout.size ∧
      NativeByteRange.pointerAt lease.pointer offset = some pointer ∧
      throughAllowed state tag .exclusive pointer ⟨1, 1⟩ = true ∧
      NativeByteMemory.storeByte state.memory pointer byte = some next.memory ∧
      next.nextTag = state.nextTag ∧ next.leases = state.leases := by
  unfold write at executed
  cases found : lookup state.leases tag with
  | none => simp only [found, Option.bind] at executed; cases executed
  | some lease =>
    simp only [found, Option.bind] at executed
    split at executed
    · rename_i rights
      cases advanced : NativeByteRange.pointerAt lease.pointer offset with
      | none => simp only [advanced] at executed; cases executed
      | some pointer =>
        simp only [advanced] at executed
        split at executed
        · rename_i allowed
          cases stored : NativeByteMemory.storeByte state.memory pointer byte with
          | none => simp only [stored, Option.map_none] at executed; cases executed
          | some memory =>
            simp only [stored, Option.map_some] at executed
            cases executed
            exact ⟨lease, pointer, rfl, rights.1, rights.2, advanced, allowed, stored, rfl, rfl⟩
        · cases executed
    · cases executed

theorem read_success (state : State) (tag offset size : Nat) (output : List Byte)
    (executed : read state tag offset size = some output) :
    ∃ lease pointer, lookup state.leases tag = some lease ∧ offset + size ≤ lease.layout.size ∧
      NativeByteRange.pointerAt lease.pointer offset = some pointer ∧
      throughAllowed state tag .shared pointer ⟨size, 1⟩ = true ∧
      NativeByteRange.loadRange state.memory pointer ⟨size, 1⟩ = some output := by
  unfold read at executed
  cases found : lookup state.leases tag with
  | none => simp only [found, Option.bind] at executed; cases executed
  | some lease =>
    simp only [found, Option.bind] at executed
    split at executed
    · rename_i bound
      cases advanced : NativeByteRange.pointerAt lease.pointer offset with
      | none => simp only [advanced] at executed; cases executed
      | some pointer =>
        simp only [advanced] at executed
        split at executed
        · rename_i allowed
          exact ⟨lease, pointer, rfl, bound, advanced, allowed, executed⟩
        · cases executed
    · cases executed

theorem read_exact_length (state : State) (tag offset size : Nat) (output : List Byte)
    (executed : read state tag offset size = some output) : output.length = size := by
  obtain ⟨_, pointer, _, _, _, _, loaded⟩ := read_success state tag offset size output executed
  exact NativeByteRange.loadRange_length state.memory pointer ⟨size, 1⟩ output loaded

theorem write_changes_memory (state : State) (tag offset : Nat) (byte : Byte) (next : State)
    (executed : write state tag offset byte = some next) :
    ∃ pointer, NativeByteMemory.loadByte next.memory pointer = some byte := by
  obtain ⟨_, pointer, _, _, _, _, _, stored, _, _⟩ := write_success state tag offset byte next executed
  exact ⟨pointer, NativeByteMemory.storeByte_then_loadByte state.memory pointer byte next.memory stored⟩

theorem deallocate_success (state : State) (pointer : Pointer) (layout : Layout) (next : State)
    (executed : deallocate state pointer layout = some next) :
    rawAllowed state .exclusive pointer layout = true ∧
      NativeByteMemory.deallocate state.memory pointer layout = some next.memory ∧
      next.nextTag = state.nextTag ∧ next.leases = state.leases := by
  unfold deallocate at executed
  split at executed
  · rename_i allowed
    cases freed : NativeByteMemory.deallocate state.memory pointer layout with
    | none => simp only [freed, Option.map_none] at executed; cases executed
    | some memory =>
      simp only [freed, Option.map_some] at executed
      cases executed
      exact ⟨allowed, rfl, rfl, rfl⟩
  · cases executed

theorem deallocate_no_borrow_overlap (state : State) (pointer : Pointer) (layout : Layout) (next : State)
    (executed : deallocate state pointer layout = some next) (lease : Lease) (member : lease ∈ state.leases) :
    ¬ Overlap pointer layout lease.pointer lease.layout :=
  raw_exclusive_no_overlap state pointer layout (deallocate_success state pointer layout next executed).1 lease member

theorem deallocate_removes_allocation (state : State) (pointer : Pointer) (layout : Layout) (next : State)
    (executed : deallocate state pointer layout = some next) :
    next.memory.blocks.length + 1 = state.memory.blocks.length :=
  NativeByteMemory.deallocate_changes_live_count state.memory pointer layout next.memory
    (deallocate_success state pointer layout next executed).2.1

theorem allocate_success (state : State) (base : NativePointerStorage.Address) (layout : Layout)
    (pointer : Pointer) (next : State) (executed : allocate state base layout = some (pointer, next)) :
    NativeByteMemory.allocate state.memory base layout = some (pointer, next.memory) ∧
      next.nextTag = state.nextTag ∧ next.leases = state.leases := by
  unfold allocate at executed
  cases allocated : NativeByteMemory.allocate state.memory base layout with
  | none => simp only [allocated, Option.map_none] at executed; cases executed
  | some result =>
    rcases result with ⟨address, memory⟩
    simp only [allocated, Option.map_some] at executed
    cases executed
    exact ⟨rfl, rfl, rfl⟩

def Within (child older : Lease) : Prop :=
  (child.mode = .shared ∨ older.mode = .exclusive) ∧
    child.pointer.provenance = older.pointer.provenance ∧
    older.pointer.address.val ≤ child.pointer.address.val ∧
    child.pointer.address.val + child.layout.size ≤ older.pointer.address.val + older.layout.size

def LedgerValid (state : State) : Prop :=
  (∀ lease ∈ state.leases, lease.tag < state.nextTag ∧ NativeByteRange.Geometry lease.pointer lease.layout ∧
    match lease.parent with
    | none => True
    | some parent => parent < lease.tag ∧ ∃ older ∈ state.leases, older.tag = parent ∧ Within lease older) ∧
  state.leases.Pairwise (fun left right => left.tag ≠ right.tag)

def WellFormed (state : State) : Prop := NativeByteMemory.WellFormed state.memory ∧ LedgerValid state

theorem empty_wellFormed : WellFormed empty := by
  exact ⟨NativeByteMemory.empty_wellFormed, by simp [LedgerValid, empty]⟩

theorem ledger_transport (state next : State) (valid : LedgerValid state)
    (counter : next.nextTag = state.nextTag) (leases : next.leases = state.leases) : LedgerValid next := by
  unfold LedgerValid at *
  rw [counter, leases]
  exact valid

theorem borrow_wellFormed (state : State) (valid : WellFormed state) (parent : Option Nat)
    (mode : Mode) (pointer : Pointer) (layout : Layout) (tag : Nat) (next : State)
    (executed : borrow state parent mode pointer layout = some (tag, next)) : WellFormed next := by
  obtain ⟨sameTag, memory, counter, leases, allowed, bytes, loaded⟩ := borrow_success state parent mode pointer layout tag next executed
  have geometry := NativeByteRange.loadRange_geometry state.memory pointer layout bytes loaded
  constructor
  · rw [memory]; exact valid.1
  · constructor
    · intro lease member
      rw [leases] at member
      rcases List.mem_cons.mp member with fresh | old
      · subst lease
        refine ⟨by change tag < next.nextTag; omega, geometry, ?_⟩
        cases parent with
        | none => trivial
        | some id =>
          obtain ⟨older, found, before, modes, origin, lower, upper, _⟩ := parent_checked state id mode pointer layout allowed
          obtain ⟨member, same⟩ := lookup_selected state.leases id older found
          refine ⟨by change id < tag; omega, older, ?_, same, modes, origin, lower, upper⟩
          rw [leases]
          exact List.mem_cons_of_mem _ member
      · obtain ⟨before, shape, parentValid⟩ := valid.2.1 lease old
        refine ⟨by omega, shape, ?_⟩
        cases parental : lease.parent with
        | none => trivial
        | some id =>
          rw [parental] at parentValid
          obtain ⟨before, older, selected, same, parentScope⟩ := parentValid
          refine ⟨before, older, ?_, same, parentScope⟩
          rw [leases]
          exact List.mem_cons_of_mem _ selected
    · rw [leases, List.pairwise_cons]
      refine ⟨?_, valid.2.2⟩
      intro old member same
      have before := (valid.2.1 old member).1
      change tag = old.tag at same
      omega

theorem endBorrow_wellFormed (state : State) (valid : WellFormed state) (tag : Nat) (next : State)
    (executed : endBorrow state tag = some next) : WellFormed next := by
  obtain ⟨memory, counter, leases, _, noChild⟩ := endBorrow_success state tag next executed
  constructor
  · rw [memory]; exact valid.1
  · constructor
    · intro lease member
      rw [leases] at member
      obtain ⟨old, _⟩ := List.mem_filter.mp member
      obtain ⟨before, geometry, parentValid⟩ := valid.2.1 lease old
      refine ⟨by omega, geometry, ?_⟩
      cases parental : lease.parent with
      | none => trivial
      | some id =>
        rw [parental] at parentValid
        obtain ⟨before, older, selected, same, parentScope⟩ := parentValid
        refine ⟨before, older, ?_, same, parentScope⟩
        rw [leases]
        apply List.mem_filter.mpr
        refine ⟨selected, decide_eq_true ?_⟩
        intro ended
        apply noChild lease old
        rw [parental, ← same, ended]
    · rw [leases]
      exact valid.2.2.sublist (List.filter_sublist)

theorem rawWrite_wellFormed (state : State) (valid : WellFormed state) (pointer : Pointer) (byte : Byte)
    (next : State) (executed : rawWrite state pointer byte = some next) : WellFormed next := by
  obtain ⟨_, stored, counter, leases⟩ := rawWrite_success state pointer byte next executed
  exact ⟨NativeByteMemory.store_wellFormed state.memory valid.1 pointer byte next.memory stored,
    ledger_transport state next valid.2 counter leases⟩

theorem write_wellFormed (state : State) (valid : WellFormed state) (tag offset : Nat) (byte : Byte)
    (next : State) (executed : write state tag offset byte = some next) : WellFormed next := by
  obtain ⟨_, pointer, _, _, _, _, _, stored, counter, leases⟩ := write_success state tag offset byte next executed
  exact ⟨NativeByteMemory.store_wellFormed state.memory valid.1 pointer byte next.memory stored,
    ledger_transport state next valid.2 counter leases⟩

theorem allocate_wellFormed (state : State) (valid : WellFormed state) (base : NativePointerStorage.Address)
    (layout : Layout) (pointer : Pointer) (next : State) (executed : allocate state base layout = some (pointer, next)) :
    WellFormed next := by
  obtain ⟨allocated, counter, leases⟩ := allocate_success state base layout pointer next executed
  exact ⟨NativeByteMemory.allocate_wellFormed state.memory valid.1 base layout pointer next.memory allocated,
    ledger_transport state next valid.2 counter leases⟩

theorem deallocate_wellFormed (state : State) (valid : WellFormed state) (pointer : Pointer) (layout : Layout)
    (next : State) (executed : deallocate state pointer layout = some next) : WellFormed next := by
  obtain ⟨_, freed, counter, leases⟩ := deallocate_success state pointer layout next executed
  exact ⟨NativeByteMemory.deallocate_wellFormed state.memory valid.1 pointer layout next.memory freed,
    ledger_transport state next valid.2 counter leases⟩

inductive Step : State → State → Prop where
  | allocate (state : State) (base : NativePointerStorage.Address) (layout : Layout) (pointer : Pointer) (next : State)
      (executed : NativeByteBorrow.allocate state base layout = some (pointer, next)) : Step state next
  | borrow (state : State) (parent : Option Nat) (mode : Mode) (pointer : Pointer) (layout : Layout) (tag : Nat) (next : State)
      (executed : NativeByteBorrow.borrow state parent mode pointer layout = some (tag, next)) : Step state next
  | endBorrow (state : State) (tag : Nat) (next : State)
      (executed : NativeByteBorrow.endBorrow state tag = some next) : Step state next
  | rawWrite (state : State) (pointer : Pointer) (byte : Byte) (next : State)
      (executed : NativeByteBorrow.rawWrite state pointer byte = some next) : Step state next
  | write (state : State) (tag offset : Nat) (byte : Byte) (next : State)
      (executed : NativeByteBorrow.write state tag offset byte = some next) : Step state next
  | deallocate (state : State) (pointer : Pointer) (layout : Layout) (next : State)
      (executed : NativeByteBorrow.deallocate state pointer layout = some next) : Step state next

inductive Reachable : State → Prop where
  | empty : Reachable NativeByteBorrow.empty
  | step {state next : State} (previous : Reachable state) (executed : Step state next) : Reachable next

theorem step_wellFormed {state next : State} (valid : WellFormed state) (executed : Step state next) : WellFormed next := by
  cases executed with
  | allocate base layout pointer next executed => exact allocate_wellFormed state valid base layout pointer next executed
  | borrow parent mode pointer layout tag next executed => exact borrow_wellFormed state valid parent mode pointer layout tag next executed
  | endBorrow tag next executed => exact endBorrow_wellFormed state valid tag next executed
  | rawWrite pointer byte next executed => exact rawWrite_wellFormed state valid pointer byte next executed
  | write tag offset byte next executed => exact write_wellFormed state valid tag offset byte next executed
  | deallocate pointer layout next executed => exact deallocate_wellFormed state valid pointer layout next executed

theorem reachable_wellFormed {state : State} (reachable : Reachable state) : WellFormed state := by
  induction reachable with
  | empty => exact empty_wellFormed
  | step previous executed ih => exact step_wellFormed ih executed

theorem missing_read (state : State) (tag offset size : Nat) (missing : lookup state.leases tag = none) :
    read state tag offset size = none := by
  simp only [read, missing, Option.bind]

theorem missing_write (state : State) (tag offset : Nat) (byte : Byte) (missing : lookup state.leases tag = none) :
    write state tag offset byte = none := by
  simp only [write, missing, Option.bind]

theorem rawRead_success (state : State) (pointer : Pointer) (layout : Layout) (output : List Byte)
    (executed : rawRead state pointer layout = some output) :
    rawAllowed state .shared pointer layout = true ∧ NativeByteRange.loadRange state.memory pointer layout = some output := by
  unfold rawRead at executed
  split at executed
  · exact ⟨by assumption, executed⟩
  · cases executed

theorem rawRead_exclusive_conflict (state : State) (pointer : Pointer) (layout : Layout) (lease : Lease)
    (member : lease ∈ state.leases) (exclusive : lease.mode = .exclusive)
    (overlap : Overlap pointer layout lease.pointer lease.layout) : rawRead state pointer layout = none := by
  cases executed : rawRead state pointer layout with
  | none => rfl
  | some output =>
    have compatible := rawAllowed_selected state .shared pointer layout (rawRead_success state pointer layout output executed).1 lease member
    rcases compatible with shared | separate
    · rw [exclusive] at shared
      cases shared.2
    · exact False.elim (separate overlap)

theorem rawWrite_conflict (state : State) (pointer : Pointer) (byte : Byte) (lease : Lease)
    (member : lease ∈ state.leases) (overlap : Overlap pointer ⟨1, 1⟩ lease.pointer lease.layout) :
    rawWrite state pointer byte = none := by
  cases executed : rawWrite state pointer byte with
  | none => rfl
  | some next => exact False.elim (raw_exclusive_no_overlap state pointer ⟨1, 1⟩ (rawWrite_success state pointer byte next executed).1 lease member overlap)

theorem deallocate_conflict (state : State) (pointer : Pointer) (layout : Layout) (lease : Lease)
    (member : lease ∈ state.leases) (overlap : Overlap pointer layout lease.pointer lease.layout) :
    deallocate state pointer layout = none := by
  cases executed : deallocate state pointer layout with
  | none => rfl
  | some next => exact False.elim (deallocate_no_borrow_overlap state pointer layout next executed lease member overlap)

theorem through_exclusive_unrelated (state : State) (tag : Nat) (pointer : Pointer) (layout : Layout)
    (allowed : throughAllowed state tag .exclusive pointer layout = true) (lease : Lease) (member : lease ∈ state.leases)
    (other : lease.tag ≠ tag) (unrelated : ancestor state.leases state.nextTag lease.tag tag = false) :
    ¬ Overlap pointer layout lease.pointer lease.layout := by
  rcases through_selected state tag .exclusive pointer layout allowed lease member with same | parent | compatible
  · exact False.elim (other same)
  · rw [unrelated] at parent
    cases parent
  · rcases compatible with impossible | separate
    · cases impossible.1
    · exact separate

/-- Metadata decoding is for byte slices only; it does not mint Rust references. -/
def borrowSlice {mutable : Bool} (state : State) (parent : Option Nat) (mode : Mode)
    (pointer : NativeRawPointer.RawPtr (List Byte) mutable) : Option (Nat × State) :=
  match pointer.metadata with
  | .slice length => borrow state parent mode pointer.storage ⟨length.val, 1⟩
  | .thin | .vtable _ => none

theorem lookup_none_iff (leases : List Lease) (tag : Nat) :
    lookup leases tag = none ↔ ∀ lease ∈ leases, lease.tag ≠ tag := by
  induction leases with
  | nil => simp [lookup]
  | cons head tail ih =>
    by_cases same : head.tag = tag
    · simp [lookup, same]
    · simp only [lookup, ite_eq_right same, ih, List.mem_cons, forall_eq_or_imp]
      exact ⟨fun rest => ⟨same, rest⟩, fun both => both.2⟩

theorem endBorrow_found (state : State) (tag : Nat) (next : State)
    (executed : endBorrow state tag = some next) : ∃ lease, lookup state.leases tag = some lease := by
  unfold endBorrow at executed
  split at executed
  · rename_i allowed
    have joined : (lookup state.leases tag).isSome = true ∧
        state.leases.all (fun lease => decide (lease.parent ≠ some tag)) = true := by
      simpa only [Bool.and_eq_true] using allowed
    cases found : lookup state.leases tag with
    | none => rw [found] at joined; cases joined.1
    | some lease => exact ⟨lease, rfl⟩
  · cases executed

theorem step_counter {state next : State} (executed : Step state next) : state.nextTag ≤ next.nextTag := by
  cases executed with
  | allocate base layout pointer next executed => rw [(allocate_success state base layout pointer next executed).2.1]; omega
  | borrow parent mode pointer layout tag next executed => rw [(borrow_success state parent mode pointer layout tag next executed).2.2.1]; omega
  | endBorrow tag next executed => rw [(endBorrow_success state tag next executed).2.1]; omega
  | rawWrite pointer byte next executed => rw [(rawWrite_success state pointer byte next executed).2.2.1]; omega
  | write tag offset byte next executed =>
    obtain ⟨_, _, _, _, _, _, _, _, counter, _⟩ := write_success state tag offset byte next executed
    rw [counter]; omega
  | deallocate pointer layout next executed => rw [(deallocate_success state pointer layout next executed).2.2.1]; omega

theorem step_keeps_revoked {state next : State} (executed : Step state next) (tag : Nat)
    (before : tag < state.nextTag) (absent : lookup state.leases tag = none) : lookup next.leases tag = none := by
  cases executed with
  | allocate base layout pointer next executed => rw [(allocate_success state base layout pointer next executed).2.2]; exact absent
  | borrow parent mode pointer layout fresh next executed =>
    obtain ⟨same, _, _, leases, _, _⟩ := borrow_success state parent mode pointer layout fresh next executed
    rw [leases]
    unfold lookup
    have different : fresh ≠ tag := by omega
    rw [ite_eq_right different]
    exact absent
  | endBorrow ended next executed =>
    rw [(endBorrow_success state ended next executed).2.2.1]
    apply (lookup_none_iff _ tag).mpr
    intro lease member
    exact (lookup_none_iff state.leases tag).mp absent lease (List.mem_filter.mp member).1
  | rawWrite pointer byte next executed => rw [(rawWrite_success state pointer byte next executed).2.2.2]; exact absent
  | write current offset byte next executed =>
    obtain ⟨_, _, _, _, _, _, _, _, _, leases⟩ := write_success state current offset byte next executed
    rw [leases]
    exact absent
  | deallocate pointer layout next executed => rw [(deallocate_success state pointer layout next executed).2.2.2]; exact absent

inductive Runs (start : State) : State → Prop where
  | refl : Runs start start
  | step {state next : State} (previous : Runs start state) (executed : Step state next) : Runs start next

theorem runs_keep_revoked {state next : State} (executed : Runs state next) (tag : Nat)
    (before : tag < state.nextTag) (absent : lookup state.leases tag = none) :
    tag < next.nextTag ∧ lookup next.leases tag = none := by
  induction executed with
  | refl => exact ⟨before, absent⟩
  | step previous transition ih =>
    exact ⟨Nat.lt_of_lt_of_le ih.1 (step_counter transition), step_keeps_revoked transition tag ih.1 ih.2⟩

theorem ended_tag_never_returns (state : State) (valid : WellFormed state) (tag : Nat) (ended next : State)
    (released : endBorrow state tag = some ended) (future : Runs ended next) : lookup next.leases tag = none := by
  obtain ⟨lease, found⟩ := endBorrow_found state tag ended released
  obtain ⟨member, same⟩ := lookup_selected state.leases tag lease found
  have before := (valid.2.1 lease member).1
  have counter := (endBorrow_success state tag ended released).2.1
  have missing := (endBorrow_success state tag ended released).2.2.2.1
  exact (runs_keep_revoked future tag (by omega) missing).2

inductive ParentPath (leases : List Lease) : Nat → Nat → Prop where
  | direct (older child : Nat) (lease : Lease) (found : lookup leases child = some lease)
      (parent : lease.parent = some older) : ParentPath leases older child
  | trans (older middle child : Nat) (lease : Lease) (found : lookup leases child = some lease)
      (parent : lease.parent = some middle) (previous : ParentPath leases older middle) : ParentPath leases older child

theorem ancestor_sound (leases : List Lease) (fuel older child : Nat)
    (accepted : ancestor leases fuel older child = true) : ParentPath leases older child := by
  induction fuel generalizing child with
  | zero => cases accepted
  | succ fuel ih =>
    unfold ancestor at accepted
    cases found : lookup leases child with
    | none => simp only [found] at accepted; cases accepted
    | some lease =>
      rw [found] at accepted
      cases parent : lease.parent with
      | none => simp only [parent] at accepted; cases accepted
      | some middle =>
        simp only [parent, Bool.or_eq_true, decide_eq_true_eq] at accepted
        rcases accepted with same | earlier
        · subst older
          exact ParentPath.direct middle child lease found parent
        · exact ParentPath.trans older middle child lease found parent (ih middle earlier)

theorem parent_before (state : State) (valid : LedgerValid state) (older child : Nat) (lease : Lease)
    (found : lookup state.leases child = some lease) (parent : lease.parent = some older) : older < child := by
  obtain ⟨member, tagEq⟩ := lookup_selected state.leases child lease found
  have edge := (valid.1 lease member).2.2
  rw [parent] at edge
  omega

theorem parentPath_strict (state : State) (valid : LedgerValid state) (older child : Nat)
    (path : ParentPath state.leases older child) : older < child := by
  induction path with
  | direct child lease found parent => exact parent_before state valid older child lease found parent
  | trans middle child lease found parent previous ih =>
    exact Nat.lt_trans ih (parent_before state valid middle child lease found parent)

theorem ancestor_irreflexive (state : State) (valid : LedgerValid state) (fuel tag : Nat) :
    ancestor state.leases fuel tag tag = false := by
  cases result : ancestor state.leases fuel tag tag with
  | false => rfl
  | true =>
    have impossible := parentPath_strict state valid tag tag (ancestor_sound state.leases fuel tag tag result)
    omega

theorem ancestor_complete (state : State) (valid : LedgerValid state) (older child : Nat)
    (path : ParentPath state.leases older child) (fuel : Nat) (bound : child < fuel) :
    ancestor state.leases fuel older child = true := by
  induction path generalizing fuel with
  | direct child lease found parent =>
    cases fuel with
    | zero => omega
    | succ fuel => simp only [ancestor, found, parent, decide_true, Bool.true_or]
  | trans middle child lease found parent previous ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have before := parent_before state valid middle child lease found parent
      have accepted := ih fuel (by omega)
      simp only [ancestor, found, parent, accepted, Bool.or_true]

theorem ancestor_iff (state : State) (valid : LedgerValid state) (older child : Nat) (lease : Lease)
    (found : lookup state.leases child = some lease) :
    ancestor state.leases state.nextTag older child = true ↔ ParentPath state.leases older child := by
  constructor
  · exact ancestor_sound state.leases state.nextTag older child
  · intro path
    obtain ⟨member, same⟩ := lookup_selected state.leases child lease found
    have before := (valid.1 lease member).1
    exact ancestor_complete state valid older child path state.nextTag (by omega)

end FormalProof4FHE.HasteBoots.NativeByteBorrow
