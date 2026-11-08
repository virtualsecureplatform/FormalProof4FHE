module
public import FormalProof4FHE.HasteBoots.NativeUsizeMessage
public import FormalProof4FHE.HasteBoots.NativePointerRepresentation
@[expose] public section

/-! Thin pointer storage for the native 64-bit target. Addresses and allocation
generations are distinct data. A nonzero address alone grants no read access.
This is an operational storage specification, not a Rust allocator, provenance,
borrow, layout or physical-work refinement. In particular it does not replace
the rejected NonNull pattern in the source extraction gate. -/
namespace FormalProof4FHE.HasteBoots.NativePointerStorage

def NonNull (pointer : Pointer) : Prop := pointer.address.val ≠ 0

def readdress (pointer : Pointer) (address : Address) : Pointer :=
  ⟨address, pointer.provenance⟩

theorem readdress_provenance (pointer : Pointer) (address : Address) :
    (readdress pointer address).provenance = pointer.provenance := rfl

theorem readdress_original (pointer : Pointer) : readdress pointer pointer.address = pointer := by
  cases pointer
  rfl

theorem pointer_fields (left right : Pointer) :
    left = right ↔ left.address = right.address ∧ left.provenance = right.provenance := by
  cases left
  cases right
  simp only [Pointer.mk.injEq]

structure Cell (Value : Type) where
  origin : Origin
  address : Address
  nonzero : address.val ≠ 0
  value : Value

def pointer {Value : Type} (cell : Cell Value) : Pointer :=
  ⟨cell.address, some cell.origin⟩

theorem cell_nonnull {Value : Type} (cell : Cell Value) : NonNull (pointer cell) := cell.nonzero

def read {Value : Type} : List (Cell Value) → Pointer → Option Value
  | [], _ => none
  | cell :: tail, reference =>
      if reference.provenance = some cell.origin ∧ reference.address = cell.address
      then some cell.value else read tail reference

theorem read_head {Value : Type} (cell : Cell Value) (tail : List (Cell Value)) :
    read (cell :: tail) (pointer cell) = some cell.value := by
  simp only [read, pointer, and_self, ite_true]

theorem read_without_provenance {Value : Type} (heap : List (Cell Value))
    (reference : Pointer) (absent : reference.provenance = none) : read heap reference = none := by
  induction heap with
  | nil => rfl
  | cons cell tail ih => simp only [read, absent, reduceCtorEq, false_and, ite_false, ih]

theorem read_null {Value : Type} (heap : List (Cell Value)) (reference : Pointer)
    (zero : reference.address.val = 0) : read heap reference = none := by
  induction heap with
  | nil => rfl
  | cons cell tail ih =>
    have different : reference.address ≠ cell.address := by
      intro same
      apply cell.nonzero
      rw [← same]
      exact zero
    simp only [read, different, and_false, ite_false, ih]

theorem read_selected {Value : Type} (heap : List (Cell Value)) (reference : Pointer) (value : Value)
    (executed : read heap reference = some value) :
    ∃ cell ∈ heap, reference.provenance = some cell.origin ∧ reference.address = cell.address ∧ cell.value = value := by
  induction heap with
  | nil => cases executed
  | cons cell tail ih =>
    simp only [read] at executed
    split at executed
    · rename_i matched
      cases executed
      exact ⟨cell, List.mem_cons_self, matched.1, matched.2, rfl⟩
    · obtain ⟨selected, member, origin, address, stored⟩ := ih executed
      exact ⟨selected, List.mem_cons_of_mem cell member, origin, address, stored⟩

theorem read_nonnull {Value : Type} (heap : List (Cell Value)) (reference : Pointer) (value : Value)
    (executed : read heap reference = some value) : NonNull reference := by
  obtain ⟨cell, _, _, address, _⟩ := read_selected heap reference value executed
  unfold NonNull
  rw [address]
  exact cell.nonzero

def retire {Value : Type} : List (Cell Value) → Origin → List (Cell Value)
  | [], _ => []
  | cell :: tail, origin =>
      if cell.origin = origin then retire tail origin else cell :: retire tail origin

theorem read_retired {Value : Type} (heap : List (Cell Value)) (origin : Origin) (reference : Pointer)
    (same : reference.provenance = some origin) : read (retire heap origin) reference = none := by
  induction heap with
  | nil => rfl
  | cons cell tail ih =>
    by_cases retired : cell.origin = origin
    · simp only [retire, retired, ite_true, ih]
    · have different : reference.provenance ≠ some cell.origin := by
        rw [same]
        intro equal
        exact retired (Option.some.inj equal).symm
      simp only [retire, retired, ite_false, read, different, false_and, ih]

theorem read_retire_other {Value : Type} (heap : List (Cell Value)) (origin : Origin) (reference : Pointer)
    (different : reference.provenance ≠ some origin) : read (retire heap origin) reference = read heap reference := by
  induction heap with
  | nil => rfl
  | cons cell tail ih =>
    by_cases retired : cell.origin = origin
    · simp only [retire, retired, ite_true, read, different, false_and, ite_false, ih]
    · simp only [retire, retired, ite_false, read, ih]

theorem reused_address_stale {Value : Type} (heap : List (Cell Value)) (old fresh : Cell Value)
    (different : old.origin ≠ fresh.origin) :
    read (fresh :: retire heap old.origin) (pointer old) = none := by
  have origin_ne : (pointer old).provenance ≠ some fresh.origin := by
    intro same
    exact different (Option.some.inj same)
  simp only [read, origin_ne, false_and, ite_false]
  exact read_retired heap old.origin (pointer old) rfl

theorem reused_address_fresh {Value : Type} (heap : List (Cell Value)) (old fresh : Cell Value) :
    read (fresh :: retire heap old.origin) (pointer fresh) = some fresh.value := read_head fresh _

end FormalProof4FHE.HasteBoots.NativePointerStorage
