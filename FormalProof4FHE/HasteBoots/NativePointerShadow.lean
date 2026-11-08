module
public import FormalProof4FHE.HasteBoots.NativePointerRepresentation
public import Mathlib.Data.List.Basic
@[expose] public section

/-! Finite per-byte origin metadata, keyed by the containing allocation and
byte address. It is ghost data, not actor authentication or a work model. -/
namespace FormalProof4FHE.HasteBoots.NativePointerShadow
open NativePointerStorage (Origin)

structure Cell where
  owner : Origin
  address : Nat
  origin : Origin
  deriving DecidableEq

def lookup : List Cell → Origin → Nat → Option Origin
  | [], _, _ => none
  | cell :: tail, owner, address =>
    if cell.owner = owner ∧ cell.address = address then some cell.origin else lookup tail owner address

/-- Integer-byte writes erase origin metadata even when bits do not change. -/
def clear (cells : List Cell) (owner : Origin) (base size : Nat) : List Cell :=
  cells.filter (fun cell => decide (cell.owner ≠ owner ∨ cell.address < base ∨ base + size ≤ cell.address))

def install (owner : Origin) : Nat → List (Option Origin) → List Cell → List Cell
  | _, [], cells => cells
  | base, none :: tail, cells => install owner (base + 1) tail cells
  | base, some origin :: tail, cells => ⟨owner, base, origin⟩ :: install owner (base + 1) tail cells

def replace (cells : List Cell) (owner : Origin) (base : Nat) (origins : List (Option Origin)) : List Cell :=
  install owner base origins (clear cells owner base origins.length)

def snapshot (cells : List Cell) (owner : Origin) (base size : Nat) : List (Option Origin) :=
  (List.range size).map (fun index => lookup cells owner (base + index))

/-- Mixed origin fragments are rejected by this policy. No live-allocation
search converts address bits into provenance. -/
def uniform (cells : List Cell) (owner : Origin) (base size : Nat) : Option (Option Origin) :=
  let first := lookup cells owner base
  if (List.range size).all (fun index => decide (lookup cells owner (base + index) = first)) then some first else none

theorem lookup_selected (cells : List Cell) (owner : Origin) (address : Nat) (origin : Origin)
    (found : lookup cells owner address = some origin) :
    ∃ cell ∈ cells, cell.owner = owner ∧ cell.address = address ∧ cell.origin = origin := by
  induction cells with
  | nil => cases found
  | cons head tail ih =>
    unfold lookup at found
    split at found
    next matched => cases found; exact ⟨head, List.mem_cons_self, matched.1, matched.2, rfl⟩
    next =>
      obtain ⟨cell, member, ownerEq, addressEq, originEq⟩ := ih found
      exact ⟨cell, List.mem_cons_of_mem head member, ownerEq, addressEq, originEq⟩

theorem clear_inside (cells : List Cell) (owner : Origin) (base size address : Nat)
    (inside : base ≤ address ∧ address < base + size) : lookup (clear cells owner base size) owner address = none := by
  induction cells with
  | nil => rfl
  | cons head tail ih =>
    unfold clear
    rw [List.filter_cons]
    split
    next kept =>
      have outside := of_decide_eq_true kept
      have unmatched : ¬ (head.owner = owner ∧ head.address = address) := by
        intro matched
        rcases outside with different | before | after
        · exact different matched.1
        · omega
        · omega
      simp only [lookup, ite_eq_right unmatched]
      exact ih
    next => exact ih

theorem clear_outside (cells : List Cell) (owner other : Origin) (base size address : Nat)
    (outside : other ≠ owner ∨ address < base ∨ base + size ≤ address) :
    lookup (clear cells owner base size) other address = lookup cells other address := by
  induction cells with
  | nil => rfl
  | cons head tail ih =>
    unfold clear
    rw [List.filter_cons]
    split
    next =>
      simp only [lookup]
      split
      · rfl
      · exact ih
    next removed =>
      have unmatched : ¬ (head.owner = other ∧ head.address = address) := by
        intro matched
        apply removed
        apply decide_eq_true
        rcases outside with different | before | after
        · exact Or.inl (by intro equal; exact different (matched.1.symm.trans equal))
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))
      simp only [lookup, ite_eq_right unmatched]
      exact ih

theorem install_outside (cells : List Cell) (owner other : Origin) (base address : Nat) (origins : List (Option Origin))
    (outside : other ≠ owner ∨ address < base ∨ base + origins.length ≤ address) :
    lookup (install owner base origins cells) other address = lookup cells other address := by
  induction origins generalizing base with
  | nil => rfl
  | cons origin tail ih =>
    have later : other ≠ owner ∨ address < base + 1 ∨ base + 1 + tail.length ≤ address := by
      rcases outside with different | before | after
      · exact Or.inl different
      · exact Or.inr (Or.inl (by omega))
      · right; right; simp only [List.length_cons] at after; omega
    cases origin with
    | none => exact ih (base + 1) later
    | some value =>
      have unmatched : ¬ (owner = other ∧ base = address) := by
        intro matched
        rcases outside with different | before | after
        · exact different matched.1.symm
        · omega
        · simp only [List.length_cons] at after; omega
      simp only [install, lookup, ite_eq_right unmatched]
      exact ih (base + 1) later

theorem install_inside (cells : List Cell) (owner : Origin) (base : Nat) (origins : List (Option Origin)) (index : Nat)
    (inside : index < origins.length) :
    lookup (install owner base origins cells) owner (base + index) =
      match origins[index]? with | some (some origin) => some origin | _ => lookup cells owner (base + index) := by
  induction origins generalizing base index with
  | nil => cases inside
  | cons origin tail ih =>
    cases index with
    | zero =>
      cases origin with
      | none =>
        simp only [install, Nat.add_zero, List.getElem?_cons_zero]
        exact install_outside cells owner owner (base + 1) base tail (Or.inr (Or.inl (by omega)))
      | some value => simp only [install, Nat.add_zero, lookup, and_self, ite_true, List.getElem?_cons_zero]
    | succ index =>
      have address : base + (index + 1) = base + 1 + index := by omega
      have different : base ≠ base + 1 + index := by omega
      cases origin with
      | none => simpa only [install, List.getElem?_cons_succ, address] using ih (base + 1) index (by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using inside)
      | some value =>
        simp only [install, lookup, true_and, ite_eq_right different, List.getElem?_cons_succ, address]
        exact ih (base + 1) index (by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using inside)

theorem replace_inside (cells : List Cell) (owner : Origin) (base : Nat) (origins : List (Option Origin)) (index : Nat)
    (inside : index < origins.length) :
    lookup (replace cells owner base origins) owner (base + index) = (origins[index]?).bind id := by
  rw [replace, install_inside _ owner base origins index inside]
  rw [clear_inside cells owner base origins.length (base + index) (by omega)]
  cases found : origins[index]? with
  | none => rfl
  | some origin => cases origin <;> rfl

theorem snapshot_length (cells : List Cell) (owner : Origin) (base size : Nat) :
    (snapshot cells owner base size).length = size := by simp only [snapshot, List.length_map, List.length_range]

theorem uniform_of_lookup (cells : List Cell) (owner : Origin) (base size : Nat) (positive : 0 < size) (origin : Option Origin)
    (same : ∀ index < size, lookup cells owner (base + index) = origin) : uniform cells owner base size = some origin := by
  have first : lookup cells owner base = origin := by simpa only [Nat.add_zero] using same 0 positive
  have all : (List.range size).all (fun index => decide (lookup cells owner (base + index) = origin)) = true :=
    List.all_eq_true.mpr (fun index member => decide_eq_true (same index (List.mem_range.mp member)))
  simp only [uniform, first, all, ite_true]


theorem replace_outside (cells : List Cell) (owner queryOwner : Origin) (base address : Nat)
    (origins : List (Option Origin))
    (outside : queryOwner ≠ owner ∨ address < base ∨ base + origins.length ≤ address) :
    lookup (replace cells owner base origins) queryOwner address = lookup cells queryOwner address := by
  rw [replace, install_outside _ owner queryOwner base address origins outside]
  exact clear_outside cells owner queryOwner base origins.length address outside

theorem replace_uniform (cells : List Cell) (owner : Origin) (base size : Nat)
    (origin : Option Origin) (positive : 0 < size) :
    uniform (replace cells owner base (List.replicate size origin)) owner base size = some origin := by
  apply uniform_of_lookup _ owner base size positive origin
  intro index inside
  rw [replace_inside _ owner base _ index (by simpa using inside)]
  simp only [List.getElem?_replicate, inside, ite_true, Option.bind_some, id_eq]

theorem clear_uniform (cells : List Cell) (owner : Origin) (base size : Nat)
    (positive : 0 < size) : uniform (clear cells owner base size) owner base size = some none := by
  apply uniform_of_lookup _ owner base size positive none
  intro index inside
  exact clear_inside cells owner base size (base + index) (by omega)

end FormalProof4FHE.HasteBoots.NativePointerShadow
