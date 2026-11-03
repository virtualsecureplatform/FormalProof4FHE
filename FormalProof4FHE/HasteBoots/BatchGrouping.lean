module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Find
public import Mathlib.Tactic.SplitIfs

@[expose] public section

/-!
# Stable native batch response grouping by trusted query-prefix keys

Native `query_groups` searches the representatives in insertion order and
appends a representative only for a previously unseen left query prefix.
This key-level spelling computes the same first-match group numbers. Every
computed group reads back the original key, and equal group numbers are
exactly equal keys. No group map or matching certificate is supplied by the
prover. Relating stored native source indices to these keys and Rust memory
refinement remains separate from this deterministic grouping semantics.
-/

namespace FormalProof4FHE.HasteBoots.BatchGrouping

variable {Key : Type} [DecidableEq Key]

/-- Return the updated first-seen representative keys and this key's group. -/
def step (representatives : List Key) (key : Key) : List Key × ℕ :=
  let index := representatives.findIdx (fun entry => decide (entry = key))
  if index < representatives.length then (representatives, index)
  else (representatives ++ [key], representatives.length)

/-- Remaining keys are processed in native input order; group indices already
assigned never change as the representative list grows. -/
def run (representatives : List Key) : List Key → List Key × List ℕ
  | [] => (representatives, [])
  | key :: rest =>
      let added := step representatives key
      let later := run added.1 rest
      (later.1, added.2 :: later.2)

def compute (keys : List Key) := run [] keys

theorem step_prefix (representatives : List Key) (key : Key) :
    representatives <+: (step representatives key).1 := by
  dsimp only [step]
  split_ifs
  · exact ⟨[], by simp⟩
  · exact ⟨[key], rfl⟩

theorem step_lookup (representatives : List Key) (key : Key) :
    (step representatives key).1[(step representatives key).2]? = some key := by
  dsimp only [step]
  split_ifs with found
  · have equal := List.findIdx_getElem (p := fun entry => decide (entry = key)) (w := found)
    simp only [decide_eq_true_eq] at equal
    exact (List.getElem?_eq_getElem found).trans (congrArg some equal)
  · simp

omit [DecidableEq Key] in
theorem preserve_lookup {first later : List Key} (extension : first <+: later)
    {index : ℕ} {key : Key} (lookup : first[index]? = some key) : later[index]? = some key := by
  obtain ⟨rest, rfl⟩ := extension
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp lookup
  exact (List.getElem?_append_left bound).trans lookup

theorem run_prefix (representatives keys : List Key) : representatives <+: (run representatives keys).1 := by
  induction keys generalizing representatives with
  | nil => exact ⟨[], by simp [run]⟩
  | cons key rest ih => exact (step_prefix representatives key).trans (ih (step representatives key).1)

/-- All group indices are in range and point to the correct original keys,
even after subsequent unseen keys extend the representative list. -/
theorem run_valid (representatives keys : List Key) :
    List.Forall₂ (fun key index => (run representatives keys).1[index]? = some key) keys (run representatives keys).2 := by
  induction keys generalizing representatives with
  | nil => exact List.Forall₂.nil
  | cons key rest ih =>
    exact List.Forall₂.cons
      (preserve_lookup (run_prefix (step representatives key).1 rest) (step_lookup representatives key))
      (ih (step representatives key).1)

theorem step_nodup (representatives : List Key) (key : Key) (valid : representatives.Nodup) :
    (step representatives key).1.Nodup := by
  dsimp only [step]
  split_ifs with found
  · exact valid
  · have absent : key ∉ representatives := by
      intro member
      exact found (List.findIdx_lt_length_of_exists ⟨key, member, by simp⟩)
    simp [List.nodup_append, valid]
    intro entry member equal
    subst entry
    exact absent member

theorem run_nodup (representatives keys : List Key) (valid : representatives.Nodup) :
    (run representatives keys).1.Nodup := by
  induction keys generalizing representatives with
  | nil => exact valid
  | cons key rest ih => exact ih _ (step_nodup representatives key valid)

theorem representatives_nodup (keys : List Key) : (compute keys).1.Nodup := run_nodup [] keys (by simp)

theorem groups_length (keys : List Key) : (compute keys).2.length = keys.length := (run_valid [] keys).length_eq.symm

theorem group_lookup (keys : List Key) (position : Fin keys.length) :
    (compute keys).1[(compute keys).2[position.val]'(by rw [groups_length]; exact position.isLt)]? =
      some (keys.get position) := by
  exact (run_valid [] keys).get position.isLt (by
    change position.val < (compute keys).2.length
    rw [groups_length]
    exact position.isLt)

/-- A typed group index computed from the actual trusted key list. -/
def groupOf (keys : List Key) (position : Fin keys.length) : Fin (compute keys).1.length :=
  ⟨(compute keys).2[position.val]'(by rw [groups_length]; exact position.isLt), by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp (group_lookup keys position)
    exact bound⟩

theorem group_key (keys : List Key) (position : Fin keys.length) :
    (compute keys).1.get (groupOf keys position) = keys.get position := by
  have lookup := group_lookup keys position
  change (compute keys).1[(groupOf keys position).val]? = some (keys.get position) at lookup
  rw [List.getElem?_eq_getElem (groupOf keys position).isLt] at lookup
  exact Option.some.inj lookup

/-- Response aliasing occurs precisely for equal left-prefix keys, so a shared
left response cannot silently be reused for an unrelated query prefix. -/
theorem groupOf_eq_iff (keys : List Key) (first second : Fin keys.length) :
    groupOf keys first = groupOf keys second ↔ keys.get first = keys.get second := by
  constructor
  · intro equal
    rw [← group_key keys first, ← group_key keys second, equal]
  · intro equal
    apply Fin.ext
    apply ((representatives_nodup keys).getElem_inj).mp
    change (compute keys).1.get (groupOf keys first) = (compute keys).1.get (groupOf keys second)
    rw [group_key, group_key, equal]

/-- Representatives arise only from keys already present in the input. -/
theorem step_mem (representatives : List Key) (key entry : Key) :
    entry ∈ (step representatives key).1 ↔ entry ∈ representatives ∨ entry = key := by
  dsimp only [step]
  split_ifs with found
  · have equal := List.findIdx_getElem (p := fun value => decide (value = key)) (w := found)
    simp only [decide_eq_true_eq] at equal
    have keyMem : key ∈ representatives := equal ▸ List.getElem_mem found
    constructor
    · exact Or.inl
    · rintro (member | same)
      · exact member
      · exact same.symm ▸ keyMem
  · simp

theorem run_mem (representatives keys : List Key) {entry : Key}
    (member : entry ∈ (run representatives keys).1) : entry ∈ representatives ∨ entry ∈ keys := by
  induction keys generalizing representatives with
  | nil => exact Or.inl member
  | cons key rest ih =>
    obtain old | remaining := ih (step representatives key).1 member
    · obtain old | same := (step_mem representatives key entry).mp old
      · exact Or.inl old
      · exact Or.inr (same ▸ List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem key remaining)

theorem representatives_mem (keys : List Key) {key : Key} (member : key ∈ (compute keys).1) : key ∈ keys := by
  simpa only [List.not_mem_nil, false_or] using run_mem [] keys member

/-- Recover the first original query supplying each representative prefix. -/
def representative (keys : List Key) (group : Fin (compute keys).1.length) : Fin keys.length :=
  ⟨keys.findIdx (fun key => decide (key = (compute keys).1.get group)),
    List.findIdx_lt_length_of_exists ⟨(compute keys).1.get group,
      representatives_mem keys (List.getElem_mem group.isLt), by simp⟩⟩

theorem representative_key (keys : List Key) (group : Fin (compute keys).1.length) :
    keys.get (representative keys group) = (compute keys).1.get group := by
  have correct := List.findIdx_getElem (p := fun key => decide (key = (compute keys).1.get group))
    (w := (representative keys group).isLt)
  simpa only [decide_eq_true_eq, representative, List.get_eq_getElem] using correct

theorem representative_first (keys : List Key) (group : Fin (compute keys).1.length)
    (position : Fin keys.length) (earlier : position.val < (representative keys group).val) :
    keys.get position ≠ (compute keys).1.get group := by
  have absent := List.not_of_lt_findIdx
    (p := fun key => decide (key = (compute keys).1.get group)) earlier
  simpa using absent

theorem representative_group_key (keys : List Key) (position : Fin keys.length) :
    keys.get (representative keys (groupOf keys position)) = keys.get position :=
  (representative_key keys (groupOf keys position)).trans (group_key keys position)

end FormalProof4FHE.HasteBoots.BatchGrouping
