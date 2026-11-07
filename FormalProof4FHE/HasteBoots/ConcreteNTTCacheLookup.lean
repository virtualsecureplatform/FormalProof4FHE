module
public import FormalProof4FHE.HasteBoots.ConcreteNTTGoldTable
@[expose] public section

/-! Literal first-match reads and append behavior of the native NTT vectors.
Duplicate keys are not silently merged or reordered. -/
namespace FormalProof4FHE.HasteBoots.ConcreteNTTCacheLookup
variable {α : Type}

def lookup : List (ℕ × α) → ℕ → Option α
  | [],_ => none
  | (storedKey,value)::tail,key => if storedKey = key then some value else lookup tail key

theorem first (entries : List (ℕ × α)) (key : ℕ) (value : α)
    (found : lookup entries key = some value) :
    ∃ prior tail, entries = prior ++ (key,value)::tail ∧ ∀ entry ∈ prior, entry.1 ≠ key := by
  induction entries with
  | nil => cases found
  | cons head tail ih =>
    rcases head with ⟨storedKey,storedValue⟩
    by_cases same : storedKey = key
    · subst storedKey
      simp only [lookup,ite_true] at found
      cases found
      exact ⟨[],tail,rfl,by simp⟩
    · simp only [lookup,same,ite_false] at found
      obtain ⟨prior,after,shape,earlier⟩ := ih found
      refine ⟨(storedKey,storedValue)::prior,after,?_,?_⟩
      · simpa only [List.cons_append] using congrArg (List.cons (storedKey,storedValue)) shape
      · intro entry member
        rcases List.mem_cons.mp member with rfl | member
        · exact same
        · exact earlier entry member

theorem member (entries : List (ℕ × α)) (key : ℕ) (value : α)
    (found : lookup entries key = some value) : (key,value) ∈ entries := by
  obtain ⟨prior,tail,rfl,_⟩ := first entries key value found
  simp

theorem none_iff (entries : List (ℕ × α)) (key : ℕ) :
    lookup entries key = none ↔ ∀ entry ∈ entries, entry.1 ≠ key := by
  induction entries with
  | nil => simp [lookup]
  | cons head tail ih =>
    rcases head with ⟨storedKey,value⟩
    by_cases same : storedKey = key <;> simp [lookup,same,ih]

theorem append (left right : List (ℕ × α)) (key : ℕ) :
    lookup (left++right) key = match lookup left key with
      | some value => some value
      | none => lookup right key := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨storedKey,value⟩
    by_cases same : storedKey = key <;> simp [lookup,same,ih]

theorem append_preserves (left right : List (ℕ × α)) (key : ℕ) (value : α)
    (found : lookup left key = some value) : lookup (left++right) key = some value := by
  rw [append,found]

theorem append_new (entries : List (ℕ × α)) (key : ℕ) (value : α)
    (missing : lookup entries key = none) : lookup (entries++[(key,value)]) key = some value := by
  rw [append,missing]
  simp only [lookup,ite_true]

end FormalProof4FHE.HasteBoots.ConcreteNTTCacheLookup
