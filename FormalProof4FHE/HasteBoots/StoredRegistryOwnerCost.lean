module
public import FormalProof4FHE.HasteBoots.StoredMetadataCost
public import FormalProof4FHE.HasteBoots.NativeSourceRegistry
@[expose] public section

/-! Charged first-original registry ownership over complete stored context/root
keys. Every original slot participates, including unused aliases. The result
matches NativeSourceRegistry.owner; no used-slot filter, root-only equality,
functional digest comparison or registry permutation executes. -/
namespace FormalProof4FHE.HasteBoots.StoredRegistryOwnerCost
open SolverOperationCost (Run)
open StoredSourceVectorReadCost (Source Sources sourceView view)

def first (key : Source) : List Source → Run (Option ℕ)
  | [] => ⟨none,1⟩
  | head::tail =>
    let same := StoredMetadataCost.sourceEqual head key
    if same.value then ⟨some 0,same.cost+3⟩
    else
      let rest := first key tail
      ⟨rest.value.map Nat.succ,same.cost+rest.cost+4⟩

theorem first_cost (key : Source) (values : List Source) :
    (first key values).cost ≤ 1327*values.length+1 := by
  induction values with
  | nil => simp [first]
  | cons head tail ih =>
    have compared := StoredMetadataCost.sourceEqual_cost head key
    simp only [first,List.length_cons]
    split <;> dsimp only <;> omega

theorem first_at (key : Source) (values : List Source) (index : ℕ) (bound : index < values.length)
    (selected : values[index] = key)
    (earliest : ∀ i (before : i < index), values[i]'(before.trans bound) ≠ key) :
    (first key values).value = some index := by
  induction values generalizing index with
  | nil => simp only [List.length_nil] at bound; omega
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem_cons_zero] at selected
      simp only [first,StoredMetadataCost.sourceEqual_value,selected,decide_true,ite_true]
    | succ index =>
      have different : head ≠ key := earliest 0 (by omega)
      have tailBound : index < tail.length := by simp only [List.length_cons] at bound; omega
      have tailSelected : tail[index] = key := by simpa only [List.getElem_cons_succ] using selected
      have tailEarliest : ∀ i (before : i < index), tail[i]'(before.trans tailBound) ≠ key := by
        intro i before
        exact earliest (i+1) (by omega)
      have continued := ih index tailBound tailSelected tailEarliest
      simp only [first,StoredMetadataCost.sourceEqual_value,different,decide_false,Bool.false_eq_true,
        ite_false,continued,Option.map_some]

def readAt : ℕ → List Source → Run (Option Source)
  | _,[] => ⟨none,1⟩
  | 0,head::_ => ⟨some head,2⟩
  | index+1,_::tail =>
    let rest := readAt index tail
    ⟨rest.value,rest.cost+2⟩

theorem readAt_value (index : ℕ) (values : List Source) : (readAt index values).value = values[index]? := by
  induction values generalizing index with
  | nil => simp [readAt]
  | cons head tail ih => cases index <;> simp only [readAt,List.getElem?_cons_zero,List.getElem?_cons_succ,ih]

theorem readAt_cost (index : ℕ) (values : List Source) : (readAt index values).cost ≤ 2*index+2 := by
  induction values generalizing index with
  | nil => simp only [readAt]; omega
  | cons head tail ih =>
    cases index with
    | zero => exact le_rfl
    | succ index => have rest := ih index; simp only [readAt]; omega

def owner (sources : Sources) (position : Fin sources.val.length) : Run (Option ℕ) :=
  let key := readAt position.val sources.val
  match key.value with
  | none => ⟨none,key.cost+2⟩
  | some value =>
    let selected := first value sources.val
    ⟨selected.value,key.cost+selected.cost+3⟩

def position (sources : Sources) (index : Fin sources.val.length) : Fin (view sources).val.length :=
  ⟨index.val,by simpa only [view,List.length_map] using index.isLt⟩

theorem view_get (sources : Sources) (index : Fin sources.val.length) :
    (view sources).val.get (position sources index) = sourceView (sources.val.get index) := by
  simp only [view,position,List.get_eq_getElem,List.getElem_map]

theorem owner_value (sources : Sources) (index : Fin sources.val.length) :
    (owner sources index).value = some (NativeSourceRegistry.owner (view sources) (position sources index)).val := by
  let nativeOwner := NativeSourceRegistry.owner (view sources) (position sources index)
  let storedOwner : Fin sources.val.length := ⟨nativeOwner.val,by
    have bound := nativeOwner.isLt
    simpa only [view,List.length_map] using bound⟩
  have ownerPosition : position sources storedOwner = nativeOwner := by apply Fin.ext; rfl
  have matched := NativeSourceRegistry.owner_key (view sources) (position sources index)
  change (view sources).val.get nativeOwner = (view sources).val.get (position sources index) at matched
  rw [← ownerPosition,view_get,view_get] at matched
  have selected : sources.val.get storedOwner = sources.val.get index := StoredMetadataCost.sourceView_injective matched
  have earliest : ∀ i (before : i < storedOwner.val), sources.val[i]'(before.trans storedOwner.isLt) ≠ sources.val.get index := by
    intro i before same
    let earlier : Fin sources.val.length := ⟨i,before.trans storedOwner.isLt⟩
    have different := NativeSourceRegistry.owner_first (view sources) (position sources index) (position sources earlier) before
    rw [view_get,view_get] at different
    exact different (congrArg sourceView same)
  have chosen := first_at (sources.val.get index) sources.val storedOwner.val storedOwner.isLt selected earliest
  simp only [owner,readAt_value,List.getElem?_eq_getElem index.isLt]
  exact chosen

theorem owner_cost (sources : Sources) (index : Fin sources.val.length) :
    (owner sources index).cost ≤ 1329*sources.val.length+6 := by
  have read := readAt_cost index.val sources.val
  have bound := index.isLt
  simp only [owner]
  split
  · dsimp only; omega
  · rename_i key found
    have selected := first_cost key sources.val
    dsimp only
    omega
end FormalProof4FHE.HasteBoots.StoredRegistryOwnerCost
