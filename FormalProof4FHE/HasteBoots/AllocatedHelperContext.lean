module
public import FormalProof4FHE.HasteBoots.AllocatedSingleOpeningOrigin
@[expose] public section

/-! Borrow the original helper parameter object from the immutable logical
store. Successful lookup derives the complete helper-parameter association;
no constructor is selected merely by matching code. Logical handles still
need application/physical pointer refinement. -/
namespace FormalProof4FHE.HasteBoots.AllocatedHelperContext
open NativeGoldParameterStore (Entry)
open NativeGoldHelperVerification (Context)

/-- Preserve the call template and read the original retained helper object. -/
def borrow {B : Type} (entries : List Entry) (handle : ℕ) (template : Context B) : Option (Context B) :=
  (entries[handle]?).map (fun entry => {template with helper := entry.initialized.parameters})

theorem borrow_spec {B : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (handle : ℕ) (template ctx : Context B) (borrowed : borrow entries handle template = some ctx) :
    ∃ entry : Entry, entries[handle]? = some entry ∧ NativeGoldParameterStore.GoodEntry entry ∧
      ctx = {template with helper := entry.initialized.parameters} := by
  obtain ⟨entry,found,same⟩ := Option.map_eq_some_iff.mp borrowed
  exact ⟨entry,found,AllocatedSingleOpeningOrigin.found_good entries reachable handle entry found,same.symm⟩

theorem helper_parameters {B : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (handle : ℕ) (template ctx : Context B) (borrowed : borrow entries handle template = some ctx) :
    ∃ entry : Entry, entries[handle]? = some entry ∧ NativeGoldParameterStore.GoodEntry entry ∧
      ctx.helper = entry.initialized.parameters := by
  obtain ⟨entry,found,good,same⟩ := borrow_spec entries reachable handle template ctx borrowed
  exact ⟨entry,found,good,congrArg (fun ctx => ctx.helper) same⟩

theorem missing {B : Type} (entries : List Entry) (handle : ℕ) (template : Context B)
    (absent : entries[handle]? = none) : borrow entries handle template = none := by
  simp only [borrow,absent,Option.map_none]

end FormalProof4FHE.HasteBoots.AllocatedHelperContext
