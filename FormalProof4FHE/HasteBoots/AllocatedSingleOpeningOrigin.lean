module
public import FormalProof4FHE.HasteBoots.SingleOpeningConstructorBounds
public import FormalProof4FHE.HasteBoots.NativeGoldParameterStore
@[expose] public section

/-! Single-opening code provenance from an original immutable parameter-store
entry. The selected logical handle and complete parameter association are
explicit boundary evidence; these are not physical pointer/heap proofs. -/
namespace FormalProof4FHE.HasteBoots.AllocatedSingleOpeningOrigin
open NativeGoldPcsExecution (Context)
open CacheBackedSingleOpening (Origin)
open NativeGoldParameterStore (Entry)
noncomputable section

def ofEntry (entry : Entry) (good : NativeGoldParameterStore.GoodEntry entry) (ctx : Context)
    (same : ctx.parameters = entry.initialized.parameters) : Origin ctx :=
  CacheBackedSingleOpening.ofInitialization entry.header entry.request entry.config good.1 entry.initialized good.2 ctx same

theorem entry_data (entry : Entry) (good : NativeGoldParameterStore.GoodEntry entry) (ctx : Context)
    (same : ctx.parameters = entry.initialized.parameters) :
    (ofEntry entry good ctx same).request = entry.request ∧ (ofEntry entry good ctx same).config = entry.config := ⟨rfl,rfl⟩

theorem found_good (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (handle : ℕ) (entry : Entry) (found : entries[handle]? = some entry) : NativeGoldParameterStore.GoodEntry entry :=
  NativeGoldParameterStore.reachable_good entries reachable entry (List.mem_of_getElem? found)

def ofFound (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (handle : ℕ) (entry : Entry) (found : entries[handle]? = some entry) (ctx : Context)
    (same : ctx.parameters = entry.initialized.parameters) : Origin ctx :=
  ofEntry entry (found_good entries reachable handle entry found) ctx same

theorem found_data (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (handle : ℕ) (entry : Entry) (found : entries[handle]? = some entry) (ctx : Context)
    (same : ctx.parameters = entry.initialized.parameters) :
    (ofFound entries reachable handle entry found ctx same).request = entry.request ∧
      (ofFound entries reachable handle entry found ctx same).config = entry.config := ⟨rfl,rfl⟩

/-- The actual helper context's full parameters must refer to this selected
entry. Code equality alone cannot provide that association. -/
def helperReceipt {B Memory : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (handle : ℕ) (entry : Entry) (found : entries[handle]? = some entry)
    (ctx : NativeGoldHelperVerification.Context B) (same : ctx.helper = entry.initialized.parameters)
    (receipt : NativeGoldHelperVerification.Receipt Memory) :
    Origin (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call) :=
  ofFound entries reachable handle entry found _ same

theorem helper_data {B Memory : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (handle : ℕ) (entry : Entry) (found : entries[handle]? = some entry)
    (ctx : NativeGoldHelperVerification.Context B) (same : ctx.helper = entry.initialized.parameters)
    (receipt : NativeGoldHelperVerification.Receipt Memory) :
    (helperReceipt entries reachable handle entry found ctx same receipt).request = entry.request ∧
      (helperReceipt entries reachable handle entry found ctx same receipt).config = entry.config := ⟨rfl,rfl⟩

end
end FormalProof4FHE.HasteBoots.AllocatedSingleOpeningOrigin
