module
public import FormalProof4FHE.HasteBoots.AllocatedHelperContext
@[expose] public section

/-! Assemble one native lookup context by collecting the original source
references and borrowing the original helper object from one immutable store.
The proof/template and all execution fuels are retained. This is the logical
application adapter, not a Rust pointer/heap or physical cost refinement. -/
namespace FormalProof4FHE.HasteBoots.AllocatedLookupContext
open NativeGoldParameterStore (Entry Reference)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)

def assemble {B : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference) (template : Context B) : Option (Context B) :=
  (NativeGoldParameterStore.registry entries references).bind (fun registry =>
    AllocatedHelperContext.borrow entries helperHandle {template with registry := registry})

/-- Both associations are consequences of the actual assembly operation.
Original aliases and unused references keep their order and multiplicity. -/
theorem assemble_spec {B : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template ctx : Context B) (assembled : assemble entries helperHandle references template = some ctx) :
    NativeGoldParameterStore.registry entries references = some ctx.registry ∧
      AllocatedHelperContext.borrow entries helperHandle {template with registry := ctx.registry} = some ctx := by
  obtain ⟨registry,collected,borrowed⟩ := Option.bind_eq_some_iff.mp assembled
  obtain ⟨entry,found,same⟩ := Option.map_eq_some_iff.mp borrowed
  have retained : ctx.registry = registry := (congrArg (fun ctx => ctx.registry) same).symm
  exact ⟨retained ▸ collected,retained ▸ borrowed⟩

theorem helper_entry {B : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (helperHandle : ℕ) (references : Vector Reference) (template ctx : Context B)
    (assembled : assemble entries helperHandle references template = some ctx) :
    ∃ entry : Entry, entries[helperHandle]? = some entry ∧ NativeGoldParameterStore.GoodEntry entry ∧
      ctx = {template with registry := ctx.registry,helper := entry.initialized.parameters} := by
  have borrowed := (assemble_spec entries helperHandle references template ctx assembled).2
  exact AllocatedHelperContext.borrow_spec entries reachable helperHandle _ ctx borrowed

theorem source_entry {B : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (helperHandle : ℕ) (references : Vector Reference) (template ctx : Context B)
    (assembled : assemble entries helperHandle references template = some ctx) (slot : Fin ctx.registry.val.length) :
    ∃ (reference : Reference) (entry : Entry), references.val[slot.val]? = some reference ∧
      entries[reference.handle]? = some entry ∧ NativeGoldParameterStore.GoodEntry entry ∧
      ctx.registry.val.get slot = ⟨entry.initialized.parameters,reference.root⟩ :=
  NativeGoldParameterStore.registry_slot entries reachable references ctx.registry
    (assemble_spec entries helperHandle references template ctx assembled).1 slot

theorem missing_helper {B : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference) (template : Context B)
    (missing : entries[helperHandle]? = none) : assemble entries helperHandle references template = none := by
  unfold assemble
  cases collected : NativeGoldParameterStore.registry entries references with
  | none => rfl
  | some registry => exact AllocatedHelperContext.missing entries helperHandle _ missing

theorem missing_registry {B : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference) (template : Context B)
    (missing : NativeGoldParameterStore.registry entries references = none) : assemble entries helperHandle references template = none := by
  simp only [assemble,missing,Option.bind_none]

end FormalProof4FHE.HasteBoots.AllocatedLookupContext
