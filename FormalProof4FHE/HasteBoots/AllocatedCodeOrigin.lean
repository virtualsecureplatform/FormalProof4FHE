module
public import FormalProof4FHE.HasteBoots.CacheBackedCodeOrigin
public import FormalProof4FHE.HasteBoots.NativeGoldParameterStore
@[expose] public section

/-! Successful native initialization and reachable immutable parameter-store
collection derive completed backend provenance for original borrowed objects.
References, aliases and unused registry positions are retained unchanged.
Logical handles are not a physical pointer/heap refinement. -/
namespace FormalProof4FHE.HasteBoots.AllocatedCodeOrigin
open CacheBackedCodeOrigin (Origin)
open NativeGoldBatchPcsProgram (Context)
open NativeGoldBlockCodeProgram (Request Config)
open NativeGoldEncodedParameters (Header Initialized)
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeSharedLookupParent (Oracle)
noncomputable section

/-- The selected result is from the actual successful initializer. Its code
identity is derived; no separately supplied retained-code proof is required. -/
def ofInitialization (header : Header) (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config) (initialized : Initialized)
    (executed : NativeGoldParameterInitialization.finish header config = some (.ok initialized))
    (ctx : Context) (same : ctx.parameters = initialized.parameters) : Origin ctx :=
  let produced := NativeGoldParameterInitialization.code_origin header request config reachable initialized executed
  { request := request
    config := config
    reachable := reachable
    result := Classical.choose produced
    finished := (Classical.choose_spec produced).1
    retained := (Classical.choose_spec produced).2.1.symm.trans (congrArg (fun parameters => parameters.code) same.symm) }

theorem initialization_data (header : Header) (request : Request) (config : Config)
    (reachable : NativeGoldBlockCodeProgram.Reachable request config) (initialized : Initialized)
    (executed : NativeGoldParameterInitialization.finish header config = some (.ok initialized))
    (ctx : Context) (same : ctx.parameters = initialized.parameters) :
    (ofInitialization header request config reachable initialized executed ctx same).request = request ∧
      (ofInitialization header request config reachable initialized executed ctx same).config = config := ⟨rfl,rfl⟩

/-- Select the entry witnessed by the actual registry-slot lookup. -/
def registryEntry (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry)
    (index : Fin registry.val.length) : Entry :=
  Classical.choose (Classical.choose_spec (NativeGoldParameterStore.registry_slot entries reachable references registry collected index))

theorem registry_entry_spec (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry)
    (index : Fin registry.val.length) :
    ∃ reference, references.val[index.val]? = some reference ∧
      entries[reference.handle]? = some (registryEntry entries reachable references registry collected index) ∧
      NativeGoldParameterStore.GoodEntry (registryEntry entries reachable references registry collected index) ∧
      registry.val.get index = ⟨(registryEntry entries reachable references registry collected index).initialized.parameters,reference.root⟩ := by
  let selected := NativeGoldParameterStore.registry_slot entries reachable references registry collected index
  exact ⟨Classical.choose selected,Classical.choose_spec (Classical.choose_spec selected)⟩

/-- Provenance retains the selected original initializer, rather than choosing
an arbitrary constructor that happens to produce the same code. -/
def ofRegistry (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry)
    (index : Fin registry.val.length) (ctx : Context) (same : ctx.parameters = (registry.val.get index).parameters) : Origin ctx :=
  let entry := registryEntry entries reachable references registry collected index
  let facts := Classical.choose_spec (registry_entry_spec entries reachable references registry collected index)
  ofInitialization entry.header entry.request entry.config facts.2.2.1.1 entry.initialized facts.2.2.1.2 ctx
    (same.trans (congrArg (fun source => source.parameters) facts.2.2.2))

theorem registry_data (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (references : Vector Reference) (registry : Vector (Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry)
    (index : Fin registry.val.length) (ctx : Context) (same : ctx.parameters = (registry.val.get index).parameters) :
    (ofRegistry entries reachable references registry collected index ctx same).request =
        (registryEntry entries reachable references registry collected index).request ∧
    (ofRegistry entries reachable references registry collected index ctx same).config =
        (registryEntry entries reachable references registry collected index).config := ⟨rfl,rfl⟩

end
end FormalProof4FHE.HasteBoots.AllocatedCodeOrigin
