module
public import FormalProof4FHE.HasteBoots.ConstructedGoldSourceDescriptor
@[expose] public section

/-! Resolve canonical source descriptors from actual immutable parameter-store
references. Roots remain separate: sharing parameters does not equate the values
of distinct source roots. No decoded source or independent geometry is supplied. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldSourceBorrowing
open NativeGoldParameterStore (Entry Reference GoodEntry Reachable)
open NativeFields (Goldilocks)
open ConstructedGoldSourceDescriptor (Configuration heights source)
noncomputable section

/-- This analysis adapter accepts square original-source layouts only. Failure
is explicit for an unavailable handle or unequal test/code-symbol widths. -/
def resolve (entries : List Entry) (reachable : Reachable entries) (reference : Reference) (b radius : ℕ) :
    Option (RecordedPaddedSource.Parameters Goldilocks Configuration heights b) :=
  match found : entries[reference.handle]? with
  | none => none
  | some entry =>
    if width : entry.initialized.parameters.width.val = b then
      if block : entry.initialized.parameters.code.blockWidth.val = b then
        some (source entry (NativeGoldParameterStore.reachable_good entries reachable entry (List.mem_of_getElem? found)) width block radius)
      else none
    else none

/-- Successful lookup and the two public width fields determine the result. -/
theorem resolve_of_lookup (entries : List Entry) (reachable : Reachable entries) (reference : Reference)
    (entry : Entry) (selected : entries[reference.handle]? = some entry) (good : GoodEntry entry)
    (b radius : ℕ) (width : entry.initialized.parameters.width.val = b)
    (block : entry.initialized.parameters.code.blockWidth.val = b) :
    resolve entries reachable reference b radius = some (source entry good width block radius) := by
  unfold resolve
  split
  · rename_i missing
    rw [selected] at missing
    cases missing
  · rename_i actual found
    have same : actual = entry := Option.some.inj (found.symm.trans selected)
    subst actual
    simp only [dite_eq_left width,dite_eq_left block]

/-- Every successful descriptor comes from the referenced actual good entry,
with its constructor-derived domain and capacity at the fixed supplied radius. -/
theorem resolve_provenance (entries : List Entry) (reachable : Reachable entries) (reference : Reference)
    (b radius : ℕ) (descriptor : RecordedPaddedSource.Parameters Goldilocks Configuration heights b)
    (executed : resolve entries reachable reference b radius = some descriptor) :
    ∃ entry, entries[reference.handle]? = some entry ∧
      ∃ good : GoodEntry entry, ∃ width : entry.initialized.parameters.width.val = b,
        ∃ block : entry.initialized.parameters.code.blockWidth.val = b,
          descriptor = source entry good width block radius := by
  unfold resolve at executed
  split at executed
  · cases executed
  · rename_i entry selected
    split at executed
    · rename_i width
      split at executed
      · rename_i block
        exact ⟨entry,selected,NativeGoldParameterStore.reachable_good entries reachable entry (List.mem_of_getElem? selected),
          width,block,(Option.some.inj executed).symm⟩
      · cases executed
    · cases executed

/-- Borrowed coefficient/evaluation/key/input/borrow references reuse one
parameter descriptor when their handles agree, even for different roots. -/
theorem resolve_same_handle (entries : List Entry) (reachable : Reachable entries)
    (left right : Reference) (same : left.handle = right.handle) (b radius : ℕ) :
    resolve entries reachable left b radius = resolve entries reachable right b radius := by
  cases left with
  | mk leftHandle leftRoot =>
    cases right with
    | mk rightHandle rightRoot =>
      change leftHandle = rightHandle at same
      cases same
      rfl

/-- The native collected registry resolves to descriptors tagged by the exact
stored public parameter objects and retains each reference's original root. -/
theorem registry_resolves (entries : List Entry) (reachable : Reachable entries)
    (references : NativePrefixCodec.Vector Reference)
    (registry : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (collected : NativeGoldParameterStore.registry entries references = some registry)
    (index : Fin registry.val.length) (b radius : ℕ)
    (width : (registry.val.get index).parameters.width.val = b)
    (block : (registry.val.get index).parameters.code.blockWidth.val = b) :
    ∃ reference descriptor,
      references.val[index.val]? = some reference ∧
      resolve entries reachable reference b radius = some descriptor ∧
      descriptor.tag = (registry.val.get index).parameters ∧
      reference.root = (registry.val.get index).root := by
  obtain ⟨reference,entry,atReference,atEntry,good,same⟩ :=
    NativeGoldParameterStore.registry_slot entries reachable references registry collected index
  have actualWidth : entry.initialized.parameters.width.val = b := by simpa only [same] using width
  have actualBlock : entry.initialized.parameters.code.blockWidth.val = b := by simpa only [same] using block
  refine ⟨reference,source entry good actualWidth actualBlock radius,atReference,
    resolve_of_lookup entries reachable reference entry atEntry good b radius actualWidth actualBlock,?_,?_⟩
  · rw [same]
    rfl
  · rw [same]

end
end FormalProof4FHE.HasteBoots.ConstructedGoldSourceBorrowing
