module
public import FormalProof4FHE.HasteBoots.LookupExecutionOrigin
public import FormalProof4FHE.HasteBoots.NativeSharedSourceClaims
@[expose] public section

/-! Typed original request-slot addresses preserve order and aliases. Native
preflight supplies their domains, and every selected address is actually used
by source verification. No equality search over response records selects it. -/
namespace FormalProof4FHE.HasteBoots.LookupOriginalSlots
open NativeSharedLookupStatement (Request)
open NativeFieldRepresentation (GoldWord)
noncomputable section

structure Slots (registryCount : ℕ) (request : Request) where
  slot : Fin request.columns → Fin registryCount
  ordered : List.ofFn (fun i => (slot i).val) = request.terminal.sourceSlots

theorem recover (registry : List NativeLookupBindGeometry.Parameters) (helper : NativeLookupBindGeometry.Parameters)
    (requests : List Request) (geometry : NativeSharedLookupPreflight.Output)
    (preflight : NativeSharedLookupPreflight.preflight registry helper requests = some geometry)
    (request : Request) (member : request ∈ requests) : Nonempty (Slots registry.length request) := by
  have dimensions := (NativeSharedLookupPreflight.preflight_spec registry helper requests geometry preflight).dimensions.2.2 request member
  have bound (i : Fin request.columns) : i.val < request.terminal.sourceSlots.length := by rw [dimensions.1]; exact i.isLt
  let slot : Fin request.columns → Fin registry.length := fun i =>
    ⟨request.terminal.sourceSlots[i.val]'(bound i),dimensions.2 _ (List.getElem_mem (bound i))⟩
  refine ⟨⟨slot,?_⟩⟩
  apply List.ext_getElem (by rw [List.length_ofFn,dimensions.1])
  intro i leftPresent rightPresent
  simp only [List.getElem_ofFn,slot]

/-- Typed vectors still refer to the actual original registry opening at
that exact slot, even when several columns address the same slot. -/
theorem Slots.opening {registryCount : ℕ} {request : Request} (slots : Slots registryCount request)
    (values copies : List (List GoldWord)) {width : ℕ} (inputs : Fin request.columns → Fin width → GoldWord)
    (rebuilt : List.ofFn (fun i => List.ofFn (inputs i)) = copies)
    (related : List.Forall₂ (fun slot value => values[slot]? = some value) request.terminal.sourceSlots copies)
    (column : Fin request.columns) : values[(slots.slot column).val]? = some (List.ofFn (inputs column)) := by
  have aligned : List.Forall₂ (fun slot value => values[slot]? = some value)
      (List.ofFn (fun i => (slots.slot i).val)) (List.ofFn (fun i => List.ofFn (inputs i))) := by
    rw [slots.ordered,rebuilt]
    exact related
  have result := aligned.get (by simpa only [List.length_ofFn] using column.isLt) (by simpa only [List.length_ofFn] using column.isLt)
  simpa only [List.get_eq_getElem,List.getElem_ofFn] using result

theorem Slots.used {registryCount : ℕ} {request : Request} (slots : Slots registryCount request)
    (requests : NativePrefixCodec.Vector NativeLookupRequestWire.Request)
    (member : request ∈ List.ofFn (NativeSharedLookupParent.models requests)) (column : Fin request.columns) :
    NativeSharedSourceClaims.used requests (slots.slot column) = true := by
  rw [NativeSharedLookupParent.models_list] at member
  obtain ⟨original,originalMember,same⟩ := List.mem_map.mp member
  have selected : (slots.slot column).val ∈ request.terminal.sourceSlots := by
    rw [← slots.ordered]
    exact List.mem_ofFn.mpr ⟨column,rfl⟩
  have selectedOriginal : (slots.slot column).val ∈ original.toModel.terminal.sourceSlots := by simpa only [same] using selected
  change (slots.slot column).val ∈ original.sourceSlots.val.map Fin.val at selectedOriginal
  obtain ⟨source,sourceMember,sameSlot⟩ := List.mem_map.mp selectedOriginal
  exact (NativeSharedSourceClaims.used_iff requests (slots.slot column)).mpr ⟨original,originalMember,source,sourceMember,sameSlot⟩

end
end FormalProof4FHE.HasteBoots.LookupOriginalSlots
