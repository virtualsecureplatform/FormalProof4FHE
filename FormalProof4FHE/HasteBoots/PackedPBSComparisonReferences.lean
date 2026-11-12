module
public import FormalProof4FHE.HasteBoots.PackedPBSDecompositionReferences
@[expose] public section

/-! Comparisons borrow the reconstruction digits and borrows in order.
Only the input column is omitted; source parameter objects and roots persist. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSComparisonReferences
open NativeGoldParameterStore (Reference)
open PackedPBSDecompositionReferences (Inputs)
noncomputable section
variable {d : ℕ}

def linearSlot (source : Fin (2*d+1)) : Fin (2*d+2) := source.succ

def digitSlot (level : Fin d) : Fin (2*d+1) := ⟨level.val,by have := level.isLt; omega⟩

def borrowSlot (level : Fin (d+1)) : Fin (2*d+1) := ⟨d+level.val,by have := level.isLt; omega⟩

theorem linear_digit (level : Fin d) : linearSlot (digitSlot level) = DecompositionLinear.digit level := by
  apply Fin.ext
  rfl

theorem linear_borrow (level : Fin (d+1)) : linearSlot (borrowSlot level) = DecompositionLinear.borrow level := by
  apply Fin.ext
  simp only [linearSlot,borrowSlot,DecompositionLinear.borrow,Fin.val_succ]
  omega

def sources (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : Inputs)
    (half : Bool) (borrows : Fin (d+1) → Reference) : List Reference :=
  List.ofFn (fun source => PackedPBSDecompositionReferences.reference family inputs half borrows (linearSlot source))

theorem source_slot (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : Inputs)
    (half : Bool) (borrows : Fin (d+1) → Reference) (source : Fin (2*d+1)) :
    (sources family inputs half borrows)[source.val]? =
      some (PackedPBSDecompositionReferences.reference family inputs half borrows (linearSlot source)) := by
  simp only [sources,List.getElem?_ofFn]
  rw [dite_eq_left source.isLt]

theorem source_digit (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : Inputs)
    (half : Bool) (borrows : Fin (d+1) → Reference) (level : Fin d) :
    (sources family inputs half borrows)[(digitSlot level).val]? =
      some (PackedPBSDecompositionReferences.digitReference family half level) := by
  rw [source_slot,linear_digit,PackedPBSDecompositionReferences.reference_digit]

theorem source_borrow (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : Inputs)
    (half : Bool) (borrows : Fin (d+1) → Reference) (level : Fin (d+1)) :
    (sources family inputs half borrows)[(borrowSlot level).val]? = some (borrows level) := by
  rw [source_slot,linear_borrow,PackedPBSDecompositionReferences.reference_borrow]

theorem reconstruction_slot (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : Inputs)
    (half : Bool) (borrows : Fin (d+1) → Reference) (source : Fin (2*d+1)) :
    (PackedPBSDecompositionReferences.linear family inputs half borrows)[(linearSlot source).val]? =
      some (PackedPBSDecompositionReferences.reference family inputs half borrows (linearSlot source)) := by
  simp only [PackedPBSDecompositionReferences.linear,List.getElem?_ofFn]
  rw [dite_eq_left (linearSlot source).isLt]

/-- Every original comparison source borrows the SAME retained object/root
as its reconstruction column, including original borrow columns and aliases. -/
theorem collected_source_alias (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : Inputs)
    (half : Bool) (borrows : Fin (d+1) → Reference) (source : Fin (2*d+1))
    (entries : List NativeGoldParameterStore.Entry)
    (linearRegistry comparisonRegistry : List (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (linearCollected : NativeGoldParameterStore.collect entries (PackedPBSDecompositionReferences.linear family inputs half borrows) = some linearRegistry)
    (comparisonCollected : NativeGoldParameterStore.collect entries (sources family inputs half borrows) = some comparisonRegistry) :
    let originalReference := PackedPBSDecompositionReferences.reference family inputs half borrows (linearSlot source)
    ∃ original, entries[originalReference.handle]? = some original ∧
      linearRegistry[(linearSlot source).val]? = some ⟨original.initialized.parameters,originalReference.root⟩ ∧
      comparisonRegistry[source.val]? = some ⟨original.initialized.parameters,originalReference.root⟩ := by
  exact PackedPBSOriginalReferences.collected_alias entries
    (PackedPBSDecompositionReferences.linear family inputs half borrows) (sources family inputs half borrows)
    linearRegistry comparisonRegistry linearCollected comparisonCollected (linearSlot source).val source.val
    (by simpa only [PackedPBSDecompositionReferences.linear,List.length_ofFn] using (linearSlot source).isLt)
    (by simpa only [sources,List.length_ofFn] using source.isLt)
    (PackedPBSDecompositionReferences.reference family inputs half borrows (linearSlot source))
    (reconstruction_slot family inputs half borrows source) (source_slot family inputs half borrows source)

end
end FormalProof4FHE.HasteBoots.PackedPBSComparisonReferences
