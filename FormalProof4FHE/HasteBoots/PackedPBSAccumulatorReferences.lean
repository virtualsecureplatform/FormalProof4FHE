module
public import FormalProof4FHE.HasteBoots.PackedPBSDecompositionReferences
@[expose] public section

/-! The accumulator reuses four original accumulator objects, the Hadamard
result coefficient and both original decomposition input objects, in native order. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSAccumulatorReferences
open NativeRootMessage (Digest)
open NativeGoldParameterStore (Reference)
noncomputable section
variable {d : ℕ}

def inputSlot (half : Bool) : Fin 7 := if half then 6 else 5

def reference (family : PackedPBSOriginalReferences.Family (2*d))
    (inputs : PackedPBSDecompositionReferences.Inputs) (accumulators : Fin 4 → Reference) : Fin 7 → Reference :=
  ![accumulators 0,accumulators 1,accumulators 2,accumulators 3,
    ⟨family.coefficientHandle,family.coefficients (Fin.last (2*d))⟩,
    PackedPBSDecompositionReferences.inputReference inputs false,
    PackedPBSDecompositionReferences.inputReference inputs true]

def registry (family : PackedPBSOriginalReferences.Family (2*d))
    (inputs : PackedPBSDecompositionReferences.Inputs) (accumulators : Fin 4 → Reference) : List Reference :=
  List.ofFn (reference family inputs accumulators)

def roots (family : PackedPBSOriginalReferences.Family (2*d))
    (inputs : PackedPBSDecompositionReferences.Inputs) (accumulators : Fin 4 → Reference) : Fin 7 → Digest :=
  fun factor => (reference family inputs accumulators factor).root

theorem accumulator_reference (family : PackedPBSOriginalReferences.Family (2*d))
    (inputs : PackedPBSDecompositionReferences.Inputs) (accumulators : Fin 4 → Reference) (index : Fin 4) :
    reference family inputs accumulators (Fin.castLE (by decide +kernel : 4 ≤ 7) index) = accumulators index := by
  fin_cases index <;> rfl

theorem sum_reference (family : PackedPBSOriginalReferences.Family (2*d))
    (inputs : PackedPBSDecompositionReferences.Inputs) (accumulators : Fin 4 → Reference) :
    reference family inputs accumulators 4 = ⟨family.coefficientHandle,family.coefficients (Fin.last (2*d))⟩ := rfl

theorem input_reference (family : PackedPBSOriginalReferences.Family (2*d))
    (inputs : PackedPBSDecompositionReferences.Inputs) (accumulators : Fin 4 → Reference) (half : Bool) :
    reference family inputs accumulators (inputSlot half) = PackedPBSDecompositionReferences.inputReference inputs half := by
  cases half <;> rfl

theorem registry_slot (family : PackedPBSOriginalReferences.Family (2*d))
    (inputs : PackedPBSDecompositionReferences.Inputs) (accumulators : Fin 4 → Reference) (factor : Fin 7) :
    (registry family inputs accumulators)[factor.val]? = some (reference family inputs accumulators factor) := by
  simp only [registry,List.getElem?_ofFn]
  rw [dite_eq_left factor.isLt]

/-- The sum-product is the exact retained coefficient object from its NTT,
including its parameter allocation identity, rather than a rebuilt geometry. -/
theorem collected_sum_alias (family : PackedPBSOriginalReferences.Family (2*d))
    (inputs : PackedPBSDecompositionReferences.Inputs) (accumulators : Fin 4 → Reference)
    (entries : List NativeGoldParameterStore.Entry)
    (nttRegistry accumulatorRegistry : List (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (nttCollected : NativeGoldParameterStore.collect entries (PackedPBSOriginalReferences.ntt family (Fin.last (2*d))) = some nttRegistry)
    (accumulatorCollected : NativeGoldParameterStore.collect entries (registry family inputs accumulators) = some accumulatorRegistry) :
    ∃ original, entries[family.coefficientHandle]? = some original ∧
      nttRegistry[0]? = some ⟨original.initialized.parameters,family.coefficients (Fin.last (2*d))⟩ ∧
      accumulatorRegistry[4]? = some ⟨original.initialized.parameters,family.coefficients (Fin.last (2*d))⟩ :=
  PackedPBSOriginalReferences.collected_alias entries (PackedPBSOriginalReferences.ntt family (Fin.last (2*d)))
    (registry family inputs accumulators) nttRegistry accumulatorRegistry nttCollected accumulatorCollected 0 4
    (by simp [PackedPBSOriginalReferences.ntt]) (by simp [registry])
    ⟨family.coefficientHandle,family.coefficients (Fin.last (2*d))⟩ rfl (registry_slot family inputs accumulators 4)

/-- Each duplicated-half source is the same original input object used by
that half's reconstruction, with its actual retained parameter object. -/
theorem collected_input_alias (family : PackedPBSOriginalReferences.Family (2*d))
    (inputs : PackedPBSDecompositionReferences.Inputs) (accumulators : Fin 4 → Reference)
    (half : Bool) (borrows : Fin (d+1) → Reference) (entries : List NativeGoldParameterStore.Entry)
    (linearRegistry accumulatorRegistry : List (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (linearCollected : NativeGoldParameterStore.collect entries (PackedPBSDecompositionReferences.linear family inputs half borrows) = some linearRegistry)
    (accumulatorCollected : NativeGoldParameterStore.collect entries (registry family inputs accumulators) = some accumulatorRegistry) :
    ∃ original, entries[inputs.handle]? = some original ∧
      linearRegistry[0]? = some ⟨original.initialized.parameters,inputs.roots half⟩ ∧
      accumulatorRegistry[(inputSlot half).val]? = some ⟨original.initialized.parameters,inputs.roots half⟩ := by
  have selected := registry_slot family inputs accumulators (inputSlot half)
  rw [input_reference] at selected
  exact PackedPBSOriginalReferences.collected_alias entries
    (PackedPBSDecompositionReferences.linear family inputs half borrows) (registry family inputs accumulators)
    linearRegistry accumulatorRegistry linearCollected accumulatorCollected 0 (inputSlot half).val
    (by simp [PackedPBSDecompositionReferences.linear]) (by simpa only [registry,List.length_ofFn] using (inputSlot half).isLt)
    (PackedPBSDecompositionReferences.inputReference inputs half)
    (by simpa only [PackedPBSDecompositionReferences.linear,DecompositionLinear.input,List.getElem?_ofFn,dite_eq_left (show 0 < 2*d+2 by omega)] using
      congrArg some (PackedPBSDecompositionReferences.reference_input family inputs half borrows)) selected

end
end FormalProof4FHE.HasteBoots.PackedPBSAccumulatorReferences
