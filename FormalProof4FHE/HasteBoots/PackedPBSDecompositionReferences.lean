module
public import FormalProof4FHE.HasteBoots.PackedPBSOriginalReferences
public import FormalProof4FHE.HasteBoots.PBSHadamardBlindRotation
public import FormalProof4FHE.HasteBoots.OwnedDecompositionSoundness
@[expose] public section

/-! Reconstruction borrows the original input and coefficient objects.
Registry order is input, native half-major digits, then original borrows. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSDecompositionReferences
open NativeRootMessage (Digest)
open NativeGoldParameterStore (Reference)
noncomputable section
variable {d : ℕ}

structure Inputs where
  handle : ℕ
  roots : Bool → Digest

def digitSlot (half : Bool) (level : Fin d) : Fin (2*d+1) :=
  Fin.castSucc (PBSHadamardBlindRotation.digitIndex (half,level))

def inputReference (inputs : Inputs) (half : Bool) : Reference := ⟨inputs.handle,inputs.roots half⟩

def digitReference (family : PackedPBSOriginalReferences.Family (2*d)) (half : Bool) (level : Fin d) : Reference :=
  ⟨family.coefficientHandle,family.coefficients (digitSlot half level)⟩

def reference (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : Inputs)
    (half : Bool) (borrows : Fin (d+1) → Reference) (factor : Fin (2*d+2)) : Reference :=
  if zero : factor.val = 0 then inputReference inputs half
  else if small : factor.val ≤ d then digitReference family half ⟨factor.val-1,by omega⟩
  else borrows ⟨factor.val-(d+1),by have := factor.isLt; omega⟩

def linear (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : Inputs)
    (half : Bool) (borrows : Fin (d+1) → Reference) : List Reference :=
  List.ofFn (reference family inputs half borrows)

theorem reference_input (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : Inputs)
    (half : Bool) (borrows : Fin (d+1) → Reference) :
    reference family inputs half borrows DecompositionLinear.input = inputReference inputs half := by
  simp [reference,DecompositionLinear.input]

theorem reference_digit (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : Inputs)
    (half : Bool) (borrows : Fin (d+1) → Reference) (level : Fin d) :
    reference family inputs half borrows (DecompositionLinear.digit level) = digitReference family half level := by
  have small : level.val+1 ≤ d := by have := level.isLt; omega
  simp [reference,DecompositionLinear.digit,small]

theorem reference_borrow (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : Inputs)
    (half : Bool) (borrows : Fin (d+1) → Reference) (level : Fin (d+1)) :
    reference family inputs half borrows (DecompositionLinear.borrow level) = borrows level := by
  have large : ¬d+1+level.val ≤ d := by omega
  simp [reference,DecompositionLinear.borrow,large]

theorem linear_digit (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : Inputs)
    (half : Bool) (borrows : Fin (d+1) → Reference) (level : Fin d) :
    (linear family inputs half borrows)[(DecompositionLinear.digit level).val]? =
      some (digitReference family half level) := by
  simp only [linear,List.getElem?_ofFn]
  rw [dite_eq_left (DecompositionLinear.digit level).isLt]
  exact congrArg some (reference_digit family inputs half borrows level)

/-- Both slots borrow the identical original object/root, including parameter identity. -/
theorem ntt_digit (family : PackedPBSOriginalReferences.Family (2*d)) (half : Bool) (level : Fin d) :
    (PackedPBSOriginalReferences.ntt family (digitSlot half level))[0]? = some (digitReference family half level) := rfl

/-- Successful collectors expose the same retained native parameter object,
rather than independently rebuilding an equal-looking code geometry. -/
theorem collected_digit_alias (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : Inputs)
    (half : Bool) (borrows : Fin (d+1) → Reference) (level : Fin d)
    (entries : List NativeGoldParameterStore.Entry)
    (nttRegistry linearRegistry : List (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (nttCollected : NativeGoldParameterStore.collect entries (PackedPBSOriginalReferences.ntt family (digitSlot half level)) = some nttRegistry)
    (linearCollected : NativeGoldParameterStore.collect entries (linear family inputs half borrows) = some linearRegistry) :
    ∃ original, entries[family.coefficientHandle]? = some original ∧
      nttRegistry[0]? = some ⟨original.initialized.parameters,family.coefficients (digitSlot half level)⟩ ∧
      linearRegistry[(DecompositionLinear.digit level).val]? =
        some ⟨original.initialized.parameters,family.coefficients (digitSlot half level)⟩ := by
  exact PackedPBSOriginalReferences.collected_alias entries
    (PackedPBSOriginalReferences.ntt family (digitSlot half level)) (linear family inputs half borrows)
    nttRegistry linearRegistry nttCollected linearCollected 0 (DecompositionLinear.digit level).val
    (by simp [PackedPBSOriginalReferences.ntt]) (by simpa only [linear,List.length_ofFn] using (DecompositionLinear.digit level).isLt)
    (digitReference family half level) (ntt_digit family half level) (linear_digit family inputs half borrows level)

end
end FormalProof4FHE.HasteBoots.PackedPBSDecompositionReferences
