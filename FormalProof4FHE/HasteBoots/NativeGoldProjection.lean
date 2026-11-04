module

public import FormalProof4FHE.HasteBoots.NativeGoldHelper
public import FormalProof4FHE.HasteBoots.PaddedExtension

@[expose] public section

/-!
# Checked raw Goldilocks extension projection

These are the native `packed_extension::vector`/`element` dimension, length
and padding checks. Projection copies the first three stored words exactly;
unused lanes compare by native field-zero equality, including lazy zero.
No query or PCS authentication certificate is supplied by this interface.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldProjection

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)

def dimensions (width : ℕ) : Bool := decide (3 ≤ width) && decide (width * width < 2 ^ 64)

def decode (values : List GoldWord) (enough : 3 ≤ values.length) : Word :=
  fun i => values[i.val]'(by have bound := i.isLt; omega)

def Padding (values : List GoldWord) : Prop := ∀ value ∈ values.drop 3, goldCanonical value = 0

def paddingCheck (values : List GoldWord) : Bool :=
  (values.drop 3).all (fun value => decide (goldCanonical value = 0))

theorem paddingCheck_iff (values : List GoldWord) : paddingCheck values = true ↔ Padding values := by
  simp only [paddingCheck, List.all_eq_true, decide_eq_true_eq, Padding]

instance (values : List GoldWord) : Decidable (Padding values) :=
  decidable_of_iff (paddingCheck values = true) (paddingCheck_iff values)

def element (width : ℕ) (values : List GoldWord) : Option Word :=
  if shape : dimensions width = true then
    if length : values.length = width then
      if paddingCheck values then
        some (decode values (by
          have lower := (Bool.and_eq_true_iff.mp shape).1
          have enough : 3 ≤ width := of_decide_eq_true lower
          omega))
      else none
    else none
  else none

def vector (width : ℕ) (value : Word) : Option (List GoldWord) :=
  if dimensions width then some (NativeGoldHelper.vector width value) else none

theorem dimensions_iff (width : ℕ) : dimensions width = true ↔ 3 ≤ width ∧ width * width < 2 ^ 64 := by
  simp only [dimensions, Bool.and_eq_true, decide_eq_true_eq]

theorem element_success (width : ℕ) (values : List GoldWord) (shape : dimensions width = true)
    (length : values.length = width) (padded : Padding values) :
    element width values = some (decode values (by have lower := (dimensions_iff width).mp shape; omega)) := by
  simp only [element, dite_eq_left shape, dite_eq_left length, ite_eq_left ((paddingCheck_iff _).mpr padded)]

/-- Success retains all original coordinates and checks every unused lane. -/
theorem element_some_iff (width : ℕ) (values : List GoldWord) (value : Word) :
    element width values = some value ↔ dimensions width = true ∧ values.length = width ∧
      Padding values ∧ ∀ i : Fin 3, values[i.val]? = some (value i) := by
  constructor
  · intro success
    by_cases shape : dimensions width = true
    · by_cases length : values.length = width
      · by_cases padded : Padding values
        · have enough : 3 ≤ values.length := by have lower := (dimensions_iff width).mp shape; omega
          have same : decode values enough = value := Option.some.inj
            ((element_success width values shape length padded).symm.trans success)
          refine ⟨shape, length, padded, ?_⟩
          intro i
          rw [List.getElem?_eq_getElem (by have bound := i.isLt; omega), ← same]
          rfl
        · simp only [element, dite_eq_left shape, dite_eq_left length, ite_eq_right ((paddingCheck_iff _).not.mpr padded)] at success
          contradiction
      · simp only [element, dite_eq_left shape, dite_eq_right length] at success
        contradiction
    · simp only [element, dite_eq_right shape] at success
      contradiction
  · rintro ⟨shape, length, padded, coordinates⟩
    have enough : 3 ≤ values.length := by have lower := (dimensions_iff width).mp shape; omega
    have same : decode values enough = value := by
      funext i
      have got := List.getElem?_eq_getElem (by have bound := i.isLt; omega : i.val < values.length)
      exact Option.some.inj (got.symm.trans (coordinates i))
    rw [element_success width values shape length padded, same]

theorem zero_iff (value : GoldWord) : goldCanonical value = 0 ↔ goldValue value = 0 := by
  have zeroField : goldValue (0 : GoldWord) = 0 := by simp only [goldValue, Fin.val_zero, Nat.cast_zero]
  have zeroRaw : goldCanonical (0 : GoldWord) = 0 := by decide
  simpa only [zeroField, zeroRaw] using (goldValue_eq_iff value (0 : GoldWord)).symm

noncomputable section

theorem padding_ofFn {padding : ℕ} (values : Fin (3 + padding) → GoldWord) :
    Padding (List.ofFn values) ↔ PaddedExtension.Padded (fun lane => goldValue (values lane)) := by
  have tail : (List.ofFn values).drop 3 = List.ofFn (fun i : Fin padding => values (Fin.natAdd 3 i)) := by
    rw [List.ofFn_add]
    simp only [List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
  rw [Padding, tail]
  change (∀ value ∈ List.ofFn (fun i : Fin padding => values (Fin.natAdd 3 i)), goldCanonical value = 0) ↔
    ∀ i : Fin padding, goldValue (values (Fin.natAdd 3 i)) = 0
  constructor
  · intro valid i
    exact (zero_iff _).mp (valid _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  · intro valid value member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact (zero_iff _).mpr (valid i)

theorem decode_value {padding : ℕ} (values : Fin (3 + padding) → GoldWord) :
    goldExtensionValue (decode (List.ofFn values) (by simp)) =
      PaddedExtension.decode goldilocksBasis (fun lane => goldValue (values lane)) := by
  apply goldilocksBasis.equivFun.injective
  ext i
  simp only [goldExtension_coordinate]
  change goldValue (decode (List.ofFn values) _ i) =
    goldilocksBasis.equivFun (goldilocksBasis.equivFun.symm
      (fun j => goldValue (values (j.castAdd padding)))) i
  rw [LinearEquiv.apply_symm_apply]
  simp only [decode, List.getElem_ofFn]
  rfl

/-- Native checked projection agrees with the existing field decoder,
including failed padding, without normalizing the meaningful stored words. -/
theorem element_value {padding : ℕ} (values : Fin (3 + padding) → GoldWord)
    (fits : (3 + padding) * (3 + padding) < 2 ^ 64) :
    (element (3 + padding) (List.ofFn values)).map goldExtensionValue =
      PaddedExtension.element goldilocksBasis (fun lane => goldValue (values lane)) := by
  have shape : dimensions (3 + padding) = true := (dimensions_iff _).mpr ⟨by omega, fits⟩
  by_cases padded : Padding (List.ofFn values)
  · rw [element_success _ _ shape List.length_ofFn padded, Option.map_some,
      PaddedExtension.element, ite_eq_left ((padding_ofFn values).mp padded), decode_value]
  · have failed : ¬PaddedExtension.Padded (fun lane => goldValue (values lane)) :=
      fun accepted => padded ((padding_ofFn values).mpr accepted)
    rw [element, dite_eq_left shape, dite_eq_left List.length_ofFn, ite_eq_right ((paddingCheck_iff _).not.mpr padded),
      Option.map_none, PaddedExtension.element, ite_eq_right failed]

/-- Packing and re-projecting preserves the exact original raw word. -/
theorem element_vector (width : ℕ) (value : Word) (shape : dimensions width = true) :
    element width (NativeGoldHelper.vector width value) = some value := by
  apply (element_some_iff _ _ _).mpr
  refine ⟨shape, NativeGoldHelper.vector_length width value, ?_, ?_⟩
  · intro entry member
    obtain ⟨index, bound, equal⟩ := List.mem_iff_getElem.mp member
    rw [List.getElem_drop] at equal
    simp only [NativeGoldHelper.vector, List.getElem_ofFn] at equal
    have outside : ¬3 + index < 3 := by omega
    simp only [NativeGoldHelper.coefficient, dite_eq_right outside] at equal
    rw [← equal]
    decide
  · intro i
    have enough := (dimensions_iff width).mp shape |>.1
    rw [List.getElem?_eq_getElem (by rw [NativeGoldHelper.vector_length]; exact i.isLt.trans_le enough)]
    simp only [NativeGoldHelper.vector, List.getElem_ofFn, NativeGoldHelper.coefficient, dite_eq_left i.isLt]

theorem vector_element (width : ℕ) (value : Word) (shape : dimensions width = true) :
    (vector width value).bind (element width) = some value := by
  rw [vector, ite_eq_left shape, Option.bind_some, element_vector width value shape]

theorem vector_value {padding : ℕ} (value : Word) (fits : (3 + padding) * (3 + padding) < 2 ^ 64) :
    (vector (3 + padding) value).map (List.map goldValue) =
      some (List.ofFn (PaddedExtension.encode (padding := padding) goldilocksBasis (goldExtensionValue value))) := by
  have shape : dimensions (3 + padding) = true := (dimensions_iff _).mpr ⟨by omega, fits⟩
  rw [vector, ite_eq_left shape, Option.map_some, NativeGoldHelper.vector_value]
  rw [NativeHelperPacking.vector, NativeHelperPacking.coefficients_padded]

end

end FormalProof4FHE.HasteBoots.NativeGoldProjection
