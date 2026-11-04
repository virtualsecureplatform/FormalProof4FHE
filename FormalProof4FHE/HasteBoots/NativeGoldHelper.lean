module

public import FormalProof4FHE.HasteBoots.NativeGoldLookupProducer
public import FormalProof4FHE.HasteBoots.NativeHelperPacking

@[expose] public section

/-!
# Raw Goldilocks helper filling and coefficient packing

Copy the selected raw extension words, truncate at helper capacity, and pad
with raw zero. Packing copies all three stored coordinates and pads unused
lanes with raw zero. Semantic field equality is never used to normalize the
stored words. Native index panics are explicit failed preconditions here.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldHelper

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)

def fill : ℕ → List Word → List ℕ → Option (List Word)
  | 0, _, _ => some []
  | capacity + 1, _, [] => some (List.replicate (capacity + 1) NativeGoldLookup.zero)
  | capacity + 1, table, index :: tail =>
      (table[index]?).bind (fun value => (fill capacity table tail).map (fun rest => value :: rest))

def coefficient (width : ℕ) (value : Word) : Fin width → GoldWord :=
  fun lane => if meaningful : lane.val < 3 then value ⟨lane.val, meaningful⟩ else 0

def vector (width : ℕ) (value : Word) : List GoldWord := List.ofFn (coefficient width value)
def pack (width : ℕ) (values : List Word) : List GoldWord := values.flatMap (vector width)

theorem vector_length (width : ℕ) (value : Word) : (vector width value).length = width := List.length_ofFn

theorem pack_length (width : ℕ) (values : List Word) : (pack width values).length = values.length * width := by
  induction values with
  | nil => simp [pack]
  | cons value tail ih =>
    simp only [pack, List.flatMap_cons, List.length_append, vector_length] at *
    rw [ih, List.length_cons, Nat.succ_mul]
    exact Nat.add_comm _ _

theorem fill_spec (capacity : ℕ) (table : List Word) (indices : List ℕ) (values : List Word)
    (lookups : List.Forall₂ (fun index value => table[index]? = some value) indices values) :
    fill capacity table indices = some
      (values.take capacity ++ List.replicate (capacity - values.length) NativeGoldLookup.zero) := by
  induction lookups generalizing capacity with
  | nil => cases capacity <;> simp [fill]
  | @cons index value indices values known related ih =>
    cases capacity with
    | zero => simp [fill]
    | succ capacity =>
      simp only [fill, known, Option.bind_some, ih, List.take_succ_cons, List.length_cons,
        Nat.add_sub_add_right, List.cons_append, Option.map_some]

/-- Every raw packed address succeeds and returns exactly the stored word. -/
theorem pack_get (width : ℕ) (values : List Word) (row : ℕ) (present : row < values.length) (lane : Fin width) :
    (pack width values)[row * width + lane.val]? = some (coefficient width values[row] lane) := by
  induction values generalizing row with
  | nil => simp at present
  | cons value tail ih =>
    cases row with
    | zero =>
      rw [pack, List.flatMap_cons]
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by rw [vector_length]; exact lane.isLt)]
      unfold vector
      rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn]
    | succ row =>
      rw [pack, List.flatMap_cons]
      change (vector width value ++ pack width tail)[(row + 1) * width + lane.val]? = _
      rw [List.getElem?_append_right (by rw [vector_length, Nat.add_mul, one_mul]; omega), vector_length]
      have address : (row + 1) * width + lane.val - width = row * width + lane.val := by
        rw [Nat.add_mul, one_mul]
        omega
      rw [address]
      exact ih row (by simpa using present)

/-- Packing with adequate width is injective on raw objects, including
lazy Goldilocks words that have the same mathematical field value. -/
theorem pack_injective (width : ℕ) (enough : 3 ≤ width) : Function.Injective (pack width) := by
  intro left right same
  have lengths := congrArg List.length same
  rw [pack_length, pack_length] at lengths
  have length : left.length = right.length := Nat.eq_of_mul_eq_mul_right (by omega : 0 < width) lengths
  apply List.ext_getElem length
  intro index leftPresent rightPresent
  funext coordinate
  let lane : Fin width := ⟨coordinate.val, coordinate.isLt.trans_le enough⟩
  have lhs := pack_get width left index leftPresent lane
  have rhs := pack_get width right index rightPresent lane
  rw [same] at lhs
  have words := Option.some.inj (lhs.symm.trans rhs)
  simpa only [coefficient, lane, dite_eq_left coordinate.isLt] using words

noncomputable section

/-- The exact raw fill projects to the existing semantic helper operation. -/
theorem fill_value (capacity : ℕ) (table : List Word) (indices : List ℕ) :
    (fill capacity table indices).map (List.map goldExtensionValue) =
      NativeLookupHelper.fill capacity (table.map goldExtensionValue) indices := by
  induction capacity generalizing indices with
  | zero => rfl
  | succ capacity ih =>
    cases indices with
    | nil => simp only [fill, NativeLookupHelper.fill, Option.map_some, List.map_replicate, NativeGoldLookup.zero_value]
    | cons index tail =>
      cases found : table[index]? with
      | none => simp only [fill, found, Option.bind_none, Option.map_none, NativeLookupHelper.fill, List.getElem?_map]
      | some value =>
        have recursive := ih tail
        cases rest : fill capacity table tail with
        | none =>
          rw [rest, Option.map_none] at recursive
          simp only [fill, Option.bind_some, rest, Option.map_none, NativeLookupHelper.fill,
            List.getElem?_map, found, Option.map_some, recursive.symm, Option.bind_none]
        | some values =>
          rw [rest, Option.map_some] at recursive
          simp only [fill, Option.bind_some, rest, Option.map_some, NativeLookupHelper.fill,
            List.getElem?_map, found, recursive.symm, Option.bind_some, List.map_cons]

theorem fill_length (capacity : ℕ) (table : List Word) (indices : List ℕ) (values : List Word)
    (filled : fill capacity table indices = some values) : values.length = capacity := by
  have related := fill_value capacity table indices
  rw [filled, Option.map_some] at related
  have length := NativeLookupHelper.fill_length capacity (table.map goldExtensionValue) indices
    (values.map goldExtensionValue) related.symm
  simpa only [List.length_map] using length

theorem coefficient_value (width : ℕ) (value : Word) (lane : Fin width) :
    goldValue (coefficient width value lane) =
      NativeHelperPacking.coefficients goldilocksBasis width (goldExtensionValue value) lane := by
  by_cases meaningful : lane.val < 3
  · simp only [coefficient, NativeHelperPacking.coefficients, dite_eq_left meaningful, goldExtension_coordinate]
  · simp only [coefficient, NativeHelperPacking.coefficients, dite_eq_right meaningful,
      goldValue, Fin.val_zero, Nat.cast_zero]

theorem vector_value (width : ℕ) (value : Word) :
    (vector width value).map goldValue = NativeHelperPacking.vector goldilocksBasis width (goldExtensionValue value) := by
  simp only [vector, NativeHelperPacking.vector, List.map_ofFn, Function.comp_def, coefficient_value]

theorem pack_value (width : ℕ) (values : List Word) :
    (pack width values).map goldValue =
      NativeHelperPacking.pack goldilocksBasis width (values.map goldExtensionValue) := by
  simp only [pack, NativeHelperPacking.pack, List.map_flatMap, List.flatMap_map, vector_value]

end

end FormalProof4FHE.HasteBoots.NativeGoldHelper
