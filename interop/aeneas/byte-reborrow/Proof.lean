namespace hasteboots_byte_reborrow
open Aeneas Aeneas.Std Result
open HasteBootsSlice64Runtime

theorem replace_cell_exact (cell value : U8) : replace_cell cell value = ok (cell, value) := rfl

theorem replace_at_found (bytes : HasteBootsSlice64Runtime.Slice U8) (offset : U64) (previous value : U8)
    (found : bytes.val[offset.val]? = some previous) :
    replace_at bytes offset value = ok (some previous, set bytes offset value) := by
  have bound : offset.val < bytes.val.length := by
    by_contra outside
    rw [List.getElem?_eq_none (Nat.le_of_not_lt outside)] at found
    cases found
  have test : offset < len bytes := bound
  simp only [replace_at, ite_eq_left test, index_mut_found bytes offset previous found, bind_tc_ok, replace_cell]

theorem replace_at_outside (bytes : HasteBootsSlice64Runtime.Slice U8) (offset : U64) (value : U8)
    (outside : ¬ offset.val < bytes.val.length) : replace_at bytes offset value = ok (none, bytes) := by
  have test : ¬ offset < len bytes := outside
  simp only [replace_at, ite_eq_right test]

theorem replace_at_exact (bytes : HasteBootsSlice64Runtime.Slice U8) (offset : U64) (value : U8) :
    replace_at bytes offset value = ok (match bytes.val[offset.val]? with
      | none => (none, bytes)
      | some previous => (some previous, set bytes offset value)) := by
  cases found : bytes.val[offset.val]? with
  | none => exact replace_at_outside bytes offset value (Nat.not_lt_of_ge (List.getElem?_eq_none_iff.mp found))
  | some previous => exact replace_at_found bytes offset previous value found

end hasteboots_byte_reborrow
