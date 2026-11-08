namespace hasteboots_byte_reference
open Aeneas Aeneas.Std Result
open HasteBootsSlice64Runtime

theorem checked_read_exact (bytes : HasteBootsSlice64Runtime.Slice U8) (offset : U64) :
    checked_read bytes offset = ok (bytes.val[offset.val]?) := by
  simp only [checked_read]
  split
  next inside =>
    have bound : offset.val < bytes.val.length := inside
    have found := List.getElem?_eq_getElem bound
    simp only [index, found, bind_tc_ok]
  next outside =>
    have bound : bytes.val.length ≤ offset.val := Nat.le_of_not_lt outside
    simp only [List.getElem?_eq_none bound]

theorem checked_write_exact (bytes : HasteBootsSlice64Runtime.Slice U8) (offset : U64) (value : U8) :
    checked_write bytes offset value =
      ok (if offset.val < bytes.val.length then (true, set bytes offset value) else (false, bytes)) := by
  simp only [checked_write]
  split
  next inside =>
    have bound : offset.val < bytes.val.length := inside
    have found := List.getElem?_eq_getElem bound
    simp only [update, found, bind_tc_ok]
    simp only [bound, ite_true]
  next outside =>
    have bound : ¬ offset.val < bytes.val.length := outside
    simp only [bound, ite_false]

theorem checked_read_found (bytes : HasteBootsSlice64Runtime.Slice U8) (offset : U64) (value : U8)
    (found : bytes.val[offset.val]? = some value) : checked_read bytes offset = ok (some value) := by
  rw [checked_read_exact, found]

theorem checked_read_missing (bytes : HasteBootsSlice64Runtime.Slice U8) (offset : U64)
    (missing : bytes.val[offset.val]? = none) : checked_read bytes offset = ok none := by
  rw [checked_read_exact, missing]

theorem checked_write_inside (bytes : HasteBootsSlice64Runtime.Slice U8) (offset : U64) (value : U8)
    (inside : offset.val < bytes.val.length) :
    checked_write bytes offset value = ok (true, set bytes offset value) := by
  rw [checked_write_exact, ite_eq_left inside]

theorem checked_write_outside (bytes : HasteBootsSlice64Runtime.Slice U8) (offset : U64) (value : U8)
    (outside : ¬ offset.val < bytes.val.length) :
    checked_write bytes offset value = ok (false, bytes) := by
  rw [checked_write_exact, ite_eq_right outside]

theorem written_length (bytes : HasteBootsSlice64Runtime.Slice U8) (offset : U64) (value : U8) :
    (set bytes offset value).val.length = bytes.val.length := set_length bytes offset value

theorem written_selected (bytes : HasteBootsSlice64Runtime.Slice U8) (offset : U64) (value : U8)
    (inside : offset.val < bytes.val.length) :
    (set bytes offset value).val[offset.val]? = some value := by
  simp only [set_values, List.getElem?_set_self, inside]

theorem written_other (bytes : HasteBootsSlice64Runtime.Slice U8) (offset : U64) (value : U8)
    (other : Nat) (different : other ≠ offset.val) :
    (set bytes offset value).val[other]? = bytes.val[other]? := by
  simp only [set_values, List.getElem?_set, Ne.symm different, ite_false]

end hasteboots_byte_reference
