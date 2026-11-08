namespace HasteBootsInlineProof
open Aeneas Aeneas.Std Result
open hasteboots_inline_fixture

theorem adjust_zero (slot : U32) : adjust slot 0#u32 = ok (.Err (),slot) := by
  simp [adjust]

theorem twice_left_zero (slot right : U32) : twice slot 0#u32 right = ok (.Err (),slot) := by
  simp [twice,adjust]
  rfl

theorem twice_right_zero (slot left updated : U32) (nonzero : left ≠ 0#u32)
    (added : slot + left = ok updated) : twice slot left 0#u32 = ok (.Err (),updated) := by
  simp [twice,adjust,nonzero,added]
  rfl

theorem twice_success (slot left right updated finalValue : U32)
    (firstNonzero : left ≠ 0#u32) (secondNonzero : right ≠ 0#u32)
    (firstAdd : slot + left = ok updated) (secondAdd : updated + right = ok finalValue) :
    twice slot left right = ok (.Ok (slot,updated),finalValue) := by
  simp [twice,adjust,firstNonzero,secondNonzero,firstAdd,secondAdd]
  rfl

theorem twice_first_abort (slot left right : U32) (failure : Error)
    (nonzero : left ≠ 0#u32) (aborted : slot + left = fail failure) :
    twice slot left right = fail failure := by
  simp [twice,adjust,nonzero,aborted]

theorem twice_second_abort (slot left right updated : U32) (failure : Error)
    (firstNonzero : left ≠ 0#u32) (secondNonzero : right ≠ 0#u32)
    (firstAdd : slot + left = ok updated) (secondAdd : updated + right = fail failure) :
    twice slot left right = fail failure := by
  simp [twice,adjust,firstNonzero,secondNonzero,firstAdd,secondAdd]
  rfl

theorem capture_none (factor : Usize) : capture none factor = ok none := rfl

theorem capture_some (value factor : Usize) :
    capture (some value) factor = ok (Usize.checked_mul value factor) := rfl

end HasteBootsInlineProof
