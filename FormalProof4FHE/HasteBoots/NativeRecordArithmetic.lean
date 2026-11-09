module
public import FormalProof4FHE.HasteBoots.NativeRecordValues
@[expose] public section

/-! Typed fixed-width operations needed by the retained allocation constructor.
Overflow flags, wrapping operations and rejected preconditions are distinct.
The representation is logical; native scalar and tuple ABI refinement is open. -/
namespace FormalProof4FHE.HasteBoots.NativeRecordArithmetic
open NativeRecordValues (Value)
open NativeWord64Memory (Word)

inductive Operation where
  | checkedMultiply
  | greater
  | lessEqual
  | equal
  | wrappingSubtract
  | uncheckedSubtract
  | wrappingShiftLeft
  | bitOr
  | logicalNot
  deriving DecidableEq

def word (value : Nat) : Word := ⟨value % 2^64,Nat.mod_lt _ (by decide)⟩

def eval : Operation → List Value → Option Value
  | .checkedMultiply, [.scalar (.usize left),.scalar (.usize right)] =>
    some (.pair (.scalar (.usize (word (left.val * right.val))))
      (.pair (.boolean (decide (2^64 ≤ left.val * right.val))) (.scalar .unit)))
  | .greater, [.scalar (.usize left),.scalar (.usize right)] => some (.boolean (decide (right.val < left.val)))
  | .lessEqual, [.scalar (.usize left),.scalar (.usize right)] => some (.boolean (decide (left.val ≤ right.val)))
  | .equal, [.scalar (.usize left),.scalar (.usize right)] => some (.boolean (left == right))
  | .wrappingSubtract, [.scalar (.usize left),.scalar (.usize right)] =>
    some (.scalar (.usize (word (left.val + 2^64 - right.val))))
  | .uncheckedSubtract, [.scalar (.usize left),.scalar (.usize right)] =>
    if right.val ≤ left.val then
      some (.scalar (.usize ⟨left.val-right.val,lt_of_le_of_lt (Nat.sub_le _ _) left.isLt⟩)) else none
  | .wrappingShiftLeft, [.scalar (.usize left),.scalar (.usize right)] =>
    some (.scalar (.usize (word (left.val * 2^(right.val % 64)))))
  | .bitOr, [.scalar (.usize left),.scalar (.usize right)] => some (.scalar (.usize (word (Nat.lor left.val right.val))))
  | .logicalNot, [.boolean value] => some (.boolean (!value))
  | _, _ => none

theorem checked_multiply_bounded (left right : Word) (bound : left.val * right.val < 2^64) :
    eval .checkedMultiply [.scalar (.usize left),.scalar (.usize right)] =
      some (.pair (.scalar (.usize ⟨left.val*right.val,bound⟩)) (.pair (.boolean false) (.scalar .unit))) := by
  simp only [eval,word,Nat.mod_eq_of_lt bound,show ¬ 2^64 ≤ left.val*right.val from Nat.not_le_of_gt bound,decide_false]

theorem checked_byte_capacity (capacity : Word) :
    eval .checkedMultiply [.scalar (.usize 1),.scalar (.usize capacity)] =
      some (.pair (.scalar (.usize capacity)) (.pair (.boolean false) (.scalar .unit))) := by
  simpa only [show (1 : Word).val = 1 from rfl,Nat.one_mul] using
    checked_multiply_bounded 1 capacity (by simpa only [show (1 : Word).val = 1 from rfl,Nat.one_mul] using capacity.isLt)

theorem unchecked_subtract_underflow (left right : Word) (underflow : left.val < right.val) :
    eval .uncheckedSubtract [.scalar (.usize left),.scalar (.usize right)] = none := by
  simp only [eval,Nat.not_le_of_gt underflow,ite_false]

theorem logical_not_twice (value : Bool) :
    eval .logicalNot [.boolean (!value)] = some (.boolean value) := by
  simp only [eval,Bool.not_not]

theorem boolean_distinct (value : Bool) (word : Word) :
    NativeRecordValues.fits .boolean (.boolean value) = true ∧
      NativeRecordValues.fits .boolean (.scalar (.usize word)) = false ∧
      NativeRecordValues.fits (.scalar .usize) (.boolean value) = false := by
  exact ⟨rfl,rfl,rfl⟩

end FormalProof4FHE.HasteBoots.NativeRecordArithmetic
