import Aeneas.Std

/-! Concrete usize-only ctlz_nonzero semantics. Zero is undefined in Rust's
intrinsic and is rejected here; defined nonzero inputs use the existing closed
bit-vector leading-zero operation. Platform width remains explicit in Usize. -/
namespace HasteBootsUsizeCtlz
open Aeneas Aeneas.Std

def nonzero (word : Usize) : Result U32 :=
  if word.val = 0 then .fail .undef
  else .ok (core.num.Usize.leading_zeros word)

theorem zero_rejected (word : Usize) (zero : word.val = 0) : nonzero word = .fail .undef := by
  simp only [nonzero,zero,ite_true]

theorem nonzero_result (word : Usize) (positive : word.val ≠ 0) :
    nonzero word = .ok (core.num.Usize.leading_zeros word) := by
  simp only [nonzero,positive,ite_false]

end HasteBootsUsizeCtlz

namespace HasteBootsUsizeCtlz
open Aeneas Aeneas.Std

theorem nonzero_bits (word : Usize) (positive : word.val ≠ 0) : word.bv ≠ 0 := by
  intro same
  apply positive
  have zeroValue : (0 : BitVec UScalarTy.Usize.numBits).toNat = 0 := BitVec.toNat_zero
  exact (congrArg BitVec.toNat same).trans zeroValue

theorem leading_value (word : Usize) (positive : word.val ≠ 0) :
    (core.num.Usize.leading_zeros word).val =
      UScalarTy.Usize.numBits - Nat.log 2 word.val - 1 := by
  have width : UScalarTy.Usize.numBits < 2^32 := by
    change (System.Platform.getNumBits ()).val < 2^32
    rcases (System.Platform.getNumBits ()).property with width32 | width64 <;> omega
  have fits : UScalarTy.Usize.numBits - Nat.log 2 word.val - 1 < 2^32 :=
    (Nat.sub_le _ _).trans_lt ((Nat.sub_le _ _).trans_lt width)
  simp only [core.num.Usize.leading_zeros,UScalar.val,
    BitVec.leadingZeros,nonzero_bits word positive,ite_false]
  exact Nat.mod_eq_of_lt fits

end HasteBootsUsizeCtlz
