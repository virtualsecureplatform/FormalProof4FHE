/-! Kernel-checked values of freshly extracted Rust functions. -/
namespace HasteBootsStaticStringsProof
open Aeneas Aeneas.Std
open hasteboots_static_strings

private def expected (text : String) (bound : text.toByteArray.size ≤ U32.max) : Str := toStr text bound

theorem literal_exact : literal = .ok (expected "invalid dimensions or query count"
    (by simp only [U32.max,U32.numBits,UScalarTy.U32_numBits_eq]; decide +kernel)) := rfl

theorem nested_error_exact : nested_error = .ok (core.result.Result.Err (expected "table size overflow"
    (by simp only [U32.max,U32.numBits,UScalarTy.U32_numBits_eq]; decide +kernel))) := rfl

theorem conditional_true : conditional_error true = .ok (core.result.Result.Ok 7#u64) := rfl

theorem conditional_false : conditional_error false = .ok (core.result.Result.Err (expected "encoded size overflow"
    (by simp only [U32.max,U32.numBits,UScalarTy.U32_numBits_eq]; decide +kernel))) := rfl

theorem unicode_exact : unicode_literal = .ok (expected "π/秘密"
    (by simp only [U32.max,U32.numBits,UScalarTy.U32_numBits_eq]; decide +kernel)) := rfl

theorem escaped_exact : escaped_literal = .ok (expected "\"\\\n\t\r\u0000\u007f"
    (by simp only [U32.max,U32.numBits,UScalarTy.U32_numBits_eq]; decide +kernel)) := rfl

theorem borrow_identity (input : Str) : preserve_borrow input = .ok input := rfl

theorem unicode_bytes :
    (expected "π/秘密" (by simp only [U32.max,U32.numBits,UScalarTy.U32_numBits_eq]; decide +kernel)).val.map (fun byte => byte.val) =
      [207,128,47,231,167,152,229,175,134] := by decide +kernel

theorem escaped_bytes :
    (expected "\"\\\n\t\r\u0000\u007f" (by simp only [U32.max,U32.numBits,UScalarTy.U32_numBits_eq]; decide +kernel)).val.map (fun byte => byte.val) =
      [34,92,10,9,13,0,127] := by decide +kernel

end HasteBootsStaticStringsProof
