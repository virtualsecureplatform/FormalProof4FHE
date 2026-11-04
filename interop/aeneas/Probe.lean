import Aeneas.Std

/-! Isolated backend regressions. No Rust extraction is claimed here. -/
namespace HasteBootsAeneasProbe

open Aeneas.Std

example : (Result.ok 3 >>= fun n => Result.ok (n + 1)) = Result.ok 4 := rfl

example : ((Result.fail Error.integerOverflow : Result Nat) >>= fun n => Result.ok (n + 1)) =
    Result.fail Error.integerOverflow := rfl

example : ((Result.div : Result Nat) >>= fun n => Result.ok (n + 1)) = Result.div := rfl

example : core.num.U128.leading_zeros 0#u128 = 128#u32 := rfl
example : core.num.U128.leading_zeros 1#u128 = 127#u32 := rfl
example : core.num.U128.leading_zeros 18446744073709551615#u128 = 64#u32 := rfl

example : core.num.U32.from_le_bytes
    ⟨[1#u8, 2#u8, 3#u8, 4#u8], by decide⟩ = 67305985#u32 := rfl

-- Realization must work from a non-root namespace and remain idempotent.
inductive Tag where
  | first | second
  deriving Aeneas.BvEnumToBitVec

#define_bv_decide_toBitVec Tag

example : Tag.enumToBitVec .first = 0 := rfl
example : Tag.enumToBitVec .second = 1 := rfl

end HasteBootsAeneasProbe
