import Aeneas.Std.Primitives

/-! Isolated backend regressions. No Rust extraction is claimed here. -/
namespace HasteBootsAeneasProbe

open Aeneas.Std

example : (Result.ok 3 >>= fun n => Result.ok (n + 1)) = Result.ok 4 := rfl

example : ((Result.fail Error.integerOverflow : Result Nat) >>= fun n => Result.ok (n + 1)) =
    Result.fail Error.integerOverflow := rfl

example : ((Result.div : Result Nat) >>= fun n => Result.ok (n + 1)) = Result.div := rfl

-- Realization must work from a non-root namespace and remain idempotent.
inductive Tag where
  | first | second
  deriving Aeneas.BvEnumToBitVec

#define_bv_decide_toBitVec Tag

example : Tag.enumToBitVec .first = 0 := rfl
example : Tag.enumToBitVec .second = 1 := rfl

end HasteBootsAeneasProbe
