namespace HasteBootsInlineEquivalence
open Aeneas Aeneas.Std Result

abbrev PairResult := hasteboots_inline_candidate.core.result.Result.mono_1e0f10563073db9afabf8f7767aeb793

def decodePair : PairResult → core.result.Result (U32 × U32) Unit
  | .Ok value => .Ok value
  | .Err error => .Err error

def decodeTwice : Result (PairResult × U32) → Result (core.result.Result (U32 × U32) Unit × U32)
  | .ok (value, state) => .ok (decodePair value, state)
  | .fail error => .fail error
  | .div => .div

def encodePair : core.result.Result (U32 × U32) Unit → PairResult
  | .Ok value => .Ok value
  | .Err error => .Err error

def encodeTwice : Result (core.result.Result (U32 × U32) Unit × U32) → Result (PairResult × U32)
  | .ok (value, state) => .ok (encodePair value, state)
  | .fail error => .fail error
  | .div => .div

theorem decode_pair_encode (value : core.result.Result (U32 × U32) Unit) :
    decodePair (encodePair value) = value := by
  cases value <;> rfl

theorem encode_pair_decode (value : PairResult) :
    encodePair (decodePair value) = value := by
  cases value <;> rfl

theorem decode_twice_encode (result : Result (core.result.Result (U32 × U32) Unit × U32)) :
    decodeTwice (encodeTwice result) = result := by
  cases result with
  | ok value => rcases value with ⟨value, state⟩; cases value <;> rfl
  | fail error => rfl
  | div => rfl

theorem encode_twice_decode (result : Result (PairResult × U32)) :
    encodeTwice (decodeTwice result) = result := by
  cases result with
  | ok value => rcases value with ⟨value, state⟩; cases value <;> rfl
  | fail error => rfl
  | div => rfl

theorem capture_equivalent (value : Option Usize) (factor : Usize) :
    hasteboots_inline_candidate.capture value factor =
    hasteboots_inline_fixture.capture value factor := by
  cases value <;> rfl

theorem twice_equivalent (slot left right : U32) :
    decodeTwice (hasteboots_inline_candidate.twice slot left right) =
    hasteboots_inline_fixture.twice slot left right := by
  by_cases hl : left = 0#u32
  · simp [hasteboots_inline_candidate.twice, hasteboots_inline_fixture.twice,
      hasteboots_inline_fixture.adjust, hl, decodeTwice, decodePair,
      hasteboots_inline_candidate.core.result.Result.Insts.CoreOpsTry_traitTry.branch,
      hasteboots_inline_candidate.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      hasteboots_inline_candidate.Tuple.Insts.CoreConvertFromTuple.from]
    rfl
  · cases firstAdd : slot + left with
    | fail error => simp [hasteboots_inline_candidate.twice, hasteboots_inline_fixture.twice,
        hasteboots_inline_fixture.adjust, hl, firstAdd, decodeTwice]
    | div => simp [hasteboots_inline_candidate.twice, hasteboots_inline_fixture.twice,
        hasteboots_inline_fixture.adjust, hl, firstAdd, decodeTwice]
    | ok updated =>
      by_cases hr : right = 0#u32
      · simp [hasteboots_inline_candidate.twice, hasteboots_inline_fixture.twice,
          hasteboots_inline_fixture.adjust, hl, hr, firstAdd, decodeTwice, decodePair,
          hasteboots_inline_candidate.core.result.Result.Insts.CoreOpsTry_traitTry.branch,
          hasteboots_inline_candidate.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          hasteboots_inline_candidate.Tuple.Insts.CoreConvertFromTuple.from]
        rfl
      · cases secondAdd : updated + right <;>
          simp [hasteboots_inline_candidate.twice, hasteboots_inline_fixture.twice,
            hasteboots_inline_fixture.adjust, hl, hr, firstAdd, secondAdd, decodeTwice, decodePair,
            hasteboots_inline_candidate.core.result.Result.Insts.CoreOpsTry_traitTry.branch,
            hasteboots_inline_candidate.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            hasteboots_inline_candidate.Tuple.Insts.CoreConvertFromTuple.from] <;> rfl

end HasteBootsInlineEquivalence
