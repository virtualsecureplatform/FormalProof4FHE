namespace HasteBootsUninhabitedProof
open Aeneas Aeneas.Std Result
open hasteboots_uninhabited
abbrev Input := hasteboots_uninhabited.core.result.Result.mono_4175b864abd865132345786a595924a2
abbrev Output := hasteboots_uninhabited.core.result.Result.mono_ba35f2f720a31c63939914016dc20577

theorem take_live (n : U64) : take (.Live n) = ok n := rfl

theorem take_exact (value : Only) :
    take value = ok (match value with | .Live n => n) := by
  cases value with
  | Impossible hole => cases hole
  | Live n => rfl

theorem nested_live (n : U64) : nested_take (.Live n) = ok n := rfl

theorem nested_exact (value : NestedOnly) :
    nested_take value = ok (match value with | .Live n => n) := by
  cases value with
  | Impossible wrapper => cases wrapper.hole
  | Live n => rfl

theorem residual_err (n : hasteboots_uninhabited.Error) : residual ((.Err n : Input)) = ok ((.Err n : Output)) := rfl

theorem residual_exact (value : Input) :
    residual value = ok (match value with | .Err n => (.Err n : Output)) := by
  cases value with
  | Ok hole => cases hole
  | Err n => rfl

end HasteBootsUninhabitedProof
