module
import all FormalProof4FHE.HasteBoots.LookupHelperClaimMeaning
import all FormalProof4FHETest.HasteBootsSmoke
import all FormalProof4FHETest.HasteBootsSingleSelectedSmoke

namespace FormalProof4FHE.HasteBoots.LookupHelperClaimSmoke
open NativeFieldRepresentation (goldValue)
open NativeTranscript (Transcript)
open HasteBootsSmoke.SharedLookupGuardSmoke (data aliasClaims helper0)
noncomputable section

/-- The actual guard fixture accepts a noncanonical sum word while retaining
its distinct raw spelling. Equality here licenses field interpretation only. -/
example : (NativeSharedLookupGuard.guard data aliasClaims 1 4).isSome = true := by decide +kernel

example : (NativeGoldHelper.vector 4 (aliasClaims[0]'(by decide +kernel)).expected) ≠ NativeGoldHelper.vector 4 helper0 ∧
    (NativeGoldHelper.vector 4 (aliasClaims[0]'(by decide +kernel)).expected).map goldValue = (NativeGoldHelper.vector 4 helper0).map goldValue := by
  constructor
  · decide +kernel
  · exact SingleHelperNativeValue.matched_vector 4 _ _ (by decide +kernel)

/-- Apply the semantic guard theorem to the actual retained checked entry. -/
def guarded := (NativeSharedLookupGuard.guard data aliasClaims 1 4).get (by decide +kernel)
def first : NativeSharedLookupGuard.Checked := guarded.checked[0]'(by decide +kernel)

theorem guarded_spec : NativeSharedLookupGuard.guard data aliasClaims 1 4 = some guarded := (Option.some_get _).symm

example : (NativeGoldHelper.vector 4 first.sumClaim.expected).map goldValue =
    (NativeGoldHelper.vector 4 first.helper).map goldValue :=
  SingleHelperNativeValue.guard_vector data aliasClaims 1 4 guarded guarded_spec first (List.getElem_mem (by decide +kernel))

/-- Helper widths three/four retain the same meaningful coefficients, with
only the independently selected helper padding appended. -/
example : NativeGoldHelper.vector 3 helper0 = [17,19,23] ∧
    NativeGoldHelper.vector 4 helper0 = [17,19,23,0] := by decide +kernel

/-- Both permitted helper widths interpret the original common point as the
coefficient query; no equality to the source packing width is required. -/
example (point : Fin 3 → NativeGoldExtensionArithmetic.Word) :
    NativeGoldCoefficientsQuery.interpret 3 3 (NativeGoldCoefficientsQuery.built 3 (List.ofFn point)) =
      some (ExtensionQuery.coefficientsQuery (padding := 0) NativeExtensionFields.goldilocksBasis
        (fun index => NativeFieldWire.goldExtensionValue (point index))) :=
  NativeGoldCoefficientsQuery.interpret_built (padding := 0) point (by decide +kernel)

example (point : Fin 3 → NativeGoldExtensionArithmetic.Word) :
    NativeGoldCoefficientsQuery.interpret 4 3 (NativeGoldCoefficientsQuery.built 4 (List.ofFn point)) =
      some (ExtensionQuery.coefficientsQuery (padding := 1) NativeExtensionFields.goldilocksBasis
        (fun index => NativeFieldWire.goldExtensionValue (point index))) :=
  NativeGoldCoefficientsQuery.interpret_built (padding := 1) point (by decide +kernel)

/-- Point reconstruction keeps the original coordinate order for any body. -/
example (body : NativeSharedLookupBody.Bound) : List.ofFn (LookupHelperClaimMeaning.point body) = body.terminal.point :=
  LookupHelperClaimMeaning.point_list body

end
end FormalProof4FHE.HasteBoots.LookupHelperClaimSmoke
