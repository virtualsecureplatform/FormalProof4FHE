module
public import FormalProof4FHE.HasteBoots.LookupTerminalDecoding
public import FormalProof4FHE.HasteBoots.ScalarNativeSourceHealing
@[expose] public section

/-! Actual native terminal acceptance yields the concrete source-derived
scalar truth or a wrong original base-field opening. Raw producer powers,
used source decoders, helper coefficients and point getters are derived. -/
namespace FormalProof4FHE.HasteBoots.LookupNativeTerminal
open scoped BigOperators
open MatrixFold (Cube)
open NativeFields (Goldilocks)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeFieldRepresentation (GoldWord goldValue)
open NativeFieldWire (goldExtensionValue)
open NativeGoldExtensionArithmetic (Word)
open NativeScalarQueryShape (laneBits)
noncomputable section

theorem partial_or_wrong {padding helperPadding row columns : ℕ}
    (eqPoint point : Fin (laneBits (3+padding)+row) → Word)
    (accepted : NativeScalarQueryShape.check row (3+padding) (List.ofFn point).length = true)
    (logical : NativeUsizeMessage.Usize) (shift : laneBits (3+padding)+row < 64)
    (enough : logical.val ≤ 2^(laneBits (3+padding)+row))
    (rows : List (List GoldWord)) (selection : NativeLookupChallenge.Machine Goldilocks3)
    (output : NativeGoldLookupProducer.Output) (produced : NativeGoldLookupProducer.produce columns rows selection = some output)
    (inputs : Fin columns → Fin (3+padding) → GoldWord) (helper expected : Word)
    (passed : NativeGoldTerminalQuery.constructedCheck row (3+padding) (List.ofFn eqPoint) (List.ofFn point) logical output.r
      (List.ofFn (fun i => List.ofFn (inputs i))) output.powers helper expected = some true)
    (sources : Fin columns → Cube row → Fin (3+padding) → Goldilocks)
    (helpers : Cube (laneBits (3+padding)+row) → Fin (3+helperPadding) → Goldilocks) :
    goldExtensionValue expected = ScalarNativeSourceHealing.truth ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue output.r)) ExtensionLookupIdentity.partialIndices _
      (ExtensionLookupIdentity.factors (fun i => goldExtensionValue (eqPoint i)) (goldExtensionValue output.y)
        (fun column => LookupSourceFlattening.flatten (NativeScalarQueryShape.checked_power _ _ _ accepted) (sources column))
        (fun cell => PaddedExtension.decode goldilocksBasis (helpers cell)) logical.val) (List.ofFn point) ∨
      (∃ i, (fun lane => goldValue (inputs i lane)) ≠
        (ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ accepted)
          (fun j => goldExtensionValue (point j))).query.fold (sources i)) ∨
      NativeHelperPacking.coefficients goldilocksBasis (3+helperPadding) (goldExtensionValue helper) ≠
        (ExtensionQuery.coefficientsQuery goldilocksBasis (fun i => goldExtensionValue (point i))).query.fold helpers := by
  obtain ⟨weights,rawWeights,powers⟩ := LookupTerminalDecoding.produced_vector columns rows selection output produced
  rw [rawWeights] at passed
  obtain ⟨decoded,allDecoded,checked⟩ := LookupTerminalDecoding.checked_decodes eqPoint point accepted logical shift enough
    output.r inputs weights helper expected passed
  have fieldChecked : ExtensionLookupIdentity.terminal (fun i => goldExtensionValue (eqPoint i)) (fun i => goldExtensionValue (point i))
      (goldExtensionValue output.r) (∑ i, goldExtensionValue output.y^i.val * decoded i) (goldExtensionValue helper)
      logical.val enough = goldExtensionValue expected := by simpa only [powers] using checked
  have result := ScalarLookupExpression.partial_checked_or_wrong goldilocksBasis
    (NativeScalarQueryShape.checked_power _ _ _ accepted) (fun i => goldExtensionValue (eqPoint i)) (fun i => goldExtensionValue (point i))
    (goldExtensionValue output.r) (goldExtensionValue output.y) logical.val enough sources helpers (fun i lane => goldValue (inputs i lane))
    (NativeHelperPacking.coefficients goldilocksBasis (3+helperPadding) (goldExtensionValue helper)) decoded
    (goldExtensionValue helper) (goldExtensionValue expected) allDecoded
    (LookupTerminalDecoding.helper_decodes (fun i => goldExtensionValue (point i)) helper) fieldChecked
  simpa only [ScalarNativeSourceHealing.truth,List.map_ofFn,Function.comp_def] using result

theorem full_or_wrong {padding helperPadding row columns : ℕ}
    (eqPoint point : Fin (laneBits (3+padding)+row) → Word)
    (accepted : NativeScalarQueryShape.check row (3+padding) (List.ofFn point).length = true)
    (logical : NativeUsizeMessage.Usize) (shift : laneBits (3+padding)+row < 64)
    (full : logical.val = 2^(laneBits (3+padding)+row))
    (rows : List (List GoldWord)) (selection : NativeLookupChallenge.Machine Goldilocks3)
    (output : NativeGoldLookupProducer.Output) (produced : NativeGoldLookupProducer.produce columns rows selection = some output)
    (inputs : Fin columns → Fin (3+padding) → GoldWord) (helper expected : Word)
    (passed : NativeGoldTerminalQuery.constructedCheck row (3+padding) (List.ofFn eqPoint) (List.ofFn point) logical output.r
      (List.ofFn (fun i => List.ofFn (inputs i))) output.powers helper expected = some true)
    (sources : Fin columns → Cube row → Fin (3+padding) → Goldilocks)
    (helpers : Cube (laneBits (3+padding)+row) → Fin (3+helperPadding) → Goldilocks) :
    goldExtensionValue expected = ScalarNativeSourceHealing.truth ExtensionLookupIdentity.fullArity
      ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices _
      (LookupPairArithmetic.fullTables (fun i => goldExtensionValue (eqPoint i)) (goldExtensionValue output.r) (goldExtensionValue output.y)
        (fun column => LookupSourceFlattening.flatten (NativeScalarQueryShape.checked_power _ _ _ accepted) (sources column))
        (fun cell => PaddedExtension.decode goldilocksBasis (helpers cell))) (List.ofFn point) ∨
      (∃ i, (fun lane => goldValue (inputs i lane)) ≠
        (ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ accepted)
          (fun j => goldExtensionValue (point j))).query.fold (sources i)) ∨
      NativeHelperPacking.coefficients goldilocksBasis (3+helperPadding) (goldExtensionValue helper) ≠
        (ExtensionQuery.coefficientsQuery goldilocksBasis (fun i => goldExtensionValue (point i))).query.fold helpers := by
  obtain ⟨weights,rawWeights,powers⟩ := LookupTerminalDecoding.produced_vector columns rows selection output produced
  rw [rawWeights] at passed
  obtain ⟨decoded,allDecoded,checked⟩ := LookupTerminalDecoding.checked_decodes eqPoint point accepted logical shift
    (by rw [full]) output.r inputs weights helper expected passed
  have fieldChecked : ExtensionLookupIdentity.terminal (fun i => goldExtensionValue (eqPoint i)) (fun i => goldExtensionValue (point i))
      (goldExtensionValue output.r) (∑ i, goldExtensionValue output.y^i.val * decoded i) (goldExtensionValue helper)
      (2^(laneBits (3+padding)+row)) le_rfl = goldExtensionValue expected := by simpa only [powers,full] using checked
  have result := ScalarLookupExpression.full_checked_or_wrong goldilocksBasis
    (NativeScalarQueryShape.checked_power _ _ _ accepted) (fun i => goldExtensionValue (eqPoint i)) (fun i => goldExtensionValue (point i))
    (goldExtensionValue output.r) (goldExtensionValue output.y) sources helpers (fun i lane => goldValue (inputs i lane))
    (NativeHelperPacking.coefficients goldilocksBasis (3+helperPadding) (goldExtensionValue helper)) decoded
    (goldExtensionValue helper) (goldExtensionValue expected) allDecoded
    (LookupTerminalDecoding.helper_decodes (fun i => goldExtensionValue (point i)) helper) fieldChecked
  simpa only [ScalarNativeSourceHealing.truth,List.map_ofFn,Function.comp_def] using result

/-- The native matched helper-sum claim has its concrete scalar truth or a
wrong original coefficient opening; the raw equality guard supplies matching. -/
theorem sum_or_wrong {padding n : ℕ} (point : Fin n → Word) (helper expected : Word)
    (matched : NativeGoldInterpolation.equal expected helper = true)
    (helpers : Cube n → Fin (3+padding) → Goldilocks) :
    goldExtensionValue expected = ScalarNativeSourceHealing.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient
        ScalarLookupExpression.sumIndices n (fun _ cell => PaddedExtension.decode goldilocksBasis (helpers cell)) (List.ofFn point) ∨
      NativeHelperPacking.coefficients goldilocksBasis (3+padding) (goldExtensionValue helper) ≠
        (ExtensionQuery.coefficientsQuery goldilocksBasis (fun i => goldExtensionValue (point i))).query.fold helpers := by
  have equal : goldExtensionValue expected = goldExtensionValue helper := by
    simpa only [NativeGoldInterpolation.equal_value,NativeInterpolationField.arithmetic,decide_eq_true_eq] using matched
  have result := ScalarLookupExpression.sum_checked_or_wrong goldilocksBasis (fun i => goldExtensionValue (point i)) helpers
    (NativeHelperPacking.coefficients goldilocksBasis (3+padding) (goldExtensionValue helper)) (goldExtensionValue helper)
    (goldExtensionValue expected) (LookupTerminalDecoding.helper_decodes (fun i => goldExtensionValue (point i)) helper) equal
  simpa only [ScalarNativeSourceHealing.truth,List.map_ofFn,Function.comp_def] using result

end
end FormalProof4FHE.HasteBoots.LookupNativeTerminal
