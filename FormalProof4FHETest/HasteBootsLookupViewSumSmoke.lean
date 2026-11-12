module
import all FormalProof4FHE.HasteBoots.AllocatedSumAlternatives
import all FormalProof4FHE.HasteBoots.SumCausalChallengeBound
import all FormalProof4FHETest.HasteBootsLookupIdentitySmoke

namespace HasteBootsLookupViewSumSmoke
open FormalProof4FHE.HasteBoots
open FormalProof4FHE.HasteBoots.LookupIdentitySmoke
open HasteBootsScalarFinishAncestrySmoke (usize)
open HasteBootsSamplerAncestrySmoke (child worldZero)
open ScalarExecutionRecoverySmoke (before decoded)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeFieldWire (goldExtensionValue)
noncomputable section

theorem sum_truth : ScalarNativeSourceHealing.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient
    ScalarLookupExpression.sumIndices 2 (LookupViewSumReduction.tables (helperPadding := 5) helpers) [] = 1 := by
  change ScalarNativeSourceHealing.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient
    ScalarLookupExpression.sumIndices 2 (fun _ cell => PaddedExtension.decode (padding := 5) goldilocksBasis (helpers cell)) [] = 1
  simp only [ScalarNativeSourceHealing.truth,List.map_nil,ScalarLookupExpression.sum_initial,
    helpers,PaddedExtension.decode_encode]
  have original := ScalarSourceSmoke.initial_truth
  simpa only [ScalarSourceSmoke.sourceTruth,ScalarNativeSourceHealing.truth,List.map_nil,ScalarSourcePolynomial.truth,
    ScalarSourceSmoke.single_expressionG] using original

theorem sum_initially_false : ScalarChainHealing.value 0 statement.claims.val ≠
    some (ScalarNativeSourceHealing.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient
      ScalarLookupExpression.sumIndices 2 (LookupViewSumReduction.tables (helperPadding := 5) helpers) []) := by
  have getter : statement.claims.val[0]? = some NativeGoldLookup.zero := rfl
  simp only [ScalarChainHealing.value,getter,Option.map_some,sum_truth,NativeGoldLookup.zero_value,ne_eq,Option.some.injEq]
  exact zero_ne_one

theorem original_sum_claim : claims[0]? = some view.checked.sumClaim := by decide +kernel

theorem original_sum_matched : NativeGoldInterpolation.equal view.checked.sumClaim.expected view.checked.helper = true := by decide +kernel

def Healing : Prop := ScalarFinishedSourceEvent.Event child statement proof 9 worldZero ScalarLookupExpression.sumArity
  ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices 2 (LookupViewSumReduction.tables (helperPadding := 5) helpers) 0
  (LookupScalarGrammar.sumInfo (usize 2))

theorem sum_event_or_wrong : Healing ∨ LookupViewSumReduction.Wrong (helperPadding := 5) view helpers :=
  LookupViewSumReduction.event_or_wrong (helperPadding := 5) view child before statement proof decoded (by decide +kernel) domain 9 worldZero
    finished rfl original_sum_claim original_sum_matched helpers sum_initially_false

theorem helper_opening_truthful : ¬LookupViewSumReduction.Wrong (helperPadding := 5) view helpers := by
  have point : view.point = fun _ => NativeGoldLookup.zero := by decide +kernel
  have helper : view.checked.helper = NativeGoldLookup.zero := by decide +kernel
  have folded : (ExtensionQuery.coefficientsQuery (padding := 5) goldilocksBasis (fun _ : Fin 2 => (0 : Goldilocks3))).query.fold helpers =
      PaddedExtension.encode (padding := 5) goldilocksBasis 0 := by
    have evaluated := ExtensionQuery.coefficients_evaluate (padding := 5) goldilocksBasis (fun _ : Fin 2 => (0 : Goldilocks3)) helpers
    change (ExtensionQuery.coefficientsQuery (padding := 5) goldilocksBasis (fun _ : Fin 2 => (0 : Goldilocks3))).query.fold helpers = _ at evaluated
    simpa [helpers,PaddedExtension.decode_encode,ExtensionQuery.evaluate,ScalarSourceSmoke.jointTable] using evaluated
  unfold LookupViewSumReduction.Wrong
  rw [point,helper]
  simp only [NativeGoldLookup.zero_value]
  rw [NativeHelperPacking.coefficients_padded goldilocksBasis 5 (0 : Goldilocks3)]
  intro wrong
  exact wrong folded.symm

theorem actual_even_slot_healing : Healing := sum_event_or_wrong.resolve_right helper_opening_truthful

theorem both_original_equations_false :
    (ScalarChainHealing.value 0 statement.claims.val ≠ some (ScalarNativeSourceHealing.truth ScalarLookupExpression.sumArity
      ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices 2 (LookupViewSumReduction.tables (helperPadding := 5) helpers) [])) ∧
    (ScalarChainHealing.value 1 statement.claims.val ≠ some (ScalarNativeSourceHealing.truth ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue job.output.r)) ExtensionLookupIdentity.partialIndices 2
      (LookupIdentityCausalReduction.partialTables (helperPadding := 5) view sources helpers) [])) :=
  ⟨sum_initially_false,initiallyFalse⟩

theorem separate_equation_degrees : statement.infos.val.map (fun info => info.maxMultiplicands.val) = [1,4] := by decide +kernel

def otherHelpers (_ : MatrixFold.Cube 2) : Fin 8 → NativeFields.Goldilocks :=
  PaddedExtension.encode (padding := 5) goldilocksBasis (1 : Goldilocks3)

theorem changed_helper_table_wrong : LookupViewSumReduction.Wrong (helperPadding := 5) view otherHelpers := by
  have point : view.point = fun _ => NativeGoldLookup.zero := by decide +kernel
  have helper : view.checked.helper = NativeGoldLookup.zero := by decide +kernel
  have folded : (ExtensionQuery.coefficientsQuery (padding := 5) goldilocksBasis (fun _ : Fin 2 => (0 : Goldilocks3))).query.fold otherHelpers =
      PaddedExtension.encode (padding := 5) goldilocksBasis 1 := by
    have evaluated := ExtensionQuery.coefficients_evaluate (padding := 5) goldilocksBasis (fun _ : Fin 2 => (0 : Goldilocks3)) otherHelpers
    change (ExtensionQuery.coefficientsQuery (padding := 5) goldilocksBasis (fun _ : Fin 2 => (0 : Goldilocks3))).query.fold otherHelpers = _ at evaluated
    have oneDecoded := PaddedExtension.decode_encode (padding := 5) goldilocksBasis (1 : Goldilocks3)
    simpa [otherHelpers,oneDecoded,ExtensionQuery.evaluate] using evaluated
  unfold LookupViewSumReduction.Wrong
  rw [point,helper]
  simp only [NativeGoldLookup.zero_value]
  rw [NativeHelperPacking.coefficients_padded goldilocksBasis 5 (0 : Goldilocks3)]
  change PaddedExtension.encode (padding := 5) goldilocksBasis (0 : Goldilocks3) ≠
    (ExtensionQuery.coefficientsQuery (padding := 5) goldilocksBasis (fun _ : Fin 2 => (0 : Goldilocks3))).query.fold otherHelpers
  rw [folded]
  intro equal
  have value := congrArg (PaddedExtension.decode (padding := 5) goldilocksBasis) equal
  simp only [PaddedExtension.decode_encode] at value
  exact zero_ne_one value

theorem original_common_point : view.checked.sumClaim.point = view.checked.identityClaim.point := by decide +kernel

end
end HasteBootsLookupViewSumSmoke
