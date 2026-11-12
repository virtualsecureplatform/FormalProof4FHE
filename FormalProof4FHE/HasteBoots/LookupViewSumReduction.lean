module
public import FormalProof4FHE.HasteBoots.LookupIdentityCausalReduction
@[expose] public section

/-! The even-slot helper-sum equation uses the original native claim and the
same completed scalar point as its neighboring identity equation. -/
namespace FormalProof4FHE.HasteBoots.LookupViewSumReduction
open MatrixFold (Cube)
open NativeFields (Goldilocks)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeFieldWire (goldExtensionValue)
open NativeScalarQueryShape (laneBits)
open LookupIdentityView (View)
noncomputable section

variable {padding row : ℕ} {n : NativeUsizeMessage.Usize} {job : NativeSharedLookupStatement.Prepared}
    {claims : List NativeScalarBatchVerifier.SubClaim} {result : NativeSharedLookupGuard.Result} {ordinal : ℕ}

def tables {helperPadding dimension : ℕ} (helpers : Cube dimension → Fin (3+helperPadding) → Goldilocks) :
    ExtensionLookupIdentity.Factor → Cube dimension → Goldilocks3 := fun _ cell => PaddedExtension.decode goldilocksBasis (helpers cell)

def Wrong {helperPadding : ℕ} (view : View padding row n job claims result ordinal)
    (helpers : Cube (laneBits (3+padding)+row) → Fin (3+helperPadding) → Goldilocks) : Prop :=
  NativeHelperPacking.coefficients goldilocksBasis (3+helperPadding) (goldExtensionValue view.checked.helper) ≠
    (ExtensionQuery.coefficientsQuery goldilocksBasis (fun i => goldExtensionValue (view.point i))).query.fold helpers

theorem event_or_wrong {helperPadding : ℕ} (view : View padding row n job claims result ordinal)
    (transcript : NativeTranscript.Transcript) (frames : List TranscriptFrame.Frame)
    (statement : NativeScalarBatchWire.Statement) (proof : NativeScalarBatchPreflight.Proof)
    (decoded : TranscriptFrame.decodeAll transcript.input = some frames)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof) (fuel : ℕ) (world : InputIndexedOracle.World)
    (finished : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .finished claims)
    (infoAt : statement.infos.val[2*ordinal]? = some (LookupScalarGrammar.sumInfo n))
    (sumAt : claims[2*ordinal]? = some view.checked.sumClaim)
    (matched : NativeGoldInterpolation.equal view.checked.sumClaim.expected view.checked.helper = true)
    (helpers : Cube (laneBits (3+padding)+row) → Fin (3+helperPadding) → Goldilocks)
    (initial : ScalarChainHealing.value (2*ordinal) statement.claims.val ≠
      some (ScalarNativeSourceHealing.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient
        ScalarLookupExpression.sumIndices (laneBits (3+padding)+row) (tables helpers) [])) :
    ScalarFinishedSourceEvent.Event transcript statement proof fuel world ScalarLookupExpression.sumArity
      ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices (laneBits (3+padding)+row)
      (tables helpers) (2*ordinal) (LookupScalarGrammar.sumInfo n) ∨ Wrong view helpers := by
  obtain ⟨bound,first,accepted,head⟩ := NativeSharedLookupBody.finished_preflight transcript statement proof fuel world claims finished
  have contract := NativeScalarBatchContract.finished_contract transcript bound statement proof first accepted head fuel world claims finished
  have output := NativeScalarBatchContract.contract_output statement proof first _ claims contract
  have identity := output.2.2 view.checked.identityClaim (List.mem_of_getElem? view.claimAt)
  have sum := output.2.2 view.checked.sumClaim (List.mem_of_getElem? sumAt)
  have dimension : first.numVariables.val = laneBits (3+padding)+row := by
    have claimLength := identity.2
    rw [view.claimPoint,List.length_ofFn] at claimLength
    exact claimLength.symm
  have sumPoint : view.checked.sumClaim.point = List.ofFn view.point := sum.1.trans (identity.1.symm.trans view.claimPoint)
  rcases LookupNativeTerminal.sum_or_wrong view.point view.checked.helper view.checked.sumClaim.expected matched helpers with truthful | wrong
  · left
    apply ScalarFinishedSourceEvent.of_claim transcript bound frames statement proof decoded accepted first head statementFits domain
      fuel world claims finished ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
      (laneBits (3+padding)+row) dimension (tables helpers) (2*ordinal) (LookupScalarGrammar.sumInfo n) infoAt
      (LookupScalarGrammar.sum_arity n) initial view.checked.sumClaim sumAt
    rw [sumPoint]
    exact truthful
  · exact Or.inr wrong

end
end FormalProof4FHE.HasteBoots.LookupViewSumReduction
