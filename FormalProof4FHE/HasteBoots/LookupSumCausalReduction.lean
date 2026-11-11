module
public import FormalProof4FHE.HasteBoots.LookupGuardProducer
public import FormalProof4FHE.HasteBoots.LookupScalarGrammar
public import FormalProof4FHE.HasteBoots.ScalarSourceChallengeBound
@[expose] public section

/-! Actual completed scalar execution and its actual helper-sum guard force
an original completed-input causal event or a wrong original helper opening.
The common point and terminal getters are derived from native execution. -/
namespace FormalProof4FHE.HasteBoots.LookupSumCausalReduction
open MatrixFold (Cube)
open NativeFields (Goldilocks)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open NativeGoldExtensionArithmetic (Word)
open NativeFieldWire (goldExtensionValue)
open NativeScalarBatchWire (Statement Info)
open NativeScalarBatchPreflight (Proof)
open NativeTranscript (Transcript)
open NativeSharedLookupGuard (Inputs Result Checked)
open InputIndexedOracle (World)
noncomputable section

theorem event_or_wrong {padding : ℕ} (transcript resultTranscript : Transcript) (frames : List TranscriptFrame.Frame)
    (statement : Statement) (proof : Proof) (first : Info)
    (decoded : TranscriptFrame.decodeAll transcript.input = some frames)
    (accepted : NativeScalarBatchPreflight.beginVerify transcript statement proof = .ok resultTranscript)
    (head : statement.infos.val.head? = some first)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain proof) (fuel : ℕ) (world : World)
    (claims : List NativeScalarBatchVerifier.SubClaim)
    (finished : (NativeScalarBatchVerifier.execute statement proof fuel
      (NativeScalarBatchVerifier.initial transcript statement proof) world).1.control = .finished claims)
    (data : Inputs) (sourceVars width : ℕ) (result : Result)
    (passed : NativeSharedLookupGuard.guard data claims sourceVars width = some result)
    (checked : Checked) (member : checked ∈ result.checked)
    (helpers : Cube first.numVariables.val → Fin (3+padding) → Goldilocks)
    (infoAt : statement.infos.val[2*checked.ordinal]? = some (LookupScalarGrammar.sumInfo first.numVariables))
    (initial : ScalarChainHealing.value (2*checked.ordinal) statement.claims.val ≠
      some (ScalarNativeSourceHealing.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
        first.numVariables.val (fun _ cell => PaddedExtension.decode goldilocksBasis (helpers cell)) [])) :
    (∃ entry ∈ (NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed,
      ∃ message, entry.packet.messages.val[2*checked.ordinal]? = some message ∧
        ∃ configuration : ScalarRecoveredReplay.Configuration,
          ScalarRecoveredReplay.recover entry.coefficients.phase.pending.input = some configuration ∧
          ScalarRecoveredUnboundedLaw.event entry.coefficients.phase.pending.input configuration transcript.profile
            (ScalarSourceChallengeBound.test (LookupScalarGrammar.sumInfo first.numVariables) message ScalarLookupExpression.sumArity
              ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices first.numVariables.val
              (fun _ cell => PaddedExtension.decode goldilocksBasis (helpers cell))) world) ∨
    ∃ point : Fin first.numVariables.val → Word, List.ofFn point = result.point ∧
      NativeHelperPacking.coefficients goldilocksBasis (3+padding) (goldExtensionValue checked.helper) ≠
        (ExtensionQuery.coefficientsQuery goldilocksBasis (fun i => goldExtensionValue (point i))).query.fold helpers := by
  have linked := NativeSharedLookupBatchLink.initialized_link data transcript resultTranscript statement proof first accepted head
    fuel world claims finished sourceVars width result passed
  have evidence := linked.guard.checked checked member
  let point : Fin first.numVariables.val → Word := fun i => result.point[i.val]'(by rw [linked.length]; exact i.isLt)
  have rebuilt : List.ofFn point = result.point := by
    apply List.ext_getElem (by rw [List.length_ofFn,linked.length])
    intro i leftPresent rightPresent
    simp only [List.getElem_ofFn,point]
  rcases LookupNativeTerminal.sum_or_wrong point checked.helper checked.sumClaim.expected evidence.matched helpers with truthful | wrong
  · apply Or.inl
    have expectedEq : claims.map NativeScalarBatchVerifier.SubClaim.expected =
        (NativeScalarBatchVerifier.execute statement proof fuel
          (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.expected := by
      rw [linked.batch.2.2.2.2.1,List.map_map]
      change (NativeScalarBatchVerifier.execute statement proof fuel
        (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.expected.map id = _
      exact List.map_id _
    have terminalTruth : ScalarChainHealing.value (2*checked.ordinal)
        (NativeScalarBatchVerifier.execute statement proof fuel
          (NativeScalarBatchVerifier.initial transcript statement proof) world).1.state.expected =
      some (ScalarNativeSourceHealing.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
        first.numVariables.val (fun _ cell => PaddedExtension.decode goldilocksBasis (helpers cell))
        ((NativeScalarBatchVerifier.execute statement proof fuel
          (NativeScalarBatchVerifier.initial transcript statement proof) world).1.completed.map (fun entry => entry.challenge))) := by
      rw [← expectedEq,ScalarChainHealing.value,List.getElem?_map,Option.map_map,evidence.sum,Option.map_some]
      exact congrArg some (truthful.trans (congrArg
        (ScalarNativeSourceHealing.truth ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
          first.numVariables.val (fun _ cell => PaddedExtension.decode goldilocksBasis (helpers cell))) (rebuilt.trans linked.point)))
    have alternative := ScalarSourceChallengeBound.false_or_event transcript resultTranscript frames statement proof decoded accepted statementFits
      domain first head fuel world ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices
      (fun _ cell => PaddedExtension.decode goldilocksBasis (helpers cell)) (2*checked.ordinal)
      (LookupScalarGrammar.sumInfo first.numVariables) infoAt (LookupScalarGrammar.sum_arity first.numVariables) initial
    exact alternative.resolve_left (fun falseFinal => falseFinal terminalTruth)
  · exact Or.inr ⟨point,rebuilt,wrong⟩

end
end FormalProof4FHE.HasteBoots.LookupSumCausalReduction
