module
public import FormalProof4FHE.HasteBoots.LookupViewSumReduction
@[expose] public section

/-! One fresh original sum challenge has degree-one loss for fixed helper
tables. Adaptive allocated-table fixation/lifetime composition is separate. -/
namespace FormalProof4FHE.HasteBoots.SumCausalChallengeBound
open InputIndexedOracle (Input World law)
open NativeTranscript (Execution)
open NativeRootMessage (Digest)
open NativeExtensionFields (goldilocksBasis)
open MeasureTheory ProbabilityTheory
noncomputable section

theorem conditional_bound {S A : Type} {past : World → Execution (S ⊕ A)}
    (replay : ObservationReplay.Replayable past) (step : S → OracleMachine.Command S A)
    (world : World) (dummy profile : Digest) (input : Input) (configuration : ScalarRecoveredReplay.Configuration)
    (found : ScalarRecoveredReplay.recover input = some configuration)
    (selected : CausalStreamExposure.firstRead step (past world).run = some input)
    (n : NativeUsizeMessage.Usize) (message : NativeScalarBatchWire.Message) {helperPadding : ℕ}
    (helpers : MatrixFold.Cube n.val → Fin (3+helperPadding) → NativeFields.Goldilocks) :
    (law[|{other | (past other).run = (past world).run}])
      {other | ScalarRecoveredUnboundedLaw.event input configuration profile
        (ScalarSourceChallengeBound.test (LookupScalarGrammar.sumInfo n) message ScalarLookupExpression.sumArity
          ScalarLookupExpression.sumCoefficient ScalarLookupExpression.sumIndices n.val
          (LookupViewSumReduction.tables helpers)) other} ≤
      (1 : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  simpa only [LookupScalarGrammar.sumInfo,Nat.cast_one] using
    (ScalarSourceChallengeBound.bound replay step world dummy profile input configuration found selected
      (LookupScalarGrammar.sumInfo n) message ScalarLookupExpression.sumArity ScalarLookupExpression.sumCoefficient
      ScalarLookupExpression.sumIndices n.val (LookupViewSumReduction.tables helpers))

end
end FormalProof4FHE.HasteBoots.SumCausalChallengeBound
