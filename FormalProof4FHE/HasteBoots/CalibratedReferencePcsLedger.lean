module
public import FormalProof4FHE.HasteBoots.PrivateCoinReferenceProbability
@[expose] public section

/-! Non-root reference probabilities are now paid by original expected
specified work in the shared scalar/PCS ledger. Only PCS failures outside
the shared hash event remain as an explicit probability term here. -/
namespace FormalProof4FHE.HasteBoots.CalibratedReferencePcsLedger
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open NativeRootMessage (Digest)
noncomputable section

theorem bound {I : Type} (HelperMemory SourceMemory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (helper : NativeGoldPcsExecution.Context) (source : I → NativeGoldBatchPcsProgram.Context)
    (sourceOrigin : (i : I) → CacheBackedCodeOrigin.Origin (source i)) (helperRadius : ℕ) (sourceRadius : I → ℕ)
    (coins : Measure Tape) (scalarRadius : ℕ) :
    (coins.prod law) {execution | (∃ fuel, PrivateCoinScalarProbability.Event code publicData privateData dummy scalarRadius fuel execution) ∨
      PrivateCoinJointPcsLedger.Pcs HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin helperRadius sourceRadius execution} ≤
      (coins.prod law) {execution | (∃ fuel, OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius
        (privateProgram code publicData execution.1 privateData fuel) OracleProgramMachine.step execution.2) ∧
        ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} +
      PrivateCoinByteWork.expectedWork coins code publicData privateData *
        (1/(2 : ENNReal)^159 + (PrivateCoinSharedHash.rate+ScalarEquationWork.rate)) := by
  apply (PrivateCoinJointPcsLedger.bound HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin helperRadius sourceRadius coins scalarRadius).trans
  calc
    _ ≤ (PrivateCoinByteWork.expectedWork coins code publicData privateData * (1/(2 : ENNReal)^159) +
        (coins.prod law) {execution | (∃ fuel, OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin helperRadius sourceRadius
          (privateProgram code publicData execution.1 privateData fuel) OracleProgramMachine.step execution.2) ∧
          ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution}) +
        PrivateCoinByteWork.expectedWork coins code publicData privateData * (PrivateCoinSharedHash.rate+ScalarEquationWork.rate) :=
      add_le_add (add_le_add (PrivateCoinReferenceProbability.lifetime_le_159 coins code publicData privateData) le_rfl) le_rfl
    _ = _ := by simp only [mul_add]; ac_rfl

end
end FormalProof4FHE.HasteBoots.CalibratedReferencePcsLedger
