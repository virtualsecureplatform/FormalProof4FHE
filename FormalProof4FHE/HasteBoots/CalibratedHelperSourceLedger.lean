module
public import FormalProof4FHE.HasteBoots.OriginalHelperJointProbability
public import FormalProof4FHE.HasteBoots.CalibratedReferencePcsLedger
@[expose] public section

/-! The original helper probability is discharged in the shared scalar/PCS
ledger. The indexed original source-family union stays explicit. -/
namespace FormalProof4FHE.HasteBoots.CalibratedHelperSourceLedger
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open NativeRootMessage (Digest)
noncomputable section

theorem bound {I : Type} (HelperMemory SourceMemory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)
    (helper : NativeGoldPcsExecution.Context) (helperOrigin : CacheBackedSingleOpening.Origin helper)
    (helperRole : NativeBrakedownCalibration.Role) (compatible : SingleOpeningCalibration.Matches helper helperRole)
    (helperWidth : 3 ≤ helper.parameters.width.val)
    (source : I → NativeGoldBatchPcsProgram.Context) (sourceOrigin : (i : I) → CacheBackedCodeOrigin.Origin (source i))
    (sourceRadius : I → ℕ) (coins : Measure Tape) (scalarRadius : ℕ) :
    (coins.prod law) {execution | (∃ fuel, PrivateCoinScalarProbability.Event code publicData privateData dummy scalarRadius fuel execution) ∨
      PrivateCoinJointPcsLedger.Pcs HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin
        (NativeBrakedownCalibration.radius .goldilocks helperRole) sourceRadius execution} ≤
      (coins.prod law) {execution : Tape × World | (∃ fuel i, CacheBackedBatchLifetimeSoundness.Failure SourceMemory dummy (source i) (sourceOrigin i) (sourceRadius i)
        (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData execution.1 privateData fuel)) id OracleProgramMachine.step execution.2) ∧
        ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} +
      PrivateCoinByteWork.expectedWork coins code publicData privateData *
        (1/(2 : ENNReal)^159 + (PrivateCoinSharedHash.rate+ScalarEquationWork.rate) + OriginalHelperJointProbability.rate) := by
  have residual : (coins.prod law) {execution : Tape × World | (∃ fuel, OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin
      (NativeBrakedownCalibration.radius .goldilocks helperRole) sourceRadius
      (privateProgram code publicData execution.1 privateData fuel) OracleProgramMachine.step execution.2) ∧
      ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * OriginalHelperJointProbability.rate +
      (coins.prod law) {execution : Tape × World | (∃ fuel i, CacheBackedBatchLifetimeSoundness.Failure SourceMemory dummy (source i) (sourceOrigin i) (sourceRadius i)
        (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData execution.1 privateData fuel)) id OracleProgramMachine.step execution.2) ∧
        ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} := by
    have included : {execution : Tape × World | (∃ fuel, OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin
        (NativeBrakedownCalibration.radius .goldilocks helperRole) sourceRadius
        (privateProgram code publicData execution.1 privateData fuel) OracleProgramMachine.step execution.2) ∧
        ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} ⊆
        {execution : Tape × World | (∃ fuel, SingleOpeningLifetimeSoundness.Failure HelperMemory dummy helper (NativeBrakedownCalibration.radius .goldilocks helperRole)
          (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData execution.1 privateData fuel)) id OracleProgramMachine.step execution.2) ∧
          ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} ∪
        {execution : Tape × World | (∃ fuel i, CacheBackedBatchLifetimeSoundness.Failure SourceMemory dummy (source i) (sourceOrigin i) (sourceRadius i)
          (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData execution.1 privateData fuel)) id OracleProgramMachine.step execution.2) ∧
          ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} := by
      rintro execution ⟨⟨fuel,single | ⟨i,batch⟩⟩,safe⟩
      · exact Or.inl ⟨⟨fuel,single⟩,safe⟩
      · exact Or.inr ⟨⟨fuel,i,batch⟩,safe⟩
    exact (measure_mono included).trans ((measure_union_le _ _).trans (add_le_add
      (OriginalHelperJointProbability.original_bound HelperMemory coins code publicData privateData dummy helper helperOrigin helperRole compatible helperWidth) le_rfl))
  apply (CalibratedReferencePcsLedger.bound HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin
    (NativeBrakedownCalibration.radius .goldilocks helperRole) sourceRadius coins scalarRadius).trans
  apply (add_le_add residual le_rfl).trans
  exact le_of_eq (by simp only [mul_add]; ac_rfl)

end
end FormalProof4FHE.HasteBoots.CalibratedHelperSourceLedger
