module
public import FormalProof4FHE.HasteBoots.IndexedSourceFieldReduction
public import FormalProof4FHE.HasteBoots.CalibratedHelperSourceLedger
@[expose] public section

/-! Substitute adaptive indexed-source field coverage into the existing
helper/scalar/shared-hash ledger. Receipt and column probabilities remain. -/
namespace FormalProof4FHE.HasteBoots.CalibratedAdaptiveSourceLedger
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open NativeRootMessage (Digest)
noncomputable section

theorem bound {I : Type} (HelperMemory SourceMemory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy profile : Digest)
    (helper : NativeGoldPcsExecution.Context) (helperOrigin : CacheBackedSingleOpening.Origin helper)
    (helperRole : NativeBrakedownCalibration.Role) (compatible : SingleOpeningCalibration.Matches helper helperRole)
    (helperWidth : 3 ≤ helper.parameters.width.val)
    (source : I → NativeGoldBatchPcsProgram.Context) (sourceOrigin : (i : I) → CacheBackedCodeOrigin.Origin (source i))
    (sourceRole : I → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ i, NativeGoldBatchCalibration.Matches (source i) (sourceRole i))
    (profiles : ∀ i, (source i).parent.profile = profile) (coins : Measure Tape) (scalarRadius : ℕ) :
    (coins.prod law) {execution | (∃ fuel, PrivateCoinScalarProbability.Event code publicData privateData dummy scalarRadius fuel execution) ∨
      PrivateCoinJointPcsLedger.Pcs HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin
        (NativeBrakedownCalibration.radius .goldilocks helperRole)
        (fun i => NativeBrakedownCalibration.radius .goldilocks (sourceRole i)) execution} ≤
      (coins.prod law) {execution | IndexedSourceFieldReduction.Remaining code publicData privateData dummy profile source sourceOrigin sourceRole execution} +
      PrivateCoinByteWork.expectedWork coins code publicData privateData *
        (1/(2 : ENNReal)^159 + (PrivateCoinSharedHash.rate+ScalarEquationWork.rate) + OriginalHelperJointProbability.rate +
          (AdaptiveBatchFieldKernel.rate+1/(2 : ENNReal)^159)) := by
  apply (CalibratedHelperSourceLedger.bound HelperMemory SourceMemory code publicData privateData dummy helper helperOrigin helperRole compatible helperWidth
    source sourceOrigin (fun i => NativeBrakedownCalibration.radius .goldilocks (sourceRole i)) coins scalarRadius).trans
  apply (add_le_add (IndexedSourceFieldReduction.root_safe_bound SourceMemory code publicData privateData dummy profile source sourceOrigin sourceRole
    coins sourceAdmitted profiles) le_rfl).trans
  exact le_of_eq (by simp only [mul_add]; ac_rfl)

end
end FormalProof4FHE.HasteBoots.CalibratedAdaptiveSourceLedger
