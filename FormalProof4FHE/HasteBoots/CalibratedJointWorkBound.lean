module
public import FormalProof4FHE.HasteBoots.IndexedSourceJointProbability
@[expose] public section

/-! The original scalar/helper/indexed-source analysis event has no residual
probability term. Work is the specified interpreter work, not physical work;
public modified-PBS false acceptance still requires semantic refinement. -/
namespace FormalProof4FHE.HasteBoots.CalibratedJointWorkBound
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open NativeRootMessage (Digest)
noncomputable section

def rate : ENNReal := 1/(2 : ENNReal)^159 + (PrivateCoinSharedHash.rate+ScalarEquationWork.rate) +
  OriginalHelperJointProbability.rate + (IndexedSourceJointProbability.rate+1/(2 : ENNReal)^159)

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
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate := by
  apply (CalibratedHelperSourceLedger.bound HelperMemory SourceMemory code publicData privateData dummy helper helperOrigin helperRole compatible helperWidth
    source sourceOrigin (fun i => NativeBrakedownCalibration.radius .goldilocks (sourceRole i)) coins scalarRadius).trans
  apply (add_le_add (IndexedSourceJointProbability.root_safe_bound SourceMemory code publicData privateData dummy profile source sourceOrigin sourceRole
    coins sourceAdmitted profiles) le_rfl).trans
  exact le_of_eq (by simp only [rate,mul_add]; ac_rfl)

def finiteRate : NNReal := 1/2^159 + (1/2^159+4/(NativeFields.goldilocksModulus^3 : ℕ)) +
  (17/2^141+1/2^255) + ((17/2^141+17/2^141+1/2^255)+1/2^159)

theorem finite_rate_coe : (finiteRate : ENNReal) = rate := by
  simp only [finiteRate,rate,PrivateCoinSharedHash.rate,ScalarEquationWork.rate,OriginalHelperJointProbability.rate,
    IndexedSourceJointProbability.rate,AdaptiveBatchFieldKernel.rate,AdaptiveBatchColumnKernel.rate,
    ENNReal.coe_add,ENNReal.coe_div (by positivity : (2 : NNReal)^159 ≠ 0),
    ENNReal.coe_div (by positivity : (2 : NNReal)^141 ≠ 0),
    ENNReal.coe_div (by positivity : (2 : NNReal)^255 ≠ 0),
    ENNReal.coe_div (by norm_num [NativeFields.goldilocksModulus] : (NativeFields.goldilocksModulus^3 : NNReal) ≠ 0),
    ENNReal.coe_pow,ENNReal.coe_ofNat,ENNReal.coe_one,ENNReal.coe_natCast,Nat.cast_pow]

theorem rate_le_128 : rate ≤ 1/(2 : ENNReal)^128 := by
  have finite : finiteRate ≤ 1/(2 : NNReal)^128 := by
    rw [← NNReal.coe_le_coe]
    norm_num [finiteRate,NativeFields.goldilocksModulus]
  have cast := ENNReal.coe_le_coe.mpr finite
  rw [finite_rate_coe] at cast
  simpa only [ENNReal.coe_div (by positivity : (2 : NNReal)^128 ≠ 0),ENNReal.coe_pow,ENNReal.coe_ofNat,ENNReal.coe_one] using cast

theorem work_128 {I : Type} (HelperMemory SourceMemory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy profile : Digest)
    (helper : NativeGoldPcsExecution.Context) (helperOrigin : CacheBackedSingleOpening.Origin helper)
    (helperRole : NativeBrakedownCalibration.Role) (compatible : SingleOpeningCalibration.Matches helper helperRole)
    (helperWidth : 3 ≤ helper.parameters.width.val)
    (source : I → NativeGoldBatchPcsProgram.Context) (sourceOrigin : (i : I) → CacheBackedCodeOrigin.Origin (source i))
    (sourceRole : I → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ i, NativeGoldBatchCalibration.Matches (source i) (sourceRole i))
    (profiles : ∀ i, (source i).parent.profile = profile) (coins : Measure Tape) (scalarRadius : ℕ) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | (∃ fuel, PrivateCoinScalarProbability.Event code publicData privateData dummy scalarRadius fuel execution) ∨
      PrivateCoinJointPcsLedger.Pcs HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin
        (NativeBrakedownCalibration.radius .goldilocks helperRole)
        (fun i => NativeBrakedownCalibration.radius .goldilocks (sourceRole i)) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  calc
    _ ≤ (2 : ENNReal)^128 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * rate) :=
      mul_le_mul' le_rfl (bound HelperMemory SourceMemory code publicData privateData dummy profile helper helperOrigin helperRole compatible helperWidth
        source sourceOrigin sourceRole sourceAdmitted profiles coins scalarRadius)
    _ ≤ (2 : ENNReal)^128 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * (1/(2 : ENNReal)^128)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl rate_le_128)
    _ = PrivateCoinByteWork.expectedWork coins code publicData privateData * ((2 : ENNReal)^128*(1/(2 : ENNReal)^128)) := by ac_rfl
    _ = _ := by rw [one_div,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]

end
end FormalProof4FHE.HasteBoots.CalibratedJointWorkBound
