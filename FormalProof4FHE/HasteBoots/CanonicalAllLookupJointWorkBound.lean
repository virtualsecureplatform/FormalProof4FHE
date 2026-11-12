module
public import FormalProof4FHE.HasteBoots.CanonicalAllLookupJointPcsLedger
public import FormalProof4FHE.HasteBoots.CanonicalLookupJointWorkBound
@[expose] public section

/-! The enlarged original full lookup/PCS/reference event retains the 128-bit
specified-work bound. Compression and reciprocal charges are added to the exact finite rate,
while original hash/reference and PCS charges remain shared. -/
namespace FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound
open MeasureTheory
open InputIndexedOracle (Input World law)
open PrivateCoinReplay (Tape)
open PrivateCoinByteMachine (Instruction)
open InterpreterScalarLifetime (privateProgram)
open NativeRootMessage (Digest)
noncomputable section

def rate : ENNReal := CanonicalLookupJointWorkBound.rate + LookupStreamWorkRate.rate + LookupStreamWorkRate.rate

def finiteRate : NNReal := CanonicalLookupJointWorkBound.finiteRate + 1/2^132 + 1/2^132

theorem finite_rate_coe : (finiteRate : ENNReal) = rate := by
  rw [finiteRate,ENNReal.coe_add,ENNReal.coe_add,CanonicalLookupJointWorkBound.finite_rate_coe]
  norm_num [rate,LookupStreamWorkRate.rate]

theorem rate_le_128 : rate ≤ 1/(2 : ENNReal)^128 := by
  have finite : finiteRate ≤ 1/(2 : NNReal)^128 := by
    rw [← NNReal.coe_le_coe]
    norm_num [finiteRate,CanonicalLookupJointWorkBound.finiteRate,CanonicalPairedJointWorkBound.finiteRate,CalibratedJointWorkBound.finiteRate,NativeFields.goldilocksModulus]
  have cast := ENNReal.coe_le_coe.mpr finite
  rw [finite_rate_coe] at cast
  simpa only [ENNReal.coe_div (by positivity : (2 : NNReal)^128 ≠ 0),ENNReal.coe_pow,ENNReal.coe_ofNat,ENNReal.coe_one] using cast

theorem bound {I : Type} (HelperMemory SourceMemory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy profile : Digest)
    (helper : NativeGoldPcsExecution.Context) (helperOrigin : CacheBackedSingleOpening.Origin helper)
    (helperRole : NativeBrakedownCalibration.Role) (compatible : SingleOpeningCalibration.Matches helper helperRole)
    (helperWidth : 3 ≤ helper.parameters.width.val)
    (source : I → NativeGoldBatchPcsProgram.Context) (sourceOrigin : (i : I) → CacheBackedCodeOrigin.Origin (source i))
    (sourceRole : I → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ i, NativeGoldBatchCalibration.Matches (source i) (sourceRole i))
    (profiles : ∀ i, (source i).parent.profile = profile) (coins : Measure Tape) :
    (coins.prod law) {execution | (∃ fuel, PrivateCoinAllLookupChallengeProbability.Event code publicData privateData dummy fuel execution) ∨
      (∃ fuel, GlobalReferenceBad.Bad (privateProgram code publicData execution.1 privateData fuel) dummy execution.2) ∨
      PrivateCoinJointPcsLedger.Pcs HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin
        (NativeBrakedownCalibration.radius .goldilocks helperRole)
        (fun i => NativeBrakedownCalibration.radius .goldilocks (sourceRole i)) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate := by
  have residual : (coins.prod law) {execution : Tape × World | (∃ fuel, OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin
      (NativeBrakedownCalibration.radius .goldilocks helperRole) (fun i => NativeBrakedownCalibration.radius .goldilocks (sourceRole i))
      (privateProgram code publicData execution.1 privateData fuel) OracleProgramMachine.step execution.2) ∧
      ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData *
        (OriginalHelperJointProbability.rate+(IndexedSourceJointProbability.rate+1/(2 : ENNReal)^159)) := by
    have included : {execution : Tape × World | (∃ fuel, OpeningLifetimeFamily.Failure HelperMemory SourceMemory dummy helper source sourceOrigin
        (NativeBrakedownCalibration.radius .goldilocks helperRole) (fun i => NativeBrakedownCalibration.radius .goldilocks (sourceRole i))
        (privateProgram code publicData execution.1 privateData fuel) OracleProgramMachine.step execution.2) ∧
        ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} ⊆
        {execution : Tape × World | (∃ fuel, SingleOpeningLifetimeSoundness.Failure HelperMemory dummy helper (NativeBrakedownCalibration.radius .goldilocks helperRole)
          (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData execution.1 privateData fuel)) id OracleProgramMachine.step execution.2) ∧
          ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} ∪
        {execution : Tape × World | (∃ fuel i, CacheBackedBatchLifetimeSoundness.Failure SourceMemory dummy (source i) (sourceOrigin i) ((fun i => NativeBrakedownCalibration.radius .goldilocks (sourceRole i)) i)
          (SingleOpeningLifetimeSoundness.clean (privateProgram code publicData execution.1 privateData fuel)) id OracleProgramMachine.step execution.2) ∧
          ¬∃ fuel, PrivateCoinSharedHash.Root code publicData privateData dummy fuel execution} := by
      rintro execution ⟨⟨fuel,single | ⟨i,batch⟩⟩,safe⟩
      · exact Or.inl ⟨⟨fuel,single⟩,safe⟩
      · exact Or.inr ⟨⟨fuel,i,batch⟩,safe⟩
    have bounded := (measure_mono included).trans ((measure_union_le _ _).trans (add_le_add
      (OriginalHelperJointProbability.original_bound HelperMemory coins code publicData privateData dummy helper helperOrigin helperRole compatible helperWidth) (IndexedSourceJointProbability.root_safe_bound SourceMemory code publicData privateData dummy profile source sourceOrigin sourceRole coins sourceAdmitted profiles)))
    exact bounded.trans (le_of_eq (mul_add _ _ _).symm)
  apply (CanonicalAllLookupJointPcsLedger.bound HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin
    (NativeBrakedownCalibration.radius .goldilocks helperRole)
    (fun i => NativeBrakedownCalibration.radius .goldilocks (sourceRole i)) coins).trans
  apply (add_le_add (add_le_add (PrivateCoinReferenceProbability.lifetime_le_159 coins code publicData privateData) residual) le_rfl).trans
  exact le_of_eq (by simp only [rate,CanonicalLookupJointWorkBound.rate,CanonicalPairedJointWorkBound.rate,CalibratedJointWorkBound.rate,
    PrivateCoinAllLookupChallengeProbability.rate,PrivateCoinLookupChallengeProbability.rate,PrivateCoinLookupArithmeticProbability.scalarRate,PrivateCoinPairedScalarProbability.scalarRate,mul_add]; ac_rfl)

theorem work_128 {I : Type} (HelperMemory SourceMemory : Type) (code : List Instruction) (publicData : Input)
    (privateData : ClosedByteMachine.Tape → Input) (dummy profile : Digest)
    (helper : NativeGoldPcsExecution.Context) (helperOrigin : CacheBackedSingleOpening.Origin helper)
    (helperRole : NativeBrakedownCalibration.Role) (compatible : SingleOpeningCalibration.Matches helper helperRole)
    (helperWidth : 3 ≤ helper.parameters.width.val)
    (source : I → NativeGoldBatchPcsProgram.Context) (sourceOrigin : (i : I) → CacheBackedCodeOrigin.Origin (source i))
    (sourceRole : I → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ i, NativeGoldBatchCalibration.Matches (source i) (sourceRole i))
    (profiles : ∀ i, (source i).parent.profile = profile) (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | (∃ fuel, PrivateCoinAllLookupChallengeProbability.Event code publicData privateData dummy fuel execution) ∨
      (∃ fuel, GlobalReferenceBad.Bad (privateProgram code publicData execution.1 privateData fuel) dummy execution.2) ∨
      PrivateCoinJointPcsLedger.Pcs HelperMemory SourceMemory code publicData privateData dummy helper source sourceOrigin
        (NativeBrakedownCalibration.radius .goldilocks helperRole)
        (fun i => NativeBrakedownCalibration.radius .goldilocks (sourceRole i)) execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  calc
    _ ≤ (2 : ENNReal)^128 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * rate) :=
      mul_le_mul' le_rfl (bound HelperMemory SourceMemory code publicData privateData dummy profile helper helperOrigin helperRole compatible helperWidth
        source sourceOrigin sourceRole sourceAdmitted profiles coins)
    _ ≤ (2 : ENNReal)^128 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * (1/(2 : ENNReal)^128)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl rate_le_128)
    _ = PrivateCoinByteWork.expectedWork coins code publicData privateData * ((2 : ENNReal)^128*(1/(2 : ENNReal)^128)) := by ac_rfl
    _ = _ := by rw [one_div,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]

end
end FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound
