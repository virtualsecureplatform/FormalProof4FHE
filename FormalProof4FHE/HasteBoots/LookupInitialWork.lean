module
public import FormalProof4FHE.HasteBoots.CallerEqualityRecovery
public import FormalProof4FHE.HasteBoots.LookupInitialPairedWork
public import FormalProof4FHE.HasteBoots.CanonicalLookupJointWorkBound
@[expose] public section

/-! Original native arithmetic violations have no unpriced equality-miss
remainder. Actual caller EQ misses enter the attained adaptive event; paired
scalar/PCS/hash charges and the seed-order exception are each retained once.
Work remains the specified private byte interpreter's lifetime counter. -/
namespace FormalProof4FHE.HasteBoots.LookupInitialWork
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open AllocatedFamilyFunctions (Allocation)
open PrivateCoinByteMachine (Instruction)
open PrivateCoinReplay (Tape)
open MeasureTheory
noncomputable section

def rate : ENNReal := CanonicalLookupJointWorkBound.rate+1/(2 : ENNReal)^159

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

theorem covered (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (execution : Tape × World)
    (failed : LookupInitialPairedWork.Failure Memory ctx allocation code publicData privateData dummy execution) :
    (∃ fuel, PrivateCoinSeedOrderProbability.Bad code publicData privateData fuel execution) ∨
      ((∃ fuel, PrivateCoinLookupArithmeticProbability.Event code publicData privateData dummy fuel execution) ∨
        PrivateCoinJointPcsLedger.Pcs Memory Memory code publicData privateData dummy target (RegistryPublicSource.context ctx)
          (RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
            (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1)
          (NativeBrakedownCalibration.radius .goldilocks helperRole)
          (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) execution) := by
  obtain ⟨fuel,⟨witness⟩⟩ := failed
  by_cases safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step
      (InterpreterScalarLifetime.privateProgram code publicData execution.1 privateData fuel) execution.2
  · right
    rcases LookupInitialPairedWork.covered witness with paired | missed
    · obtain ⟨paired⟩ := paired
      let ordered := SeedOrderPairedWork.ordered (SequencedInputPairedWork.toSeedOrder paired helperWidth sourceWidths) safe
      rcases CanonicalPairedIdentityWork.covered Memory ctx allocation code publicData privateData dummy
        target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted execution ⟨fuel,⟨ordered⟩⟩ with scalar | pcs
      · obtain ⟨horizon,occurred⟩ := scalar
        exact Or.inl ⟨horizon,Or.inl occurred⟩
      · exact Or.inr pcs
    · exact Or.inl ⟨fuel,Or.inr (CallerEqualityRecovery.covered witness.data witness.inputs helperWidth sourceWidths
        witness.before witness.bytes witness.valid dummy safe missed)⟩
  · exact Or.inl ⟨fuel,not_not.mp safe⟩

theorem bound (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (coins.prod law) {execution | LookupInitialPairedWork.Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate := by
  have helperWidth : ctx.helper.width.val ≤ 4 := by
    rw [parameters,helperAdmitted.width]
    cases helperRole <;> decide +kernel
  have sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4 := by
    intro slot
    have compatible := (sourceAdmitted slot).width
    change (ctx.registry.val.get slot).parameters.width.val = NativeBrakedownCalibration.testWidth .goldilocks (sourceRole slot) at compatible
    rw [compatible]
    cases sourceRole slot <;> decide +kernel
  let helperOrigin := AllocatedOpeningLifetimeBound.helperOrigin ctx allocation.entries allocation.reachable allocation.helperHandle allocation.references
    allocation.template allocation.assembled target parameters
  let sourceOrigin := RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
    (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1
  have width : 3 ≤ target.parameters.width.val := by
    rw [helperAdmitted.width]
    cases helperRole <;> decide +kernel
  have included : {execution | LookupInitialPairedWork.Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | ∃ fuel, PrivateCoinSeedOrderProbability.Bad code publicData privateData fuel execution} ∪
      {execution | (∃ fuel, PrivateCoinLookupArithmeticProbability.Event code publicData privateData dummy fuel execution) ∨
        PrivateCoinJointPcsLedger.Pcs Memory Memory code publicData privateData dummy target (RegistryPublicSource.context ctx) sourceOrigin
          (NativeBrakedownCalibration.radius .goldilocks helperRole)
          (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) execution} := by
    intro execution failed
    exact covered Memory ctx allocation code publicData privateData dummy target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted
      helperWidth sourceWidths execution failed
  apply (measure_mono included).trans ((measure_union_le _ _).trans ?_)
  apply (add_le_add (PrivateCoinSeedOrderProbability.lifetime_le_159 coins code publicData privateData)
    (CanonicalLookupJointWorkBound.bound Memory Memory code publicData privateData dummy ctx.parent.profile target helperOrigin helperRole helperAdmitted width
      (RegistryPublicSource.context ctx) sourceOrigin sourceRole sourceAdmitted (IndexedSourceFieldReduction.registry_profiles ctx) coins)).trans
  exact le_of_eq (by rw [rate,mul_add,add_comm])

theorem rate_le_128 : rate ≤ 1/(2 : ENNReal)^128 := by
  have finite : CanonicalLookupJointWorkBound.finiteRate+1/(2 : NNReal)^159 ≤ 1/(2 : NNReal)^128 := by
    rw [← NNReal.coe_le_coe]
    norm_num [CanonicalLookupJointWorkBound.finiteRate,CanonicalPairedJointWorkBound.finiteRate,
      CalibratedJointWorkBound.finiteRate,NativeFields.goldilocksModulus]
  have cast := ENNReal.coe_le_coe.mpr finite
  rw [ENNReal.coe_add,CanonicalLookupJointWorkBound.finite_rate_coe] at cast
  simpa only [rate,ENNReal.coe_div (by positivity : (2 : NNReal)^159 ≠ 0),
    ENNReal.coe_div (by positivity : (2 : NNReal)^128 ≠ 0),ENNReal.coe_pow,ENNReal.coe_ofNat,ENNReal.coe_one] using cast

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law)
        {execution | LookupInitialPairedWork.Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  calc
    _ ≤ (2 : ENNReal)^128 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * rate) :=
      mul_le_mul' le_rfl (bound Memory ctx allocation code publicData privateData dummy target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted coins)
    _ ≤ (2 : ENNReal)^128 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * (1/(2 : ENNReal)^128)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl rate_le_128)
    _ = PrivateCoinByteWork.expectedWork coins code publicData privateData * ((2 : ENNReal)^128*(1/(2 : ENNReal)^128)) := by ac_rfl
    _ = _ := by rw [one_div,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]

end
end FormalProof4FHE.HasteBoots.LookupInitialWork
