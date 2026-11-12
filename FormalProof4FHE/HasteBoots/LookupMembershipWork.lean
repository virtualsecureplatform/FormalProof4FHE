module
public import FormalProof4FHE.HasteBoots.CallerLookupWorkCoverage
public import FormalProof4FHE.HasteBoots.LookupInitialWork
public import FormalProof4FHE.HasteBoots.CanonicalAllLookupJointWorkBound
@[expose] public section

/-! Full original tuple nonmembership for a fixed caller context/allocation
satisfies the 128-bit specified-interpreter-work bound under the original
helper/source calibration premises. Whole PBS enforcement and dynamic caller
scope, actor separation and physical cost refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.LookupMembershipWork
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open AllocatedFamilyFunctions (Allocation)
open PrivateCoinByteMachine (Instruction)
open PrivateCoinReplay (Tape)
open InterpreterScalarLifetime (privateProgram)
open MeasureTheory
noncomputable section

structure Witness {Memory A : Type} (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
    (program : OracleProgram.Program A) (dummy : Digest) (world : World) where
  data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world
  policy : NativeSharedLookupValues.Policy
  original : Vector NativeLookupRequestWire.Request
  template : Context (Vector Opening)
  result : NativeGoldLookupVerification.Outcome Memory
  executed : (OracleProgram.run (RebuiltLookupExecution.program policy original allocation.entries allocation.helperHandle allocation.references template
    data.chooseHelper data.chooseBatch data.memory) world).run.1 = .allocated (.verification ctx result)
  inputs : SequencedCallerInputs.Inputs data
  before : List TranscriptFrame.Frame
  bytes : ctx.parent.input = TranscriptFrame.encodeMany before
  valid : ∀ frame ∈ before, TranscriptFrame.Valid frame
  bad : RebuiltCallerLookupCoverage.Nonmember data dummy

def Failure (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
    (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest) (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)

def rate : ENNReal := CanonicalAllLookupJointWorkBound.rate+1/(2 : ENNReal)^159

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
    (failed : Failure Memory ctx allocation code publicData privateData dummy execution) :
    (∃ fuel, PrivateCoinSeedOrderProbability.Bad code publicData privateData fuel execution) ∨
      ((∃ fuel, PrivateCoinAllLookupChallengeProbability.Event code publicData privateData dummy fuel execution) ∨
        (∃ fuel, GlobalReferenceBad.Bad (InterpreterScalarLifetime.privateProgram code publicData execution.1 privateData fuel) dummy execution.2) ∨
        PrivateCoinJointPcsLedger.Pcs Memory Memory code publicData privateData dummy target (RegistryPublicSource.context ctx)
          (RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
            (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1)
          (NativeBrakedownCalibration.radius .goldilocks helperRole)
          (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) execution) := by
  obtain ⟨fuel,⟨witness⟩⟩ := failed
  rcases CallerLookupWorkCoverage.nonmember witness.data witness.policy witness.original witness.template witness.result witness.executed
      witness.inputs helperWidth sourceWidths witness.before witness.bytes witness.valid dummy witness.bad with
    arithmetic | seed | reference | compression | reciprocal
  · rcases LookupInitialWork.covered Memory ctx allocation code publicData privateData dummy target parameters profile helperRole helperAdmitted
        sourceRole sourceAdmitted helperWidth sourceWidths execution ⟨fuel,arithmetic⟩ with seed | ⟨horizon,arithmetic⟩ | pcs
    · exact Or.inl seed
    · exact Or.inr (Or.inl ⟨horizon,Or.inl (Or.inl arithmetic)⟩)
    · exact Or.inr (Or.inr (Or.inr pcs))
  · exact Or.inl ⟨fuel,seed⟩
  · exact Or.inr (Or.inr (Or.inl ⟨fuel,reference⟩))
  · exact Or.inr (Or.inl ⟨fuel,Or.inr compression⟩)
  · exact Or.inr (Or.inl ⟨fuel,Or.inl (Or.inr reciprocal)⟩)

theorem bound (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
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
  have included : {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | ∃ fuel, PrivateCoinSeedOrderProbability.Bad code publicData privateData fuel execution} ∪
      {execution | (∃ fuel, PrivateCoinAllLookupChallengeProbability.Event code publicData privateData dummy fuel execution) ∨
        (∃ fuel, GlobalReferenceBad.Bad (InterpreterScalarLifetime.privateProgram code publicData execution.1 privateData fuel) dummy execution.2) ∨
        PrivateCoinJointPcsLedger.Pcs Memory Memory code publicData privateData dummy target (RegistryPublicSource.context ctx) sourceOrigin
          (NativeBrakedownCalibration.radius .goldilocks helperRole)
          (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) execution} := by
    intro execution failed
    exact covered Memory ctx allocation code publicData privateData dummy target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted
      helperWidth sourceWidths execution failed
  apply (measure_mono included).trans ((measure_union_le _ _).trans ?_)
  apply (add_le_add (PrivateCoinSeedOrderProbability.lifetime_le_159 coins code publicData privateData)
    (CanonicalAllLookupJointWorkBound.bound Memory Memory code publicData privateData dummy ctx.parent.profile target helperOrigin helperRole helperAdmitted width
      (RegistryPublicSource.context ctx) sourceOrigin sourceRole sourceAdmitted (IndexedSourceFieldReduction.registry_profiles ctx) coins)).trans
  exact le_of_eq (by rw [rate,mul_add,add_comm])

theorem rate_le_128 : rate ≤ 1/(2 : ENNReal)^128 := by
  have finite : CanonicalAllLookupJointWorkBound.finiteRate+1/(2 : NNReal)^159 ≤ 1/(2 : NNReal)^128 := by
    rw [← NNReal.coe_le_coe]
    norm_num [CanonicalAllLookupJointWorkBound.finiteRate,CanonicalLookupJointWorkBound.finiteRate,CanonicalPairedJointWorkBound.finiteRate,
      CalibratedJointWorkBound.finiteRate,NativeFields.goldilocksModulus]
  have cast := ENNReal.coe_le_coe.mpr finite
  rw [ENNReal.coe_add,CanonicalAllLookupJointWorkBound.finite_rate_coe] at cast
  simpa only [rate,ENNReal.coe_div (by positivity : (2 : NNReal)^159 ≠ 0),
    ENNReal.coe_div (by positivity : (2 : NNReal)^128 ≠ 0),ENNReal.coe_pow,ENNReal.coe_ofNat,ENNReal.coe_one] using cast

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law)
        {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  calc
    _ ≤ (2 : ENNReal)^128 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * rate) :=
      mul_le_mul' le_rfl (bound Memory ctx allocation code publicData privateData dummy target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted coins)
    _ ≤ (2 : ENNReal)^128 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * (1/(2 : ENNReal)^128)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl rate_le_128)
    _ = PrivateCoinByteWork.expectedWork coins code publicData privateData * ((2 : ENNReal)^128*(1/(2 : ENNReal)^128)) := by ac_rfl
    _ = _ := by rw [one_div,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]

end
end FormalProof4FHE.HasteBoots.LookupMembershipWork
