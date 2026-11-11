module
public import FormalProof4FHE.HasteBoots.PrivateCoinSeedOrderProbability
@[expose] public section

/-! Originally false native identities need no seed-order safety premise.
Prior/pending ordering exceptions are paid by their original joint work
ledger. Native framing/domains and actual attacker-work refinement remain. -/
namespace FormalProof4FHE.HasteBoots.SeedOrderIdentityWork
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open OracleProgram (Program)
open AllocatedFamilyFunctions (Allocation)
open InterpreterScalarLifetime (privateProgram)
open PrivateCoinByteMachine (Instruction)
open PrivateCoinReplay (Tape)
open MeasureTheory
noncomputable section

def rate : ENNReal := CanonicalJointWorkBound.rate+1/(2 : ENNReal)^159

structure Witness {Memory A : Type} (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
    (program : Program A) (dummy : Digest) (world : World) where
  data : CanonicalAllocatedJob.Job (Memory := Memory) ctx allocation program world
  rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit
  frames : List TranscriptFrame.Frame
  decoded : TranscriptFrame.decodeAll data.origin.ready.equality.transcript.input = some frames
  statementFits : (NativeScalarBatchWire.statementCodec.encode data.origin.ready.statement).length < TranscriptFrame.lengthLimit
  domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra
  framing : AllocatedLookupReadStability.Framing ctx world
  before : List TranscriptFrame.Frame
  bytes : ctx.parent.input = TranscriptFrame.encodeMany before
  valid : ∀ frame ∈ before, TranscriptFrame.Valid frame
  parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests
  initial : ScalarChainHealing.value (2*data.index.val+1) data.origin.ready.statement.claims.val ≠
    some (CanonicalAllocatedIdentity.truth data dummy)


def ordered {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx}
    {program : Program A} {dummy : Digest} {world : World} (witness : Witness (Memory := Memory) ctx allocation program dummy world)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    CanonicalIdentityWork.Witness (Memory := Memory) ctx allocation program dummy world :=
  ⟨witness.data,witness.rootsFit,witness.frames,witness.decoded,witness.statementFits,witness.domain,witness.framing,safe,
    witness.before,witness.bytes,witness.valid,witness.parentDomain,witness.initial⟩

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

def Failure (execution : Tape × World) : Prop :=
  ∃ fuel, Nonempty (Witness (Memory := Memory) ctx allocation (privateProgram code publicData execution.1 privateData fuel) dummy execution.2)


theorem covered (execution : Tape × World) (failed : Failure Memory ctx allocation code publicData privateData dummy execution) :
    (∃ fuel, PrivateCoinSeedOrderProbability.Bad code publicData privateData fuel execution) ∨
      CanonicalIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution := by
  obtain ⟨fuel,⟨witness⟩⟩ := failed
  by_cases bad : SeedQuoteOrder.Bad OracleProgramMachine.step (privateProgram code publicData execution.1 privateData fuel) execution.2
  · exact Or.inl ⟨fuel,bad⟩
  · exact Or.inr ⟨fuel,⟨ordered witness bad⟩⟩

theorem ordered_bound (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (coins.prod law) {execution | CanonicalIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * CanonicalJointWorkBound.rate := by
  let helperOrigin := AllocatedOpeningLifetimeBound.helperOrigin ctx allocation.entries allocation.reachable allocation.helperHandle allocation.references
    allocation.template allocation.assembled target parameters
  let sourceOrigin := RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
    (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1
  have width : 3 ≤ target.parameters.width.val := by
    rw [helperAdmitted.width]
    cases helperRole <;> decide +kernel
  have included : {execution | CanonicalIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | (∃ fuel, PrivateCoinCanonicalScalarProbability.Event code publicData privateData dummy fuel execution) ∨
        PrivateCoinJointPcsLedger.Pcs Memory Memory code publicData privateData dummy target (RegistryPublicSource.context ctx) sourceOrigin
          (NativeBrakedownCalibration.radius .goldilocks helperRole)
          (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) execution} := by
    intro execution failed
    exact CanonicalIdentityWork.covered Memory ctx allocation code publicData privateData dummy target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted execution failed
  exact (measure_mono included).trans
    (CanonicalJointWorkBound.bound Memory Memory code publicData privateData dummy ctx.parent.profile target helperOrigin helperRole helperAdmitted width
      (RegistryPublicSource.context ctx) sourceOrigin sourceRole sourceAdmitted (IndexedSourceFieldReduction.registry_profiles ctx) coins)


theorem bound (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData * rate := by
  have included : {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | ∃ fuel, PrivateCoinSeedOrderProbability.Bad code publicData privateData fuel execution} ∪
      {execution | CanonicalIdentityWork.Failure Memory ctx allocation code publicData privateData dummy execution} := by
    intro execution failed
    exact covered Memory ctx allocation code publicData privateData dummy execution failed
  apply (measure_mono included).trans ((measure_union_le _ _).trans ?_)
  apply (add_le_add (PrivateCoinSeedOrderProbability.lifetime_le_159 coins code publicData privateData)
    (ordered_bound Memory ctx allocation code publicData privateData dummy target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted coins)).trans
  exact le_of_eq (by rw [rate,mul_add,add_comm])

theorem rate_le_128 : rate ≤ 1/(2 : ENNReal)^128 := by
  have finite : CalibratedJointWorkBound.finiteRate+1/(2 : NNReal)^159 ≤ 1/(2 : NNReal)^128 := by
    rw [← NNReal.coe_le_coe]
    norm_num [CalibratedJointWorkBound.finiteRate,NativeFields.goldilocksModulus]
  have cast := ENNReal.coe_le_coe.mpr finite
  simpa only [rate,CanonicalJointWorkBound.rate,ENNReal.coe_add,CalibratedJointWorkBound.finite_rate_coe,
    ENNReal.coe_div (by positivity : (2 : NNReal)^159 ≠ 0),
    ENNReal.coe_div (by positivity : (2 : NNReal)^128 ≠ 0),ENNReal.coe_pow,ENNReal.coe_ofNat,ENNReal.coe_one] using cast

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | Failure Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  calc
    _ ≤ (2 : ENNReal)^128 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * rate) :=
      mul_le_mul' le_rfl (bound Memory ctx allocation code publicData privateData dummy target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted coins)
    _ ≤ (2 : ENNReal)^128 * (PrivateCoinByteWork.expectedWork coins code publicData privateData * (1/(2 : ENNReal)^128)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl rate_le_128)
    _ = PrivateCoinByteWork.expectedWork coins code publicData privateData * ((2 : ENNReal)^128*(1/(2 : ENNReal)^128)) := by ac_rfl
    _ = _ := by rw [one_div,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]

end
end FormalProof4FHE.HasteBoots.SeedOrderIdentityWork
