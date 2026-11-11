module
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedIdentity
@[expose] public section

/-! Actual allocated native wrong-fold jobs inherit the proved joint
specified-work bound, with independently calibrated source/helper radii.
This event is not yet public modified-PBS false acceptance. -/
namespace FormalProof4FHE.HasteBoots.CanonicalAllocatedJobWork
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (Input World law)
open NativeRootMessage (Digest)
open AllocatedFamilyFunctions (Allocation)
open InterpreterScalarLifetime (privateProgram)
open PrivateCoinByteMachine (Instruction)
open PrivateCoinReplay (Tape)
open MeasureTheory
noncomputable section

variable (Memory : Type) (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
  (code : List Instruction) (publicData : Input) (privateData : ClosedByteMachine.Tape → Input) (dummy : Digest)

def WrongLifetime (execution : Tape × World) : Prop :=
  ∃ fuel, ∃ data : CanonicalAllocatedJob.Job (Memory := Memory) ctx allocation
    (privateProgram code publicData execution.1 privateData fuel) execution.2, CanonicalAllocatedJob.Wrong data dummy

theorem covered (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (execution : Tape × World) (wrong : WrongLifetime Memory ctx allocation code publicData privateData dummy execution) :
    PrivateCoinJointPcsLedger.Pcs Memory Memory code publicData privateData dummy target (RegistryPublicSource.context ctx)
      (RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
        (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1)
      (NativeBrakedownCalibration.radius .goldilocks helperRole)
      (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) execution := by
  obtain ⟨fuel,data,wrong⟩ := wrong
  exact ⟨fuel,CanonicalAllocatedJob.wrong_covered data dummy target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted wrong⟩

theorem work_128 (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (coins : Measure Tape) :
    (2 : ENNReal)^128 * (coins.prod law) {execution | WrongLifetime Memory ctx allocation code publicData privateData dummy execution} ≤
      PrivateCoinByteWork.expectedWork coins code publicData privateData := by
  let helperOrigin := AllocatedOpeningLifetimeBound.helperOrigin ctx allocation.entries allocation.reachable allocation.helperHandle allocation.references
    allocation.template allocation.assembled target parameters
  let sourceOrigin := RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
    (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1
  have width : 3 ≤ target.parameters.width.val := by
    rw [helperAdmitted.width]
    cases helperRole <;> decide +kernel
  have included : {execution | WrongLifetime Memory ctx allocation code publicData privateData dummy execution} ⊆
      {execution | (∃ fuel, PrivateCoinScalarProbability.Event code publicData privateData dummy 0 fuel execution) ∨
        PrivateCoinJointPcsLedger.Pcs Memory Memory code publicData privateData dummy target (RegistryPublicSource.context ctx) sourceOrigin
          (NativeBrakedownCalibration.radius .goldilocks helperRole)
          (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) execution} := by
    intro execution wrong
    exact Or.inr (covered Memory ctx allocation code publicData privateData dummy target parameters profile helperRole helperAdmitted sourceRole sourceAdmitted execution wrong)
  exact (mul_le_mul' le_rfl (measure_mono included)).trans
    (CalibratedJointWorkBound.work_128 Memory Memory code publicData privateData dummy ctx.parent.profile target helperOrigin helperRole helperAdmitted width
      (RegistryPublicSource.context ctx) sourceOrigin sourceRole sourceAdmitted (IndexedSourceFieldReduction.registry_profiles ctx) coins 0)

end
end FormalProof4FHE.HasteBoots.CanonicalAllocatedJobWork
