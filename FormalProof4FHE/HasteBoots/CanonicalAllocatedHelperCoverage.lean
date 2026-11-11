module
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedOpeningCoverage
@[expose] public section

/-! A wrong helper fold is decoded at the helper's own retained-parameter
radius and enters the original single-opening lifetime at its calibrated role. -/
namespace FormalProof4FHE.HasteBoots.CanonicalAllocatedHelperCoverage
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeFieldWire (goldExtensionValue)
open NativeExtensionFields (goldilocksBasis)
open OracleProgram (Program run)
open AllocatedFamilyFunctions (Allocation)
noncomputable section

theorem helper {Memory A : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (after : NativeDeferredBatchVerification.Progress Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index) (allocation : Allocation ctx)
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (program : Program A)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (role : NativeBrakedownCalibration.Role)
    (admitted : SingleOpeningCalibration.Matches target role)
    (observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist (run program world).run.2)
    (framing : ∀ receipt ∈ lookup.helpers.receipts,
      SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call))
    (responseFits : ∀ receipt ∈ lookup.helpers.receipts, (SingleOpeningColumnLaw.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)
    (wrong : NativeHelperPacking.coefficients goldilocksBasis (3+AllocatedLookupTables.helperPadding (ctx := ctx))
        (goldExtensionValue job.view.checked.helper) ≠
      (ExtensionQuery.coefficientsQuery goldilocksBasis (fun j => goldExtensionValue (job.view.point j))).query.fold
        (CanonicalAllocatedTables.helpers allocation origin index job geometry dummy (run program world).run.2)) :
    SingleOpeningLifetimeSoundness.Failure Memory dummy target (NativeBrakedownCalibration.radius .goldilocks role)
      (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world := by
  let targetOrigin := AllocatedOpeningLifetimeBound.helperOrigin ctx allocation.entries allocation.reachable allocation.helperHandle allocation.references
    allocation.template allocation.assembled target parameters
  have radiusEq : CanonicalAllocatedTables.helperRadius ctx = NativeBrakedownCalibration.radius .goldilocks role := by
    unfold CanonicalAllocatedTables.helperRadius
    rw [parameters]
    exact ParameterDecodingRadius.helper_eq target role admitted
  have small : 3*CanonicalAllocatedTables.helperRadius ctx < ctx.helper.code.blocks.val-ctx.helper.code.messageBlocks.val+1 := by
    unfold CanonicalAllocatedTables.helperRadius
    rw [parameters]
    exact ParameterDecodingRadius.helper_small target targetOrigin role admitted
  rw [← radiusEq]
  apply ProgramOpeningLifetime.helper program world dummy target (CanonicalAllocatedTables.helperRadius ctx)
  exact AllocatedHelperLifetime.witness ctx chooseHelper chooseBatch memory world lookup progress after executed origin index job
    allocation.entries allocation.reachable allocation.helperHandle allocation.references allocation.template allocation.assembled geometry dummy
    (run program world).run.2 (CanonicalAllocatedTables.helperRadius ctx) target parameters profile observed small framing responseFits wrong

end
end FormalProof4FHE.HasteBoots.CanonicalAllocatedHelperCoverage
