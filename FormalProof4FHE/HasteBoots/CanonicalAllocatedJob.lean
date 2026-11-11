module
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedHelperCoverage
@[expose] public section

/-! Retain an actual allocated native job and its original execution log.
Wrong public folds use parameter-derived source/helper radii independently. -/
namespace FormalProof4FHE.HasteBoots.CanonicalAllocatedJob
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open OracleProgram (Program run)
open AllocatedFamilyFunctions (Allocation)
noncomputable section

structure Job {Memory A : Type} (ctx : Context (Vector Opening)) (allocation : Allocation ctx)
    (program : Program A) (world : World) where
  chooseHelper : NativeGoldPcsProgram.Scheduler Memory
  chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory
  memory : Memory
  lookup : NativeGoldLookupVerification.Prepared Memory
  progress : NativeSharedSourceClaims.Progress
  after : NativeDeferredBatchVerification.Progress Memory
  executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
    .batches lookup progress (.verification (.done after))
  origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body
  index : Fin origin.ready.jobs.length
  job : LookupExecutionJob.Job origin index
  geometry : AllocatedLookupTables.Geometry origin index job
  observed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist (run program world).run.2
  sourceFraming : ∀ receipt ∈ after.receipts, NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before)
  sourceResponseFits : ∀ receipt ∈ after.receipts, (NativeGoldBatchResponseBinding.payload receipt.call.opening).length < TranscriptFrame.lengthLimit
  helperFraming : ∀ receipt ∈ lookup.helpers.receipts,
    SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call)
  helperResponseFits : ∀ receipt ∈ lookup.helpers.receipts, (SingleOpeningColumnLaw.payload receipt.call.opening).length < TranscriptFrame.lengthLimit

variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : Allocation ctx} {program : Program A} {world : World}

def sources (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :=
  CanonicalAllocatedTables.sources allocation data.origin data.index data.job data.geometry dummy (run program world).run.2

def helpers (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest) :=
  CanonicalAllocatedTables.helpers allocation data.origin data.index data.job data.geometry dummy (run program world).run.2

def Wrong (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest) : Prop :=
  LookupIdentityCausalReduction.Wrong data.job.view (sources data dummy) (helpers data dummy)

theorem wrong_covered (data : Job (Memory := Memory) ctx allocation program world) (dummy : Digest)
    (target : NativeGoldPcsExecution.Context) (parameters : ctx.helper = target.parameters)
    (profile : ctx.parent.profile = target.transcript.profile) (helperRole : NativeBrakedownCalibration.Role)
    (helperAdmitted : SingleOpeningCalibration.Matches target helperRole)
    (sourceRole : Fin ctx.registry.val.length → NativeBrakedownCalibration.Role)
    (sourceAdmitted : ∀ slot, NativeGoldBatchCalibration.Matches (RegistryPublicSource.context ctx slot) (sourceRole slot))
    (wrong : Wrong data dummy) :
    SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world ∨
    OpeningLifetimeFamily.Failure Memory Memory dummy target (RegistryPublicSource.context ctx)
      (RegistryPublicSource.origin ctx allocation.entries allocation.reachable allocation.references
        (AllocatedLookupContext.assemble_spec allocation.entries allocation.helperHandle allocation.references allocation.template ctx allocation.assembled).1)
      (NativeBrakedownCalibration.radius .goldilocks helperRole)
      (fun slot => NativeBrakedownCalibration.radius .goldilocks (sourceRole slot)) program OracleProgramMachine.step world := by
  by_cases bad : NativeRootFamilyLifetime.Bad dummy (run program world).run.2
  · exact Or.inl (ProgramOpeningLifetime.root_bad program world dummy bad)
  · right
    rcases wrong with source | helper
    · right
      obtain ⟨slot,failed⟩ := CanonicalAllocatedOpeningCoverage.source_no_bad ctx data.chooseHelper data.chooseBatch data.memory world data.lookup
        data.progress data.after data.executed data.origin data.index data.job allocation data.geometry dummy program data.observed
        sourceRole sourceAdmitted data.sourceFraming data.sourceResponseFits source bad
      refine ⟨slot,?_⟩
      have radii : CanonicalAllocatedTables.sourceRadius ctx slot = NativeBrakedownCalibration.radius .goldilocks (sourceRole slot) :=
        ParameterDecodingRadius.source_eq (RegistryPublicSource.context ctx slot) (sourceRole slot) (sourceAdmitted slot)
      rwa [radii] at failed
    · left
      exact CanonicalAllocatedHelperCoverage.helper ctx data.chooseHelper data.chooseBatch data.memory world data.lookup data.progress data.after
        data.executed data.origin data.index data.job allocation data.geometry dummy program target parameters profile helperRole helperAdmitted
        data.observed data.helperFraming data.helperResponseFits helper

end
end FormalProof4FHE.HasteBoots.CanonicalAllocatedJob
