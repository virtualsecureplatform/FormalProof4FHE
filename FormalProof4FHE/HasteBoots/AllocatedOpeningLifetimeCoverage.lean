module
public import FormalProof4FHE.HasteBoots.OpeningLifetimeFamily
@[expose] public section

/-! Actual allocated identity alternatives enter the enclosing program's
unbounded PCS family lifetime, retaining its original source slots and the
single shared full-history hash event. -/
namespace FormalProof4FHE.HasteBoots.AllocatedOpeningLifetimeCoverage
open InputIndexedOracle (World)
open OracleProgram (Program run)
open NativeRootMessage (Digest)
open NativeGoldParameterStore (Entry Reference)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
noncomputable section

theorem source {Memory A : Type} (ctx : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (lookup : NativeGoldLookupVerification.Prepared Memory)
    (progress : NativeSharedSourceClaims.Progress) (after : NativeDeferredBatchVerification.Progress Memory)
    (executed : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
      .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ)
    (references : Vector Reference) (template : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)
    (dummy : Digest) (program : Program A) (radius : ℕ)
    (occurred : AllocatedSourceLifetime.Witness ctx chooseHelper chooseBatch memory world lookup progress after executed origin index job
      entries reachable helperHandle references template assembled dummy (run program world).run.2 radius) :
    ∃ slot : Fin ctx.registry.val.length, CacheBackedBatchLifetimeSoundness.Failure Memory dummy (RegistryPublicSource.context ctx slot)
      (RegistryPublicSource.origin ctx entries reachable references (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1 slot)
      radius (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world := by
  obtain ⟨column,receipt,member,parameters,witness⟩ := occurred
  refine ⟨job.slots.slot column,?_⟩
  exact ProgramOpeningLifetime.batch program world dummy _ _
    (RegistryPublicSource.origin ctx entries reachable references (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx assembled).1
      (job.slots.slot column)) radius witness

variable {ctx : Context (Vector Opening)} {world : World}

theorem false_identity_covered {Memory A : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (program : Program A)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist
      (run program world).run.2)
    (framing : AllocatedLookupReadStability.Framing ctx world)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index)
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (radius : ℕ)
    (frames : List TranscriptFrame.Frame)
    (decoded : TranscriptFrame.decodeAll origin.ready.equality.transcript.input = some frames)
    (initial : ScalarChainHealing.value (2*index.val+1) origin.ready.statement.claims.val ≠
      some (AllocatedIdentityAlternatives.truth origin index job (AllocatedLookupTables.sources origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius) (AllocatedLookupTables.helpers origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius)))
    (small : ∀ column : Fin (origin.ready.jobs.get index).tag.request.columns,
      3*radius < (ctx.registry.val.get (job.slots.slot column)).parameters.code.blocks.val-
        (ctx.registry.val.get (job.slots.slot column)).parameters.code.messageBlocks.val+1)
    (sourceFraming : ∀ receipt ∈ after.receipts, NativeGoldBatchSourceRisk.Framed (receipt.call.context ctx.tables ctx.fieldFuel receipt.before))
    (sourceResponseFits : ∀ receipt ∈ after.receipts, (NativeGoldBatchResponseBinding.payload receipt.call.opening).length < TranscriptFrame.lengthLimit)
    (helperTarget : NativeGoldPcsExecution.Context) (helperParameters : ctx.helper = helperTarget.parameters)
    (helperProfile : ctx.parent.profile = helperTarget.transcript.profile)
    (helperSmall : 3*radius < ctx.helper.code.blocks.val-ctx.helper.code.messageBlocks.val+1)
    (helperFraming : ∀ receipt ∈ lookup.helpers.receipts,
      SingleOpeningAvailability.Framed (NativeGoldHelperVerification.context ctx.tables ctx.helper ctx.fieldFuel receipt.before receipt.call))
    (helperResponseFits : ∀ receipt ∈ lookup.helpers.receipts, (SingleOpeningColumnLaw.payload receipt.call.opening).length < TranscriptFrame.lengthLimit) :
    (∃ position input, AttainableIdentityEvent.Event program position input index.val dummy radius world) ∨
      SingleOpeningLifetimeSoundness.SourceBad dummy (SingleOpeningLifetimeSoundness.clean program) id OracleProgramMachine.step world ∨
      OpeningLifetimeFamily.Failure Memory Memory dummy helperTarget (RegistryPublicSource.context ctx) (RegistryPublicSource.origin ctx entries reachable references
        (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx
          (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1).1)
        radius (fun _ => radius) program OracleProgramMachine.step world := by
  rcases AllocatedIdentityOpeningLifetime.false_identity_opening_lifetimes entries reachable helperHandle references template chooseHelper chooseBatch memory
    result executed lookup progress after phase origin rootsFit statementFits domain program observed framing safe before bytes valid parentDomain
    index job geometry dummy radius frames decoded initial small sourceFraming sourceResponseFits helperTarget helperParameters helperProfile helperSmall
    helperFraming helperResponseFits with attained | batch | single | bad
  · exact Or.inl attained
  · have nativePhase := AllocatedLookupPublicOwnership.native_phase entries helperHandle references template chooseHelper chooseBatch memory world ctx
      result executed lookup progress after phase
    obtain ⟨slot,failed⟩ := source ctx chooseHelper chooseBatch memory world lookup progress after nativePhase origin index job entries reachable helperHandle
      references template (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
      dummy program radius batch
    exact Or.inr (Or.inr (Or.inr ⟨slot,failed⟩))
  · exact Or.inr (Or.inr (Or.inl (ProgramOpeningLifetime.helper program world dummy helperTarget radius single)))
  · exact Or.inr (Or.inl (ProgramOpeningLifetime.root_bad program world dummy bad))

end
end FormalProof4FHE.HasteBoots.AllocatedOpeningLifetimeCoverage
