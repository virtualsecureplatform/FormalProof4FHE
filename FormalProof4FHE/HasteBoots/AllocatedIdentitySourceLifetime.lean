module
public import FormalProof4FHE.HasteBoots.AllocatedIdentityAlternatives
public import FormalProof4FHE.HasteBoots.AllocatedSourceLifetime
@[expose] public section

/-! Actual false identity equations reach attained healing, original source
PCS lifetime witnesses, helper receipt mismatches, or one shared hash event. -/
namespace FormalProof4FHE.HasteBoots.AllocatedIdentitySourceLifetime
open InputIndexedOracle (World)
open OracleProgram (Program run)
open NativeRootMessage (Digest)
open NativeGoldParameterStore (Entry Reference)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World}

theorem false_identity_source_lifetime {Memory A : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ) (references : Vector Reference)
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
    (sourceResponseFits : ∀ receipt ∈ after.receipts, (NativeGoldBatchResponseBinding.payload receipt.call.opening).length < TranscriptFrame.lengthLimit) :
    (∃ position input, AttainableIdentityEvent.Event program position input index.val dummy radius world) ∨
      AllocatedSourceLifetime.Witness ctx chooseHelper chooseBatch memory world lookup progress after
        (AllocatedLookupPublicOwnership.native_phase entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase)
        origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        dummy (run program world).run.2 radius ∨
      LookupWrongReceipts.HelperFalse ctx chooseHelper world lookup origin index job (AllocatedLookupTables.helpers origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius) ∨
      NativeRootFamilyLifetime.Bad dummy (run program world).run.2 := by
  rcases AllocatedIdentityAlternatives.false_identity_alternatives entries reachable helperHandle references template chooseHelper chooseBatch memory
    result executed lookup progress after phase origin rootsFit statementFits domain program observed framing safe before bytes valid parentDomain
    index job geometry dummy radius frames decoded initial with attained | wrong | bad
  · exact Or.inl attained
  · have nativePhase := AllocatedLookupPublicOwnership.native_phase entries helperHandle references template chooseHelper chooseBatch memory world ctx
      result executed lookup progress after phase
    have nativeObserved : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist
        (run program world).run.2 := by
      rw [← (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).2.2]
      exact observed
    rcases wrong with source | helper
    · rcases AllocatedSourceLifetime.source_or_bad ctx chooseHelper chooseBatch memory world lookup progress after nativePhase origin index job
        entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius (OracleProgram.run_replay program |>.truthful world) nativeObserved
        small sourceFraming sourceResponseFits source with lifetime | bad
      · exact Or.inr (Or.inl lifetime)
      · exact Or.inr (Or.inr (Or.inr bad))
    · exact Or.inr (Or.inr (Or.inl (LookupWrongReceipts.wrong_helper ctx chooseHelper chooseBatch memory world lookup progress after nativePhase
        origin index job _ helper)))
  · exact Or.inr (Or.inr (Or.inr bad))

end
end FormalProof4FHE.HasteBoots.AllocatedIdentitySourceLifetime
