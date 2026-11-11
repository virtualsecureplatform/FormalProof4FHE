module
public import FormalProof4FHE.HasteBoots.AllocatedIdentityAlternatives
public import FormalProof4FHE.HasteBoots.LookupReceiptQueryMeaning
@[expose] public section

/-! Native false identity equations yield attained healing, actual accepted
false source/helper rows, or the same shared full-history root/hash event. -/
namespace FormalProof4FHE.HasteBoots.AllocatedIdentityReceiptAlternatives
open InputIndexedOracle (World)
open OracleProgram (Program run)
open NativeRootMessage (Digest)
open NativeGoldParameterStore (Entry Reference)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World}

theorem false_identity_receipts {Memory A : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ) (references : Vector Reference)
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
        geometry dummy (run program world).run.2 radius))) :
    (∃ position input, AttainableIdentityEvent.Event program position input index.val dummy radius world) ∨
      LookupWrongReceipts.SourceFalse ctx chooseBatch world lookup after origin index job (AllocatedLookupTables.sources origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius) ∨
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
    rcases LookupWrongReceipts.wrong_receipt ctx chooseHelper chooseBatch memory world lookup progress after nativePhase origin index job _ _ wrong with source | helper
    · exact Or.inr (Or.inl source)
    · exact Or.inr (Or.inr (Or.inl helper))
  · exact Or.inr (Or.inr (Or.inr bad))

end
end FormalProof4FHE.HasteBoots.AllocatedIdentityReceiptAlternatives
