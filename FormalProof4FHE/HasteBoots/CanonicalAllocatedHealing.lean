module
public import FormalProof4FHE.HasteBoots.CanonicalJobReferenceRecovery
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedCandidateEvent
@[expose] public section

/-! Actual canonical native healing reaches an attained original scalar
candidate, retaining its reader, factors and independently decoded tables. -/
namespace FormalProof4FHE.HasteBoots.CanonicalAllocatedHealing
open InputIndexedOracle (World)
open OracleProgram (Program run)
open NativeRootMessage (Digest)
open NativeGoldParameterStore (Entry Reference)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open AllocatedHealingWitness (Event)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World}

theorem recover {Memory A : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ) (references : Vector Reference)
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
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest)
    (healing : Event origin index job
      (CanonicalAllocatedTables.sources ⟨entries,reachable,helperHandle,references,template,
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1⟩
        origin index job geometry dummy (run program world).run.2)
      (CanonicalAllocatedTables.helpers ⟨entries,reachable,helperHandle,references,template,
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1⟩
        origin index job geometry dummy (run program world).run.2)) :
    (∃ position input, CanonicalAttainableEvent.Event program position input index.val dummy world) ∨
      NativeRootFamilyLifetime.Bad dummy (run program world).run.2 := by
  obtain ⟨entry,member,message,messageAt,configuration,found,happened⟩ := healing
  have captured := AllocatedScalarExposure.captured entries helperHandle references template chooseHelper chooseBatch memory result executed
    lookup progress after phase origin (run program world).run.2 observed
  obtain ⟨first⟩ := AllocatedScalarExposure.first_read origin program captured entry member
  rcases CanonicalJobReferenceRecovery.recover_at_first entries reachable helperHandle references template chooseHelper chooseBatch memory result executed
      lookup progress after phase origin rootsFit statementFits domain entry member program observed framing first safe before bytes valid parentDomain index job dummy with
    ⟨otherGeometry,candidate,ctxEq,bodyEq,ordinal,inputEq,entryEq,originEq,jobEq,sourcesEq,helpersEq⟩ | bad
  · exact Or.inl ⟨first.position,entry.coefficients.phase.pending.input,
      CanonicalAllocatedCandidateEvent.of_witness candidate origin index job _ _ dummy entry ctxEq bodyEq originEq ordinal jobEq sourcesEq helpersEq
        inputEq entryEq message messageAt configuration found happened⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.CanonicalAllocatedHealing
