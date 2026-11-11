module
public import FormalProof4FHE.HasteBoots.AllocatedCandidateEvent
@[expose] public section

/-! The actual allocated native identity-healing event supplies an attained
candidate at an actual original scalar first read, or the existing shared
full-history root/hash alternative. -/
namespace FormalProof4FHE.HasteBoots.AllocatedHealingWitness
open InputIndexedOracle (World)
open OracleProgram (Program run)
open NativeRootMessage (Digest)
open NativeGoldParameterStore (Entry Reference)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeScalarQueryShape (laneBits)
open NativeFieldWire (goldExtensionValue)
open MatrixFold (Cube)
noncomputable section

variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}

variable (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)
    (sources : Fin (origin.ready.jobs.get index).tag.request.columns → Cube body.sourceVariables → Fin (3+origin.padding) → NativeFields.Goldilocks)
    (helpers : Cube (laneBits (3+origin.padding)+body.sourceVariables) → Fin (3+AllocatedLookupTables.helperPadding (ctx := ctx)) → NativeFields.Goldilocks)

def Event : Prop :=
  ∃ entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement ctx.proof.algebra ctx.scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra) world).1.completed,
    ∃ message, entry.packet.messages.val[2*index.val+1]? = some message ∧
      ∃ configuration : ScalarRecoveredReplay.Configuration,
        ScalarRecoveredReplay.recover entry.coefficients.phase.pending.input = some configuration ∧
        ScalarRecoveredUnboundedLaw.event entry.coefficients.phase.pending.input configuration origin.ready.equality.transcript.profile
          (AllocatedCandidateEvent.nativeTest origin index job sources helpers message) world

theorem full_event
    (branch : (origin.ready.jobs.get index).tag.request.terminal.logicalLength.val = 2^origin.geometry.geometry.1.val)
    (happened : ScalarFinishedSourceEvent.Event origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra ctx.scalarFuel world
      ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
      (laneBits (3+origin.padding)+body.sourceVariables) (LookupIdentityCausalReduction.fullTables job.view sources helpers)
      (2*index.val+1) (LookupScalarGrammar.identityInfo origin.geometry.geometry.1 (origin.ready.jobs.get index).tag.request)) :
    Event origin index job sources helpers := by
  simpa only [Event,AllocatedCandidateEvent.nativeTest,branch,ite_true,ScalarFinishedSourceEvent.Event] using happened

theorem partial_event
    (branch : (origin.ready.jobs.get index).tag.request.terminal.logicalLength.val ≠ 2^origin.geometry.geometry.1.val)
    (happened : ScalarFinishedSourceEvent.Event origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra ctx.scalarFuel world
      ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue (origin.ready.jobs.get index).output.r)) ExtensionLookupIdentity.partialIndices
      (laneBits (3+origin.padding)+body.sourceVariables) (LookupIdentityCausalReduction.partialTables job.view sources helpers)
      (2*index.val+1) (LookupScalarGrammar.identityInfo origin.geometry.geometry.1 (origin.ready.jobs.get index).tag.request)) :
    Event origin index job sources helpers := by
  simpa only [Event,AllocatedCandidateEvent.nativeTest,branch,ite_false,ScalarFinishedSourceEvent.Event] using happened

variable {origin index job sources helpers}

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
    (geometry : AllocatedLookupTables.Geometry origin index job) (dummy : Digest) (radius : ℕ)
    (healing : Event origin index job
      (AllocatedLookupTables.sources origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius)
      (AllocatedLookupTables.helpers origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius)) :
    (∃ position input, AttainableIdentityEvent.Event program position input index.val dummy radius world) ∨
      NativeRootFamilyLifetime.Bad dummy (run program world).run.2 := by
  obtain ⟨entry,member,message,messageAt,configuration,found,happened⟩ := healing
  have captured := AllocatedScalarExposure.captured entries helperHandle references template chooseHelper chooseBatch memory result executed
    lookup progress after phase origin (run program world).run.2 observed
  obtain ⟨first⟩ := AllocatedScalarExposure.first_read origin program captured entry member
  rcases JobReferenceCandidate.recover_at_first entries reachable helperHandle references template chooseHelper chooseBatch memory result executed
      lookup progress after phase origin rootsFit statementFits domain entry member program observed framing first safe before bytes valid parentDomain index job dummy radius with
    ⟨otherGeometry,candidate,ctxEq,bodyEq,ordinal,inputEq,entryEq,originEq,jobEq,sourcesEq,helpersEq⟩ | bad
  · exact Or.inl ⟨first.position,entry.coefficients.phase.pending.input,
      AllocatedCandidateEvent.of_witness candidate origin index job _ _ dummy radius entry ctxEq bodyEq originEq ordinal jobEq sourcesEq helpersEq
        inputEq entryEq message messageAt configuration found happened⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.AllocatedHealingWitness
