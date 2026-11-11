module
public import FormalProof4FHE.HasteBoots.AllocatedHealingWitness
@[expose] public section

/-! An originally false native identity equation yields an attained healing
candidate, an original PCS Wrong alternative, or the existing shared
full-history root/hash event. Full/partial selection adds no union charge. -/
namespace FormalProof4FHE.HasteBoots.AllocatedIdentityAlternatives
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

def truth (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)
    (sources : Fin (origin.ready.jobs.get index).tag.request.columns → Cube body.sourceVariables → Fin (3+origin.padding) → NativeFields.Goldilocks)
    (helpers : Cube (laneBits (3+origin.padding)+body.sourceVariables) → Fin (3+AllocatedLookupTables.helperPadding (ctx := ctx)) → NativeFields.Goldilocks) :=
  if (origin.ready.jobs.get index).tag.request.terminal.logicalLength.val = 2^origin.geometry.geometry.1.val then
    ScalarNativeSourceHealing.truth ExtensionLookupIdentity.fullArity ExtensionLookupIdentity.fullCoefficient ExtensionLookupIdentity.fullIndices
      (laneBits (3+origin.padding)+body.sourceVariables) (LookupIdentityCausalReduction.fullTables job.view sources helpers) []
  else
    ScalarNativeSourceHealing.truth ExtensionLookupIdentity.partialArity
      (ExtensionLookupIdentity.partialCoefficient (goldExtensionValue (origin.ready.jobs.get index).output.r)) ExtensionLookupIdentity.partialIndices
      (laneBits (3+origin.padding)+body.sourceVariables) (LookupIdentityCausalReduction.partialTables job.view sources helpers) []

theorem false_identity_alternatives {Memory A : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ) (references : Vector Reference)
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
      some (truth origin index job (AllocatedLookupTables.sources origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius) (AllocatedLookupTables.helpers origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius))) :
    (∃ position input, AttainableIdentityEvent.Event program position input index.val dummy radius world) ∨
      LookupIdentityCausalReduction.Wrong job.view (AllocatedLookupTables.sources origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius) (AllocatedLookupTables.helpers origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius) ∨
      NativeRootFamilyLifetime.Bad dummy (run program world).run.2 := by
  have lift (healing : AllocatedHealingWitness.Event origin index job (AllocatedLookupTables.sources origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius) (AllocatedLookupTables.helpers origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius)) :
      (∃ position input, AttainableIdentityEvent.Event program position input index.val dummy radius world) ∨
        LookupIdentityCausalReduction.Wrong job.view (AllocatedLookupTables.sources origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius) (AllocatedLookupTables.helpers origin index job entries reachable helperHandle references template
        (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
        geometry dummy (run program world).run.2 radius) ∨
        NativeRootFamilyLifetime.Bad dummy (run program world).run.2 := by
    rcases AllocatedHealingWitness.recover entries reachable helperHandle references template chooseHelper chooseBatch memory result executed
      lookup progress after phase origin rootsFit statementFits domain program observed framing safe before bytes valid parentDomain index job geometry dummy radius healing with attained | bad
    · exact Or.inl attained
    · exact Or.inr (Or.inr bad)
  by_cases branch : (origin.ready.jobs.get index).tag.request.terminal.logicalLength.val = 2^origin.geometry.geometry.1.val
  · have falseFull := initial
    simp only [truth,branch,ite_true] at falseFull
    rcases AllocatedLookupTables.full_event_or_wrong origin index job entries reachable helperHandle references template
      (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
      geometry dummy (run program world).run.2 radius frames decoded statementFits domain branch falseFull with healing | wrong
    · exact lift (AllocatedHealingWitness.full_event origin index job _ _ branch healing)
    · exact Or.inr (Or.inl wrong)
  · have falsePartial := initial
    simp only [truth,branch,ite_false] at falsePartial
    rcases AllocatedLookupTables.partial_event_or_wrong origin index job entries reachable helperHandle references template
      (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1
      geometry dummy (run program world).run.2 radius frames decoded statementFits domain branch falsePartial with healing | wrong
    · exact lift (AllocatedHealingWitness.partial_event origin index job _ _ branch healing)
    · exact Or.inr (Or.inl wrong)

end
end FormalProof4FHE.HasteBoots.AllocatedIdentityAlternatives
