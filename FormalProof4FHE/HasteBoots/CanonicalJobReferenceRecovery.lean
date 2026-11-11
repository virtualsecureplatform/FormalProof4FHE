module
public import FormalProof4FHE.HasteBoots.CanonicalAllocatedReadStability
@[expose] public section

/-! Recover an original attained job candidate with complete canonical
family equality, actual factors and its completed native reader retained. -/
namespace FormalProof4FHE.HasteBoots.CanonicalJobReferenceRecovery
open InputIndexedOracle (Input World)
open OracleProgram (Program run)
open NativeRootMessage (Digest)
open ProgramFirstStreamRead (First)
open PositionedFactorSamples (ScalarAt PointAt)
open JobReferenceCandidate (Candidate)
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World}

theorem recover_at_first {Memory A : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ) (references : Vector Reference)
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
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement ctx.proof.algebra ctx.scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra) world).1.completed)
    (program : Program A)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist
      (run program world).run.2)
    (framing : AllocatedLookupReadStability.Framing ctx world)
    (first : ProgramFirstStreamRead.First program world entry.coefficients.phase.pending.input)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (index : Fin origin.ready.jobs.length) (job : LookupExecutionJob.Job origin index) (dummy : Digest) :
    (∃ geometry : AllocatedLookupTables.Geometry origin index job, ∃ candidate : Candidate program first.position world,
      candidate.selection.ctx = ctx ∧ candidate.selection.body = lookup.body ∧ candidate.selection.index.val = index.val ∧
        candidate.selection.family.input = entry.coefficients.phase.pending.input ∧
        candidate.compression.value.view.reader.entry = entry ∧
        HEq candidate.selection.origin origin ∧ HEq candidate.selection.job job ∧
        HEq (CanonicalCandidateFixation.sources candidate dummy)
          (CanonicalAllocatedTables.sources ⟨entries,reachable,helperHandle,references,template,
            (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1⟩
            origin index job geometry dummy (run program world).run.2) ∧
        HEq (CanonicalCandidateFixation.helpers candidate dummy)
          (CanonicalAllocatedTables.helpers ⟨entries,reachable,helperHandle,references,template,
            (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1⟩
            origin index job geometry dummy (run program world).run.2)) ∨
      NativeRootFamilyLifetime.Bad dummy (run program world).run.2 := by
  rcases AllocatedLookupTables.geometry_or_bad entries reachable helperHandle references template chooseHelper chooseBatch memory result executed lookup progress after phase
      origin index job dummy (run program world).run.2 (OracleProgram.run_replay program |>.truthful world) observed with geometry | bad
  · obtain ⟨family,registry,helper,requests,_,roots,input⟩ := AllocatedScalarFamily.at_scalar_first entries helperHandle references template
      chooseHelper chooseBatch memory result executed lookup progress after phase origin rootsFit statementFits domain entry member program observed framing first safe
      before bytes valid parentDomain
    obtain ⟨_,compression,offset,point,compressionView,offsetView,pointView,compressionAt,offsetAt,pointAt,y,r,eqPoint,compressionLog,offsetLog,pointLog⟩ :=
      AllocatedFactorSamples.observed entries helperHandle references template chooseHelper chooseBatch memory result executed lookup progress after phase
        origin job rootsFit statementFits domain entry member program observed
    let allocation : AllocatedFamilyFunctions.Allocation ctx := ⟨entries,reachable,helperHandle,references,template,
      (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1⟩
    let selection : AllocatedJobFamily.Selection program first.position world :=
      ⟨ctx,lookup.body,allocation,origin,index,job,geometry,family,registry,helper,requests,roots⟩
    let compressionSample : ScalarAt program world selection.family.input (.compression selection.index.val) :=
      ⟨compression,by rw [compressionView]; rfl,by rw [compressionView,input]; rfl,compressionAt,compressionLog⟩
    let offsetSample : ScalarAt program world selection.family.input (.offset selection.index.val) :=
      ⟨offset,by rw [offsetView]; rfl,by rw [offsetView,input]; rfl,offsetAt,offsetLog⟩
    let pointSample : PointAt program world selection.family.input (.equalityPoint selection.index.val) :=
      ⟨point,by rw [pointView]; rfl,by rw [pointView,input]; rfl,pointAt,pointLog⟩
    have positive : InputIndexedOracle.bytes world entry.coefficients.phase.pending.input first.offset first.count ≠ [] := by
      simpa only [ne_eq,← List.length_eq_zero_iff,InputIndexedOracle.bytes_length] using Nat.ne_of_gt first.positive
    have stability := CanonicalAllocatedReadStability.allocated_program_read entries reachable helperHandle references template chooseHelper chooseBatch memory result executed
      lookup progress after phase origin index job allocation.assembled geometry dummy program observed framing rootsFit statementFits domain entry member
      first.position first.offset _ positive first.outputAt
    have stable := stability.resolve_right safe
    rw [← first.history] at stable
    exact Or.inl ⟨geometry,⟨selection,PositionedFactorSamples.reindex first world family.input rfl input,rfl,
      compressionSample,offsetSample,pointSample,rootsFit,
      (by change compression.view.reader.statement = _; rw [compressionView]; rfl),
      (by change compression.view.reader.transcript = _; rw [compressionView]; rfl),y,r,eqPoint⟩,rfl,rfl,rfl,input,
      (by change compression.view.reader.entry = entry; rw [compressionView]; rfl),
      HEq.rfl,HEq.rfl,heq_of_eq stable.1.symm,heq_of_eq stable.2.symm⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.CanonicalJobReferenceRecovery
