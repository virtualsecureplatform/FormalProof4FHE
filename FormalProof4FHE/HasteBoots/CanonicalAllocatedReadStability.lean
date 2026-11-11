module
public import FormalProof4FHE.HasteBoots.CanonicalCandidateFixation
@[expose] public section

/-! Native ancestry makes every canonical table stable at the first scalar
read. Apply the original radius-parametric result separately to each object. -/
namespace FormalProof4FHE.HasteBoots.CanonicalAllocatedReadStability
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input World)
open AllocatedLookupTables (Geometry)
open AllocatedLookupReadStability (Framing)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World}

theorem allocated_program_read {Memory A : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (helperHandle : ℕ) (references : Vector Reference) (template : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (OracleProgram.run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)
    (geometry : Geometry origin index job) (dummy : Digest)
    (program : OracleProgram.Program A)
    (observed : (OracleProgram.run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist
      (OracleProgram.run program world).run.2)
    (framing : Framing ctx world)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement ctx.proof.algebra ctx.scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra) world).1.completed)
    (position : ℕ) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (positioned : (OracleProgram.run program world).run.2[position]? = some (.output entry.coefficients.phase.pending.input offset values)) :
    (CanonicalAllocatedTables.sources ⟨entries,reachable,helperHandle,references,template,assembled⟩ origin index job geometry dummy (OracleProgram.run program world).run.2 =
        CanonicalAllocatedTables.sources ⟨entries,reachable,helperHandle,references,template,assembled⟩ origin index job geometry dummy ((OracleProgram.run program world).run.2.take position) ∧
      CanonicalAllocatedTables.helpers ⟨entries,reachable,helperHandle,references,template,assembled⟩ origin index job geometry dummy (OracleProgram.run program world).run.2 =
        CanonicalAllocatedTables.helpers ⟨entries,reachable,helperHandle,references,template,assembled⟩ origin index job geometry dummy ((OracleProgram.run program world).run.2.take position)) ∨
      SeedQuoteOrder.Bad OracleProgramMachine.step program world := by
  by_cases safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world
  · left
    constructor
    · funext column
      have stable := (AllocatedLookupReadStability.allocated_program_read entries reachable helperHandle references template chooseHelper chooseBatch memory
        result executed lookup progress after phase origin index job assembled geometry dummy
        (CanonicalAllocatedTables.sourceRadius ctx (job.slots.slot column)) program observed framing rootsFit statementFits domain entry member
        position offset values positive positioned).resolve_right safe
      exact congrFun stable.1 column
    · have stable := (AllocatedLookupReadStability.allocated_program_read entries reachable helperHandle references template chooseHelper chooseBatch memory
        result executed lookup progress after phase origin index job assembled geometry dummy (CanonicalAllocatedTables.helperRadius ctx)
        program observed framing rootsFit statementFits domain entry member position offset values positive positioned).resolve_right safe
      exact stable.2
  · exact Or.inr (Classical.not_not.mp safe)

end
end FormalProof4FHE.HasteBoots.CanonicalAllocatedReadStability
