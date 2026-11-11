module
public import FormalProof4FHE.HasteBoots.ProgramFirstStreamRead
public import FormalProof4FHE.HasteBoots.AllocatedLookupReadStability
@[expose] public section

/-! Actual allocated execution supplies a causal first-read selector for
every retained scalar record in a containing program. The selected read need
not be a native read: prequeries, empty reads and far offsets remain visible. -/
namespace FormalProof4FHE.HasteBoots.AllocatedScalarExposure
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}

def Captured (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (history : List Observation) : Prop :=
  (NativeScalarBatchVerifier.execute origin.ready.statement ctx.proof.algebra ctx.scalarFuel
    (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra) world).2.Sublist history

theorem recover {Memory : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after))) :
    ∃ origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body,
      Captured origin (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2 := by
  have native := AllocatedRegistrySeed.native_execution entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase
  obtain ⟨origin,logged⟩ := LookupScalarTrace.recover NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world lookup.body native.1
  exact ⟨origin,logged.trans native.2⟩

/-- Every recovered origin has its scalar observations in the actual
allocated caller history, hence in any containing execution history. -/
theorem captured {Memory : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body) (history : List Observation)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist history) :
    Captured origin history := by
  have native := AllocatedRegistrySeed.native_execution entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase
  exact (LookupScalarTrace.logged_of_success origin native.1).trans (native.2.trans observed)

theorem first_read {A : Type} (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (program : OracleProgram.Program A)
    (captured : Captured origin (run program world).run.2)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement ctx.proof.algebra ctx.scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra) world).1.completed) :
    Nonempty (ProgramFirstStreamRead.First program world entry.coefficients.phase.pending.input) := by
  obtain ⟨position,offset,present⟩ := LookupScalarTrace.completed_in origin (run program world).run.2 captured entry member
  apply ProgramFirstStreamRead.of_output program world entry.coefficients.phase.pending.input offset _ _ (List.mem_of_getElem? present)
  simp only [ne_eq,← List.length_eq_zero_iff,InputIndexedOracle.bytes_length]
  decide

open NativeRootMessage (Digest)
open AllocatedLookupTables (sources helpers Geometry)
open AllocatedLookupReadStability (Framing)

/-- The actual causal selector supplies the pre-read family for a completed
original scalar input. No read position, output occurrence, freshness or
chronological ancestry certificate is supplied independently. -/
theorem first_stable {Memory A : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (helperHandle : ℕ) (references : Vector Reference) (template : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (OracleProgram.run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)
    (geometry : Geometry origin index job) (dummy : Digest) (radius : ℕ)
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
    :
    ∃ first : ProgramFirstStreamRead.First program world entry.coefficients.phase.pending.input,
      (sources origin index job entries reachable helperHandle references template assembled geometry dummy (run program world).run.2 radius =
          sources origin index job entries reachable helperHandle references template assembled geometry dummy (OracleProgram.runPrefix first.position program world).run.2 radius ∧
        helpers origin index job entries reachable helperHandle references template assembled geometry dummy (run program world).run.2 radius =
          helpers origin index job entries reachable helperHandle references template assembled geometry dummy (OracleProgram.runPrefix first.position program world).run.2 radius) ∨
        SeedQuoteOrder.Bad OracleProgramMachine.step program world := by
  have recorded := captured entries helperHandle references template chooseHelper chooseBatch memory result executed lookup progress after phase origin
    (run program world).run.2 observed
  obtain ⟨first⟩ := first_read origin program recorded entry member
  have positive : InputIndexedOracle.bytes world entry.coefficients.phase.pending.input first.offset first.count ≠ [] := by
    simpa only [ne_eq,← List.length_eq_zero_iff,InputIndexedOracle.bytes_length] using Nat.ne_of_gt first.positive
  have stable := AllocatedLookupReadStability.allocated_program_read entries reachable helperHandle references template chooseHelper chooseBatch memory result executed
    lookup progress after phase origin index job assembled geometry dummy radius program observed framing rootsFit statementFits domain entry member
    first.position first.offset (InputIndexedOracle.bytes world entry.coefficients.phase.pending.input first.offset first.count) positive first.outputAt
  rw [← first.history] at stable
  exact ⟨first,stable⟩

end
end FormalProof4FHE.HasteBoots.AllocatedScalarExposure
