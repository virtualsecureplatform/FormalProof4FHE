module
public import FormalProof4FHE.HasteBoots.AllocatedRegistrySeed
@[expose] public section

/-! One actual completed scalar input fixes the complete allocated family at
an actual positive read in an enclosing program. Source/helper ancestry is
semantic and may be out of order; one shared seed-order exception is retained. -/
namespace FormalProof4FHE.HasteBoots.AllocatedLookupReadStability
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input World)
open AllocatedLookupTables (sources helpers helperIndex Geometry)
open AllocatedLookupFrontier (sourceKey helperKey Resolved)
noncomputable section

variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)

structure Ancestry (history : List Observation) : Prop where
  sources : ∀ column : Fin (origin.ready.jobs.get index).tag.request.columns, ∃ position,
    NativeSeedAncestry.Realized world history (LookupScalarSeedQuote.forkInput ctx world) position
      (.source (sourceKey (ctx := ctx) (world := world) (job.slots.slot column)))
  helper : ∃ position, NativeSeedAncestry.Realized world history (LookupScalarSeedQuote.forkInput ctx world) position
    (.helper (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper)))

/-- Explicit native frame/allocation domain. The helper association is an
original binding recognized in the actual prepared parent, not an ancestry
or chronological certificate and not a supplied snapshot equality. -/
structure Framing (ctx : Context (Vector Opening)) (world : World) where
  preflightFrames : List TranscriptFrame.Frame
  preflightBytes : (OracleProgram.run (NativeSharedLookupParent.preflight NativeGoldBlockCode.description.row ctx.registry.val ctx.helper ctx.parent ctx.requests) world).run.1.1.input =
    TranscriptFrame.encodeMany preflightFrames
  preflightValid : ∀ frame ∈ preflightFrames, TranscriptFrame.Valid frame
  registryFits : ∀ sources : Vector NativeCanonicalLookupWire.Source,
    (OracleProgram.run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val →
      (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit
  groupedFits : (NativeLookupMultiplicityWire.grouped ctx.proof.multiplicities).length < TranscriptFrame.lengthLimit
  flatFits : (NativeLookupMultiplicityWire.flattened ctx.proof.multiplicities).length < TranscriptFrame.lengthLimit
  parentFrames : List TranscriptFrame.Frame
  parentBytes : (OracleProgram.run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.1.input =
    TranscriptFrame.encodeMany parentFrames
  parentValid : ∀ frame ∈ parentFrames, TranscriptFrame.Valid frame
  binding : NativeCanonicalLookupWire.Binding
  bound : (⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩ : TranscriptFrame.Frame) ∈ parentFrames
  helper : binding.helper = InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper)

/-- Ancestry for all selected columns and the helper is an actual allocated
execution conclusion; no independent ancestry, parent index or chronology is
required once the original native framing domain has been established. -/
theorem allocated_ancestry {Memory : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (OracleProgram.run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index) (framing : Framing ctx world) (history : List Observation)
    (observed : (OracleProgram.run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist history) :
    Ancestry origin index job history := by
  obtain ⟨sources,computed,ancestry⟩ := AllocatedRegistrySeed.registered_sources entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed
    lookup progress after phase history observed
  have selected := ancestry framing.preflightFrames framing.preflightBytes framing.preflightValid (framing.registryFits sources computed) framing.groupedFits framing.flatFits
  refine ⟨fun column => selected (job.slots.slot column),?_⟩
  exact AllocatedRegistrySeed.helper_from_binding entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed
    lookup progress after phase history observed framing.parentFrames framing.parentBytes framing.parentValid framing.groupedFits framing.flatFits
    framing.binding framing.bound framing.helper

variable (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ)
    (references : Vector Reference) (template : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)
    (geometry : Geometry origin index job) (dummy : Digest) (radius : ℕ)

theorem program_read {A : Type} (program : OracleProgram.Program A)
    (ancestry : Ancestry origin index job (OracleProgram.run program world).run.2)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement ctx.proof.algebra ctx.scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra) world).1.completed)
    (position : ℕ) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (positioned : (OracleProgram.run program world).run.2[position]? = some (.output entry.coefficients.phase.pending.input offset values)) :
    (sources origin index job entries reachable helperHandle references template assembled geometry dummy (OracleProgram.run program world).run.2 radius =
        sources origin index job entries reachable helperHandle references template assembled geometry dummy ((OracleProgram.run program world).run.2.take position) radius ∧
      helpers origin index job entries reachable helperHandle references template assembled geometry dummy (OracleProgram.run program world).run.2 radius =
        helpers origin index job entries reachable helperHandle references template assembled geometry dummy ((OracleProgram.run program world).run.2.take position) radius) ∨
      SeedQuoteOrder.Bad OracleProgramMachine.step program world := by
  by_cases safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world
  · apply Or.inl
    have quoted := LookupScalarSeedQuote.completed_quote origin rootsFit statementFits domain entry member
    obtain ⟨fuel,completed⟩ := OracleProgramMachine.complete program world
    have logs := congrArg Prod.snd completed
    have resolved : Resolved origin index job dummy ((OracleProgram.run program world).run.2.take position) entry.coefficients.phase.pending.input := by
      constructor
      · intro column
        obtain ⟨parentPosition,realized⟩ := ancestry.sources column
        have native : NativeSeedAncestry.Realized world
            (OracleProgram.run (OracleMachine.take OracleProgramMachine.step fuel program) world).run.2
            (LookupScalarSeedQuote.forkInput ctx world) parentPosition (.source (sourceKey (ctx := ctx) (world := world) (job.slots.slot column))) := by
          rw [logs]; exact realized
        have found := native.before_read_resolves OracleProgramMachine.step fuel program world safe position entry.coefficients.phase.pending.input offset values positive
          (by rw [logs]; exact positioned) quoted _ (List.mem_singleton_self _)
        simpa only [logs,AllocatedLookupFrontier.resolved,NativeRootFamilyHistory.reconstruct,NativeRootFamilyHistory.initial,NativeRootFamilyState.fold_parent] using found
      · obtain ⟨parentPosition,realized⟩ := ancestry.helper
        have native : NativeSeedAncestry.Realized world
            (OracleProgram.run (OracleMachine.take OracleProgramMachine.step fuel program) world).run.2
            (LookupScalarSeedQuote.forkInput ctx world) parentPosition (.helper (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper))) := by
          rw [logs]; exact realized
        have root := LookupScalarSeedQuote.completed_root origin rootsFit statementFits domain entry member
          (ctx.proof.roots.val.get (helperIndex origin index)) (List.get_mem _ _)
        have key : helperKey origin index ∈ NativeSeedAncestry.Keys entry.coefficients.phase.pending.input
            (.helper (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper))) :=
          List.mem_map.mpr ⟨_,root,rfl⟩
        have found := native.before_read_resolves OracleProgramMachine.step fuel program world safe position entry.coefficients.phase.pending.input offset values positive
          (by rw [logs]; exact positioned) quoted _ key
        simpa only [logs,AllocatedLookupFrontier.resolved,NativeRootFamilyHistory.reconstruct,NativeRootFamilyHistory.initial,NativeRootFamilyState.fold_parent] using found
    exact AllocatedLookupFrontier.read_at origin index job entries reachable helperHandle references template assembled geometry dummy radius
      (OracleProgram.run program world).run.2 position entry.coefficients.phase.pending.input offset values positive positioned resolved
  · exact Or.inr (not_not.mp safe)

/-- Direct allocated-caller form: original execution and framing derive the
whole-family ancestry internally, then retain one shared seed-order bad event. -/
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
    (position : ℕ) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (positioned : (OracleProgram.run program world).run.2[position]? = some (.output entry.coefficients.phase.pending.input offset values)) :
    (sources origin index job entries reachable helperHandle references template assembled geometry dummy (OracleProgram.run program world).run.2 radius =
        sources origin index job entries reachable helperHandle references template assembled geometry dummy ((OracleProgram.run program world).run.2.take position) radius ∧
      helpers origin index job entries reachable helperHandle references template assembled geometry dummy (OracleProgram.run program world).run.2 radius =
        helpers origin index job entries reachable helperHandle references template assembled geometry dummy ((OracleProgram.run program world).run.2.take position) radius) ∨
      SeedQuoteOrder.Bad OracleProgramMachine.step program world := by
  have ancestry := allocated_ancestry entries helperHandle references template chooseHelper chooseBatch memory result executed lookup progress after phase
    origin index job framing (OracleProgram.run program world).run.2 observed
  exact program_read origin index job entries reachable helperHandle references template assembled geometry dummy radius program ancestry rootsFit statementFits domain
    entry member position offset values positive positioned

end
end FormalProof4FHE.HasteBoots.AllocatedLookupReadStability
