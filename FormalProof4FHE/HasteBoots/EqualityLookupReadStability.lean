module
public import FormalProof4FHE.HasteBoots.EqualityInputFamilyView
@[expose] public section

/-! The exact original source/helper tables are stable at a positive equality
read, with the shared seed-order exception retained. No later scalar sampler
or completed equality receipt is required to name the original roots. -/
namespace FormalProof4FHE.HasteBoots.EqualityLookupReadStability
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input World)
open AllocatedLookupTables (sources helpers helperIndex Geometry)
open AllocatedLookupFrontier (sourceKey helperKey Resolved)
open AllocatedLookupReadStability (Ancestry Framing allocated_ancestry)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World} {body : NativeSharedLookupBody.Bound}
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index)
    (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries) (helperHandle : ℕ)
    (references : Vector Reference) (template : Context (Vector Opening))
    (assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx)
    (geometry : Geometry origin index job) (dummy : Digest) (radius : ℕ)

theorem program_read {A : Type} (program : OracleProgram.Program A)
    (ancestry : Ancestry origin index job (OracleProgram.run program world).run.2)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (draw : NativeLookupEquality.Draw origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3)
    (member : draw ∈ origin.ready.machine.draws)
    (position : ℕ) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (positioned : (OracleProgram.run program world).run.2[position]? = some (.output draw.coefficients.phase.pending.input offset values)) :
    (sources origin index job entries reachable helperHandle references template assembled geometry dummy (OracleProgram.run program world).run.2 radius =
        sources origin index job entries reachable helperHandle references template assembled geometry dummy ((OracleProgram.run program world).run.2.take position) radius ∧
      helpers origin index job entries reachable helperHandle references template assembled geometry dummy (OracleProgram.run program world).run.2 radius =
        helpers origin index job entries reachable helperHandle references template assembled geometry dummy ((OracleProgram.run program world).run.2.take position) radius) ∨
      SeedQuoteOrder.Bad OracleProgramMachine.step program world := by
  by_cases safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world
  · apply Or.inl
    have quoted := (EqualityInputFamilyView.recover origin rootsFit draw member).2
    obtain ⟨fuel,completed⟩ := OracleProgramMachine.complete program world
    have logs := congrArg Prod.snd completed
    have resolved : Resolved origin index job dummy ((OracleProgram.run program world).run.2.take position) draw.coefficients.phase.pending.input := by
      constructor
      · intro column
        obtain ⟨parentPosition,realized⟩ := ancestry.sources column
        have native : NativeSeedAncestry.Realized world
            (OracleProgram.run (OracleMachine.take OracleProgramMachine.step fuel program) world).run.2
            (LookupScalarSeedQuote.forkInput ctx world) parentPosition (.source (sourceKey (ctx := ctx) (world := world) (job.slots.slot column))) := by
          rw [logs]; exact realized
        have found := native.before_read_resolves OracleProgramMachine.step fuel program world safe position draw.coefficients.phase.pending.input offset values positive
          (by rw [logs]; exact positioned) quoted _ (List.mem_singleton_self _)
        simpa only [logs,AllocatedLookupFrontier.resolved,NativeRootFamilyHistory.reconstruct,NativeRootFamilyHistory.initial,NativeRootFamilyState.fold_parent] using found
      · obtain ⟨parentPosition,realized⟩ := ancestry.helper
        have native : NativeSeedAncestry.Realized world
            (OracleProgram.run (OracleMachine.take OracleProgramMachine.step fuel program) world).run.2
            (LookupScalarSeedQuote.forkInput ctx world) parentPosition (.helper (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper))) := by
          rw [logs]; exact realized
        have root := EqualityInputFamilyView.parsed_root draw.coefficients.phase.pending.input ctx.proof.roots
          (EqualityInputFamilyView.recover origin rootsFit draw member).1
          (ctx.proof.roots.val.get (helperIndex origin index)) (List.get_mem _ _)
        have key : helperKey origin index ∈ NativeSeedAncestry.Keys draw.coefficients.phase.pending.input
            (.helper (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper))) :=
          List.mem_map.mpr ⟨_,root,rfl⟩
        have found := native.before_read_resolves OracleProgramMachine.step fuel program world safe position draw.coefficients.phase.pending.input offset values positive
          (by rw [logs]; exact positioned) quoted _ key
        simpa only [logs,AllocatedLookupFrontier.resolved,NativeRootFamilyHistory.reconstruct,NativeRootFamilyHistory.initial,NativeRootFamilyState.fold_parent] using found
    exact AllocatedLookupFrontier.read_at origin index job entries reachable helperHandle references template assembled geometry dummy radius
      (OracleProgram.run program world).run.2 position draw.coefficients.phase.pending.input offset values positive positioned resolved
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
    (draw : NativeLookupEquality.Draw origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3)
    (member : draw ∈ origin.ready.machine.draws)
    (position : ℕ) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (positioned : (OracleProgram.run program world).run.2[position]? = some (.output draw.coefficients.phase.pending.input offset values)) :
    (sources origin index job entries reachable helperHandle references template assembled geometry dummy (OracleProgram.run program world).run.2 radius =
        sources origin index job entries reachable helperHandle references template assembled geometry dummy ((OracleProgram.run program world).run.2.take position) radius ∧
      helpers origin index job entries reachable helperHandle references template assembled geometry dummy (OracleProgram.run program world).run.2 radius =
        helpers origin index job entries reachable helperHandle references template assembled geometry dummy ((OracleProgram.run program world).run.2.take position) radius) ∨
      SeedQuoteOrder.Bad OracleProgramMachine.step program world := by
  have ancestry := allocated_ancestry entries helperHandle references template chooseHelper chooseBatch memory result executed lookup progress after phase
    origin index job framing (OracleProgram.run program world).run.2 observed
  exact program_read origin index job entries reachable helperHandle references template assembled geometry dummy radius program ancestry rootsFit
    draw member position offset values positive positioned

end
end FormalProof4FHE.HasteBoots.EqualityLookupReadStability
