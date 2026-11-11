module
public import FormalProof4FHE.HasteBoots.LookupExecutionJob
public import FormalProof4FHE.HasteBoots.AllocatedLookupPublicOwnership
public import FormalProof4FHE.HasteBoots.AllocatedScalarSource
public import FormalProof4FHE.HasteBoots.AllocatedScalarHelper
@[expose] public section

/-! One allocated caller execution supplies the original identity job and
its allocated source/helper ownership. Selected slots are native request
addresses; ownership is inherited without a new per-column hash bad event. -/
namespace FormalProof4FHE.HasteBoots.AllocatedLookupIdentity
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open OracleProgram (run)
noncomputable section

abbrev NativeOrigin (ctx : Context (Vector Opening)) (world : World) (body : NativeSharedLookupBody.Bound) :=
  LookupExecutionOrigin.Origin NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world body

variable {Memory : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (helperHandle : ℕ) (references : Vector Reference) (template : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (ctx : Context (Vector Opening)) (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 =
      .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory)
    (phase : result.phase = .batches lookup progress (.verification (.done after)))

include executed phase

/-- No separately supplied assembly, ready-state, scalar completion or terminal
certificate is required by the allocated entry point. -/
theorem recover : AllocatedLookupContext.assemble entries helperHandle references template = some ctx ∧
    Nonempty (NativeOrigin ctx world lookup.body) := by
  have assembled := AllocatedLookupPublicOwnership.assembled entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed
  have helpers := AllocatedLookupPublicOwnership.helpers_done entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed
    lookup progress after phase
  have origin := NativeGoldHelperVerification.helpers_origin ctx chooseHelper memory world lookup.body lookup.plan (.done lookup.helpers) helpers
  have native := origin.native
  simp only [NativeGoldHelperVerification.Context.native,NativeSharedLookupHelpers.run_protocol] at native
  have completed := congrArg Prod.fst native
  change (run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.1 = some (.bound lookup.body) at completed
  exact ⟨assembled,LookupExecutionOrigin.recover _ _ _ _ _ _ _ _ _ world lookup.body completed⟩

include reachable

/-- The original source allocation and reference root of every selected column
follow from the actual assembled store, preserving repeated source addresses. -/
theorem source_entry (origin : NativeOrigin ctx world lookup.body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index) (column : Fin (origin.ready.jobs.get index).tag.request.columns) :
    ∃ (reference : Reference) (entry : Entry), references.val[(job.slots.slot column).val]? = some reference ∧
      entries[reference.handle]? = some entry ∧ NativeGoldParameterStore.GoodEntry entry ∧
      ctx.registry.val.get (job.slots.slot column) = ⟨entry.initialized.parameters,reference.root⟩ ∧
      entry.initialized.parameters.numVariables.val = lookup.body.sourceVariables ∧
      entry.initialized.parameters.width.val = 3+origin.padding := by
  have assembled := (recover entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase).1
  obtain ⟨reference,entry,referenceAt,entryAt,good,same⟩ := AllocatedLookupContext.source_entry entries reachable helperHandle references template ctx assembled
    (job.slots.slot column)
  have dimensions := origin.registry_dimensions (job.slots.slot column)
  rw [same] at dimensions
  exact ⟨reference,entry,referenceAt,entryAt,good,same,dimensions⟩

/-- All selected sources and the actual checked helper inherit public-table
ownership from this same allocated run, with one existing lifetime hash bad
event shared across all columns and aliases. This does not assert opening truth. -/
theorem owned_or_bad (origin : NativeOrigin ctx world lookup.body) (index : Fin origin.ready.jobs.length)
    (job : LookupExecutionJob.Job origin index) (dummy : Digest) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist history) :
    ((∀ column : Fin (origin.ready.jobs.get index).tag.request.columns,
      LookupSourcePublicOwnership.Owned ctx chooseHelper chooseBatch memory world lookup progress after
        (AllocatedLookupPublicOwnership.native_phase entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase)
        entries reachable references
        (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx
          (recover entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase).1).1
        dummy history (job.slots.slot column)) ∧
      HelperPublicOwnership.Owned ctx chooseHelper memory world lookup.body lookup.plan lookup.helpers
        (AllocatedLookupPublicOwnership.helpers_done entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase)
        entries reachable helperHandle dummy history job.view.checked) ∨ NativeRootFamilyLifetime.Bad dummy history := by
  have helper := AllocatedLookupPublicOwnership.all_helpers_owned entries reachable helperHandle references template chooseHelper chooseBatch memory world ctx result executed
    lookup progress after phase dummy history job.view.checked (List.mem_of_getElem? job.view.checkedAt)
  rcases AllocatedLookupPublicOwnership.all_sources_owned_or_bad entries reachable helperHandle references template chooseHelper chooseBatch memory world ctx result executed
      lookup progress after phase dummy history truthful observed with sources | bad
  · exact Or.inl ⟨fun column => sources (job.slots.slot column) (job.used column),helper⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.AllocatedLookupIdentity
