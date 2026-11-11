module
public import FormalProof4FHE.HasteBoots.LookupScalarSeedQuote
public import FormalProof4FHE.HasteBoots.SeedAncestryEmbedding
@[expose] public section

/-! Actual allocated execution supplies registered source ancestry in the
complete containing raw history. Original slots and full context hashes are
retained, while first exposures are recomputed after embedding the native log. -/
namespace FormalProof4FHE.HasteBoots.AllocatedRegistrySeed
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

variable {Memory : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (ctx : Context (Vector Opening)) (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory)
    (phase : result.phase = .batches lookup progress (.verification (.done after)))

include executed phase

theorem native_execution :
    (run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
      ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.1 = some (.bound lookup.body) ∧
    (run (NativeSharedLookupExecution.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
      ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel) world).run.2.Sublist
      (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2 := by
  have allocated := AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed
  have nativePhase := AllocatedLookupPublicOwnership.native_phase entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed
    lookup progress after phase
  have helpers := AllocatedLookupPublicOwnership.helpers_done entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed
    lookup progress after phase
  have origin := NativeGoldHelperVerification.helpers_origin ctx chooseHelper memory world lookup.body lookup.plan (.done lookup.helpers) helpers
  have native := origin.native
  simp only [NativeGoldHelperVerification.Context.native,NativeSharedLookupHelpers.run_protocol] at native
  refine ⟨congrArg Prod.fst native,?_⟩
  have earlier : (run ctx.native world).run.2.Sublist (run (NativeGoldHelperVerification.program ctx chooseHelper memory) world).run.2 := by
    rw [origin.log]
    exact List.sublist_append_left _ _
  have later := (NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress (.verification (.done after)) nativePhase).2.2.2
  have helperLog : (run (NativeGoldHelperVerification.program ctx chooseHelper memory) world).run.2.Sublist
      (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2 := by
    rw [later]
    exact List.sublist_append_left _ _
  rw [allocated.2.2]
  simpa only [NativeGoldHelperVerification.Context.native,NativeSharedLookupHelpers.run_protocol] using earlier.trans helperLog

/-- Every original registry slot obtains its ancestry from actual execution.
The remaining inputs bound native frame allocations; no chronology, frozen
source, parent-index or context/hash association certificate is assumed. -/
theorem registered_sources (history : List Observation)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist history) :
    ∃ sources : Vector NativeCanonicalLookupWire.Source,
      (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some sources.val ∧
      ∀ frames : List TranscriptFrame.Frame,
        (run (NativeSharedLookupParent.preflight NativeGoldBlockCode.description.row ctx.registry.val ctx.helper ctx.parent ctx.requests) world).run.1.1.input =
          TranscriptFrame.encodeMany frames →
        (∀ frame ∈ frames, TranscriptFrame.Valid frame) →
        (NativeCanonicalLookupWire.sourcesCodec.encode sources).length < TranscriptFrame.lengthLimit →
        (NativeLookupMultiplicityWire.grouped ctx.proof.multiplicities).length < TranscriptFrame.lengthLimit →
        (NativeLookupMultiplicityWire.flattened ctx.proof.multiplicities).length < TranscriptFrame.lengthLimit →
        ∀ slot : Fin ctx.registry.val.length, ∃ position, NativeSeedAncestry.Realized world history (LookupScalarSeedQuote.forkInput ctx world) position
          (.source (AllocatedLookupFrontier.sourceKey (ctx := ctx) (world := world) slot)) := by
  have native := native_execution entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase
  obtain ⟨sources,computed,ancestry⟩ := NativeRegistryAncestry.bound_registered_sources NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world lookup.body native.1
  refine ⟨sources,computed,?_⟩
  intro frames bytes valid registryFits groupedFits flatFits slot
  obtain ⟨key,keyAt,context,root⟩ := NativeRegistryAncestry.contexts_slot NativeGoldBlockCode.description.row ctx.registry.val world sources.val computed slot
  rw [GoldContextCollision.context_run] at context
  have digest := Option.some.inj context
  have same : key = AllocatedLookupFrontier.sourceKey (ctx := ctx) (world := world) slot := Prod.ext digest.symm root
  obtain ⟨position,realized⟩ := ancestry frames bytes valid registryFits groupedFits flatFits key (List.mem_of_getElem? keyAt)
  rw [same] at realized
  exact SeedAncestryEmbedding.realized_sublist (native.2.trans observed) realized

/-- An original canonical helper binding supplies the helper fact through the
actual initializer segment. Its observation log is recovered from the same
allocated run, rather than supplied separately. -/
theorem helper_from_binding (history : List Observation)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist history)
    (frames : List TranscriptFrame.Frame)
    (bytes : (run (NativeSharedLookupParent.prepare NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests) world).run.1.1.input =
      TranscriptFrame.encodeMany frames)
    (valid : ∀ frame ∈ frames, TranscriptFrame.Valid frame)
    (groupedFits : (NativeLookupMultiplicityWire.grouped ctx.proof.multiplicities).length < TranscriptFrame.lengthLimit)
    (flatFits : (NativeLookupMultiplicityWire.flattened ctx.proof.multiplicities).length < TranscriptFrame.lengthLimit)
    (binding : NativeCanonicalLookupWire.Binding)
    (bound : (⟨1,NativeCanonicalLookupWire.label,NativeCanonicalLookupWire.payload binding⟩ : TranscriptFrame.Frame) ∈ frames)
    (helper : binding.helper = InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper)) :
    ∃ position, NativeSeedAncestry.Realized world history (LookupScalarSeedQuote.forkInput ctx world) position
      (.helper (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper))) := by
  have native := native_execution entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase
  have start := NativeRegistryAncestry.bound_start NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world lookup.body native.1
  have fact := NativeForkAncestry.start_helper world history _ frames ctx.proof.multiplicities bytes valid groupedFits flatFits
    (start.trans (native.2.trans observed)) binding bound
  simpa only [helper,LookupScalarSeedQuote.forkInput] using fact

end
end FormalProof4FHE.HasteBoots.AllocatedRegistrySeed
