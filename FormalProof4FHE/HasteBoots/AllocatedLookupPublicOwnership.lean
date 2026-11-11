module
public import FormalProof4FHE.HasteBoots.AllocatedLookupExecution
public import FormalProof4FHE.HasteBoots.LookupSourcePublicOwnership
public import FormalProof4FHE.HasteBoots.HelperPublicOwnership
@[expose] public section

/-! Actual execution of the allocated lookup entry point derives both source
and helper public-table ownership. Source collection and helper borrowing
are execution conclusions, not independent context-association certificates. -/
namespace FormalProof4FHE.HasteBoots.AllocatedLookupPublicOwnership
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

variable {Memory : Type} (entries : List Entry) (reachable : NativeGoldParameterStore.Reachable entries)
    (helperHandle : ℕ) (references : Vector Reference) (template : Context (Vector Opening))
    (chooseHelper : NativeGoldPcsProgram.Scheduler Memory) (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory)
    (memory : Memory) (world : World) (ctx : Context (Vector Opening)) (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 =
      .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory)
    (phase : result.phase = .batches lookup progress (.verification (.done after)))

include executed

theorem assembled : AllocatedLookupContext.assemble entries helperHandle references template = some ctx :=
  (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).1

include phase

theorem native_phase : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.1.phase =
    .batches lookup progress (.verification (.done after)) :=
  (congrArg (fun outcome : NativeGoldLookupVerification.Outcome Memory => outcome.phase)
    (AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed).2.1).trans phase

theorem helpers_done : (run (NativeGoldHelperVerification.program ctx chooseHelper memory) world).run.1 =
    .helpers lookup.body lookup.plan (.done lookup.helpers) := by
  have prepared := (NativeGoldLookupVerification.program_batches_origin ctx chooseHelper chooseBatch memory world lookup progress
    (.verification (.done after)) (native_phase entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase)).1
  have packet := congrArg Prod.fst (NativeGoldLookupVerification.prepare_spec _ lookup prepared).1
  have erased := congrArg Prod.fst (NativeRegisteredLookup.helpers_erasure ctx chooseHelper memory world)
  exact erased.symm.trans packet

/-- All original checked helper ordinals inherit their actual allocated helper
object and proof roots directly from the assembled entry point. -/
theorem all_helpers_owned (dummy : Digest) (history : List Observation) : ∀ checked ∈ lookup.body.terminal.checked,
    HelperPublicOwnership.Owned ctx chooseHelper memory world lookup.body lookup.plan lookup.helpers
      (helpers_done entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase)
      entries reachable helperHandle dummy history checked := by
  have borrowed := (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx
    (assembled entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed)).2
  exact HelperPublicOwnership.all_checked_owned ctx chooseHelper memory world lookup.body lookup.plan lookup.helpers
    (helpers_done entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase)
    entries reachable helperHandle {template with registry := ctx.registry} borrowed dummy history

/-- The complete native log is unchanged by the logical allocation adapter.
All used original source slots share the existing one hash bad event. -/
theorem all_sources_owned_or_bad (dummy : Digest) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist history) :
    (∀ slot : Fin ctx.registry.val.length, NativeSharedSourceClaims.used ctx.requests slot = true →
      LookupSourcePublicOwnership.Owned ctx chooseHelper chooseBatch memory world lookup progress after
        (native_phase entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase)
        entries reachable references
        (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx
          (assembled entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed)).1 dummy history slot) ∨
      NativeRootFamilyLifetime.Bad dummy history := by
  have origin := AllocatedLookupExecution.verification_origin entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed
  have included : (run (NativeGoldLookupVerification.program ctx chooseHelper chooseBatch memory) world).run.2.Sublist history := by
    rw [← origin.2.2]
    exact observed
  exact LookupSourcePublicOwnership.all_sources_or_bad ctx chooseHelper chooseBatch memory world lookup progress after
    (native_phase entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase)
    entries reachable references (AllocatedLookupContext.assemble_spec entries helperHandle references template ctx origin.1).1
    dummy history truthful included

end
end FormalProof4FHE.HasteBoots.AllocatedLookupPublicOwnership
