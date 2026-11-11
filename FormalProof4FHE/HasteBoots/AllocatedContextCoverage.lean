module
public import FormalProof4FHE.HasteBoots.GoldContextCoverage
@[expose] public section

/-! Actual allocated execution supplies the complete context observations;
chronological source/helper naming moves them into a chosen old prefix or
the single bounded late-context target ledger. -/
namespace FormalProof4FHE.HasteBoots.AllocatedContextCoverage
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (Input World)
open OracleProgram (Program run runPrefix)
noncomputable section

variable {Memory A : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (ctx : Context (Vector Opening)) (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory)
    (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (program : Program A)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist (run program world).run.2)

include executed phase observed

theorem full :
    (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.helper) world).run.2.Sublist (run program world).run.2 ∧
    ∀ slot : Fin ctx.registry.val.length,
      (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row (ctx.registry.val.get slot).parameters) world).run.2.Sublist (run program world).run.2 := by
  have native := AllocatedRegistrySeed.native_execution entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase
  have contained := native.2.trans observed
  constructor
  · exact (RegistryContextObservation.helper_protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
      ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world lookup.body native.1).trans contained
  · intro slot
    exact (RegistryContextObservation.protocol NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
      ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world lookup.body native.1 _ (List.get_mem _ _)).trans contained

theorem source (position : ℕ) (input : Input) (slot : Fin ctx.registry.val.length)
    (known : NativeSourceLineage.Known world (runPrefix position program world).run.2 input
      (AllocatedLookupFrontier.sourceKey (ctx := ctx) (world := world) slot)) :
    (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row (ctx.registry.val.get slot).parameters) world).run.2.Sublist
      (runPrefix position program world).run.2 ∨ ProgramContextTarget.Bad program world := by
  have covered := full entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase program observed
  apply GoldContextCoverage.source program world position input _ _ known _ (covered.2 slot)
  rw [GoldContextCollision.context_run]
  rfl

theorem helper (position : ℕ) (input : Input)
    (known : NativeParentLineage.Known world (runPrefix position program world).run.2 input
      (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper))) :
    (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.helper) world).run.2.Sublist
      (runPrefix position program world).run.2 ∨ ProgramContextTarget.Bad program world := by
  have covered := full entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase program observed
  apply GoldContextCoverage.helper program world position input _ _ known _ covered.1
  rw [GoldContextCollision.context_run]


/-- A chronologically known actual parent covers every original context
outside one late-target event, with no per-slot union or extra certificate
that each parameter hash was already observed. -/
theorem all_contexts (position : ℕ) (framing : AllocatedLookupReadStability.Framing ctx world)
    (known : NativeParentLineage.Known world (runPrefix position program world).run.2 (LookupScalarSeedQuote.forkInput ctx world)
      (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper))) :
    ((run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.helper) world).run.2.Sublist
        (runPrefix position program world).run.2 ∧
      ∀ slot : Fin ctx.registry.val.length,
        (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row (ctx.registry.val.get slot).parameters) world).run.2.Sublist
          (runPrefix position program world).run.2) ∨ ProgramContextTarget.Bad program world := by
  by_cases bad : ProgramContextTarget.Bad program world
  · exact Or.inr bad
  · apply Or.inl
    have full := full entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase program observed
    refine ⟨(helper entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase
      program observed position _ known).resolve_right bad,?_⟩
    obtain ⟨view,parsed,_,computed,_,_⟩ := AllocatedParentData.recover entries helperHandle references template chooseHelper chooseBatch memory
      result executed lookup progress after phase framing
    intro slot
    obtain ⟨source,found,context,_⟩ := OriginalSharedParent.slot NativeGoldBlockCode.description.row ctx.registry world view computed slot
    have named := GoldContextCoverage.registry_named program world position _ _ known view parsed source (List.mem_of_getElem? found)
    exact (ProgramContextTarget.context_observed_or_bad program world position _ source.1 context (full.2 slot) named).resolve_right bad

end
end FormalProof4FHE.HasteBoots.AllocatedContextCoverage
