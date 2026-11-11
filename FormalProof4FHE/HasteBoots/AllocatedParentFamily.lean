module
public import FormalProof4FHE.HasteBoots.OriginalParentFamily
@[expose] public section

/-! The original family package is constructed from actual allocated success,
original caller framing and native allocation domains. No family equality or
per-slot old observation certificate is supplied. -/
namespace FormalProof4FHE.HasteBoots.AllocatedParentFamily
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World}

/-- Numeric preflight cannot succeed without an original request. -/
theorem preflight_nonempty (registry : List NativeLookupBindGeometry.Parameters) (helper : NativeLookupBindGeometry.Parameters)
    (requests : List NativeSharedLookupStatement.Request) (geometry : NativeSharedLookupPreflight.Output)
    (success : NativeSharedLookupPreflight.preflight registry helper requests = some geometry) : requests ≠ [] := by
  intro empty
  subst requests
  unfold NativeSharedLookupPreflight.preflight at success
  split at success <;> contradiction

theorem recover {Memory A : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (domain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (program : OracleProgram.Program A) (position : ℕ)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist
      (run program world).run.2)
    (known : NativeParentLineage.Known world (OracleProgram.runPrefix position program world).run.2 (LookupScalarSeedQuote.forkInput ctx world)
      (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper)))
    (framing : AllocatedLookupReadStability.Framing ctx world) :
    ∃ family : OriginalParentFamily.Family program position world,
      family.registry = ctx.registry ∧ family.helper = ctx.helper ∧ family.requests = ctx.requests ∧
        family.input = LookupScalarSeedQuote.forkInput ctx world := by
  obtain ⟨parent,bindings,parsed,bindingParsed,computed,requests,related⟩ := SharedParentBindingsData.recover entries helperHandle references template
    chooseHelper chooseBatch memory result executed lookup progress after phase before bytes valid domain framing
  have full := AllocatedContextCoverage.full entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed
    lookup progress after phase program observed
  have native := AllocatedRegistrySeed.native_execution entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed
    lookup progress after phase
  obtain ⟨geometry,launched,_,numeric,_,_⟩ := NativeSharedLookupExecution.bound_origin NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent
    ctx.requests ctx.proof ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world lookup.body native.1
  rw [NativeSharedLookupParent.models_list] at numeric
  have nonempty : ctx.requests.val ≠ [] := by
    intro empty
    have impossible := preflight_nonempty _ _ _ geometry numeric
    apply impossible
    rw [empty,List.map_nil]
  have bindingNonempty : bindings.bindings ≠ [] := by
    intro empty
    have length := related.length_eq
    rw [empty,List.length_nil] at length
    exact nonempty (List.eq_nil_of_length_eq_zero length)
  exact ⟨⟨ctx.registry,ctx.helper,ctx.requests,LookupScalarSeedQuote.forkInput ctx world,parent,bindings,known,parsed,bindingParsed,computed,requests,
    related,bindingNonempty,full.1,full.2⟩,rfl,rfl,rfl,rfl⟩

end
end FormalProof4FHE.HasteBoots.AllocatedParentFamily
