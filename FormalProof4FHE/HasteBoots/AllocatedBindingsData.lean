module
public import FormalProof4FHE.HasteBoots.OriginalParentBindings
public import FormalProof4FHE.HasteBoots.AllocatedParentData
@[expose] public section

/-! Actual allocated success supplies the original per-request canonical
bindings. Native frame allocation and the caller's original framed parent
remain explicit; no parser-produced binding is treated as ownership alone. -/
namespace FormalProof4FHE.HasteBoots.AllocatedBindingsData
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem preflight_of_prepare {C : Type} (row : NativeBrakedownContext.RowDescription C)
    (registry : Vector (NativeSharedLookupParent.Oracle C)) (helper : NativeBrakedownContext.Parameters C)
    (parent : NativeTranscript.Transcript) (requests : Vector NativeLookupRequestWire.Request) (world : World)
    (output : NativeSharedLookupPreflight.Output)
    (success : (run (NativeSharedLookupParent.prepare row registry helper parent requests) world).run.1.2 = some output) :
    (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.2 = some output := by
  simp only [NativeSharedLookupParent.prepare,OracleProgram.run_bind,ObservationReplay.run_bind] at success
  cases pref : (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.2 with
  | none => simp only [pref,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
  | some result =>
    simp only [pref,OracleProgram.run_bind,ObservationReplay.run_bind] at success
    cases registered : (run (NativeSharedLookupParent.register row registry
      (run (NativeSharedLookupParent.preflight row registry.val helper parent requests) world).run.1.1) world).run.1 with
    | none => simp only [registered,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success; contradiction
    | some finalParent =>
      simp only [registered,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at success
      obtain rfl := Option.some.inj success
      rfl

variable {ctx : Context (Vector Opening)} {world : World}

theorem recover {Memory : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (domain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests) :
    ∃ view : ParentBindingsView.View,
      ParentBindingsView.parse (run (NativeSharedLookupParent.preflight NativeGoldBlockCode.description.row ctx.registry.val ctx.helper ctx.parent ctx.requests) world).run.1.1.input = some view ∧
      view.before = before ∧ view.requests = ctx.requests ∧
      List.Forall₂ (ParentBindingTrace.ForRequest NativeGoldBlockCode.description.row ctx.registry.val ctx.helper world) ctx.requests.val view.bindings := by
  have native := AllocatedRegistrySeed.native_execution entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase
  obtain ⟨geometry,launched,began,_,_,_⟩ := NativeSharedLookupExecution.bound_origin NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world lookup.body native.1
  obtain ⟨g,l,_,prepared,_,_⟩ := NativeSharedLookupParent.begin_spec NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel world _ began
  exact OriginalParentBindings.recover NativeGoldBlockCode.description.row ctx.registry.val ctx.helper ctx.parent ctx.requests world g
    (preflight_of_prepare _ _ _ _ _ _ g prepared) before bytes valid domain

end
end FormalProof4FHE.HasteBoots.AllocatedBindingsData
