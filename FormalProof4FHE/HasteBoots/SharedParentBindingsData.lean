module
public import FormalProof4FHE.HasteBoots.AllocatedBindingsData
public import FormalProof4FHE.HasteBoots.ParentBindingSlots
@[expose] public section

/-! The actual allocated parent view and canonical binding view share the
same native preflight bytes. Matching parents therefore fixes the original
request vector and all per-request binding records together. -/
namespace FormalProof4FHE.HasteBoots.SharedParentBindingsData
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (Input World)
open OracleProgram (run)
noncomputable section
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
    (domain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests)
    (framing : AllocatedLookupReadStability.Framing ctx world) :
    ∃ parentView : SharedParentInputView.View, ∃ bindingView : ParentBindingsView.View,
      SharedParentInputView.parse (LookupScalarSeedQuote.forkInput ctx world) = some parentView ∧
      ParentBindingsView.parse (TranscriptFrame.encodeMany parentView.before) = some bindingView ∧
      (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some parentView.sources.val ∧
      bindingView.requests = ctx.requests ∧
      List.Forall₂ (ParentBindingTrace.ForRequest NativeGoldBlockCode.description.row ctx.registry.val ctx.helper world) ctx.requests.val bindingView.bindings := by
  obtain ⟨parentView,parentParsed,parentBefore,contexts,_,_⟩ := AllocatedParentData.recover entries helperHandle references template chooseHelper chooseBatch memory
    result executed lookup progress after phase framing
  obtain ⟨bindingView,bindingParsed,_,requests,relations⟩ := AllocatedBindingsData.recover entries helperHandle references template chooseHelper chooseBatch memory
    result executed lookup progress after phase before bytes valid domain
  rw [framing.preflightBytes,← parentBefore] at bindingParsed
  exact ⟨parentView,bindingView,parentParsed,bindingParsed,contexts,requests,relations⟩

/-- A shared decoded parent prefix fixes the entire literal request vector
and binding sequence, including all original source-slot addresses. -/
theorem bindings_equal (left right : SharedParentInputView.View) (leftBindings rightBindings : ParentBindingsView.View)
    (leftParsed : ParentBindingsView.parse (TranscriptFrame.encodeMany left.before) = some leftBindings)
    (rightParsed : ParentBindingsView.parse (TranscriptFrame.encodeMany right.before) = some rightBindings)
    (same : left = right) : leftBindings = rightBindings := by
  rw [same] at leftParsed
  exact Option.some.inj (leftParsed.symm.trans rightParsed)

/-- Matching parent seeds fixes both decoded views, with the existing lifetime collision exception. -/
theorem compare_on_fiber {A : Type} (program : OracleProgram.Program A) (position : ℕ) (world other : World)
    (input leftInput rightInput : Input) (left right : SharedParentInputView.View)
    (leftContext rightContext : NativeRootMessage.Digest)
    (leftKnown : NativeParentLineage.Known world (OracleProgram.runPrefix position program world).run.2 leftInput leftContext)
    (rightKnown : NativeParentLineage.Known other (OracleProgram.runPrefix position program other).run.2 rightInput rightContext)
    (leftParsed : SharedParentInputView.parse leftInput = some left)
    (rightParsed : SharedParentInputView.parse rightInput = some right)
    (leftQuote : NativeChildSeedView.quote input = some (InputIndexedOracle.block world leftInput 0 64))
    (rightQuote : NativeChildSeedView.quote input = some (InputIndexedOracle.block other rightInput 0 64))
    (leftBindings rightBindings : ParentBindingsView.View)
    (leftBindingParsed : ParentBindingsView.parse (TranscriptFrame.encodeMany left.before) = some leftBindings)
    (rightBindingParsed : ParentBindingsView.parse (TranscriptFrame.encodeMany right.before) = some rightBindings)
    (same : (ParentFactorFiber.extend (OracleProgram.runPrefix position program) other).run =
      (ParentFactorFiber.extend (OracleProgram.runPrefix position program) world).run) :
    (left = right ∧ leftBindings = rightBindings) ∨ ProgramParentSeedCollision.Bad program world := by
  rcases OriginalSharedParent.compare_on_fiber program position world other input leftInput rightInput left right leftContext rightContext
      leftKnown rightKnown leftParsed rightParsed leftQuote rightQuote same with equal | bad
  · exact Or.inl ⟨equal,bindings_equal left right leftBindings rightBindings leftBindingParsed rightBindingParsed equal⟩
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.SharedParentBindingsData
