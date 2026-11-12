module
public import FormalProof4FHE.HasteBoots.LookupAssemblyScope
@[expose] public section

/-! The real rebuilt-entry-point adapter uses one original assembly scope.
Successful execution recovers its dynamic view and trusted profile directly. -/
namespace FormalProof4FHE.HasteBoots.ScopedRebuiltLookup
open LookupAssemblyScope (Scope View)
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeLookupRequestWire (Request)
open NativeGoldBatchOpening (Opening)
open NativeSharedLookupValues (Policy)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

def program {Memory : Type} (scope : Scope) (policy : Policy) (original : Vector Request)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) :=
  RebuiltLookupExecution.program policy original scope.allocation.entries scope.allocation.helperHandle scope.allocation.references
    template chooseHelper chooseBatch memory

theorem recover {Memory : Type} (scope : Scope) (policy : Policy) (original : Vector Request)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory) (world : World)
    (ctx : Context (Vector Opening)) (result : NativeGoldLookupVerification.Outcome Memory)
    (profile : template.parent.profile = scope.anchor.parent.profile)
    (executed : (run (program scope policy original template chooseHelper chooseBatch memory) world).run.1 = .allocated (.verification ctx result)) :
    ∃ view : View scope, view.ctx = ctx ∧
      ∃ rebuilt, LookupRequestRebuild.rebuild policy original = some rebuilt ∧ view.template = {template with requests := rebuilt} := by
  obtain ⟨rebuilt,built,native,_,_,_⟩ := RebuiltLookupExecution.verification_origin policy original scope.allocation.entries
    scope.allocation.helperHandle scope.allocation.references template chooseHelper chooseBatch memory world ctx result executed
  have assembled := (AllocatedLookupExecution.verification_origin scope.allocation.entries scope.allocation.helperHandle scope.allocation.references
    {template with requests := rebuilt} chooseHelper chooseBatch memory world ctx result native).1
  have same := Option.some.inj (assembled.symm.trans (LookupAssemblyScope.retemplate scope {template with requests := rebuilt}))
  have trusted : ctx.parent.profile = scope.anchor.parent.profile := by rw [same]; exact profile
  exact ⟨⟨ctx,{template with requests := rebuilt},assembled,trusted⟩,rfl,rebuilt,built,rfl⟩

end
end FormalProof4FHE.HasteBoots.ScopedRebuiltLookup
