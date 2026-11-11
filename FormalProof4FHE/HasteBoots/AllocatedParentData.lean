module
public import FormalProof4FHE.HasteBoots.OriginalSharedParent
@[expose] public section

/-! Actual allocated verification supplies the strict parent-input view and
its full original registry. No parsed source vector or registration-success
certificate is supplied independently. -/
namespace FormalProof4FHE.HasteBoots.AllocatedParentData
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (World)
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
    (framing : AllocatedLookupReadStability.Framing ctx world) :
    ∃ view : SharedParentInputView.View,
      SharedParentInputView.parse (LookupScalarSeedQuote.forkInput ctx world) = some view ∧
      view.before = framing.preflightFrames ∧
      (run (NativeSharedLookupParent.contexts NativeGoldBlockCode.description.row ctx.registry.val) world).run.1 = some view.sources.val ∧
      view.grouped = NativeLookupMultiplicityWire.grouped ctx.proof.multiplicities ∧
      view.flat = NativeLookupMultiplicityWire.flattened ctx.proof.multiplicities := by
  have native := AllocatedRegistrySeed.native_execution entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed lookup progress after phase
  exact OriginalSharedParent.recover NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof
    ctx.lookupFuel ctx.equalityFuel ctx.scalarFuel world lookup.body native.1 framing.preflightFrames framing.preflightBytes framing.preflightValid
    framing.registryFits framing.groupedFits framing.flatFits

end
end FormalProof4FHE.HasteBoots.AllocatedParentData
