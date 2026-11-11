module
public import FormalProof4FHE.HasteBoots.AllocatedContextCoverage
@[expose] public section

/-! Actual allocated scalar first-read placement derives prior observation
of every original parameter context outside the bounded late-context target
ledger. Native domains and the existing seed-order exception remain explicit. -/
namespace FormalProof4FHE.HasteBoots.AllocatedFirstContextCoverage
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (World)
open OracleProgram (Program run runPrefix)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World}

theorem at_scalar_first {Memory A : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (statementFits : (NativeScalarBatchWire.statementCodec.encode origin.ready.statement).length < TranscriptFrame.lengthLimit)
    (domain : NativeScalarTranscriptExtension.RoundDomain ctx.proof.algebra)
    (entry : NativeScalarBatchVerifier.CompletedRound)
    (member : entry ∈ (NativeScalarBatchVerifier.execute origin.ready.statement ctx.proof.algebra ctx.scalarFuel
      (NativeScalarBatchVerifier.initial origin.ready.equality.transcript origin.ready.statement ctx.proof.algebra) world).1.completed)
    (program : Program A)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist
      (run program world).run.2)
    (framing : AllocatedLookupReadStability.Framing ctx world)
    (first : ProgramFirstStreamRead.First program world entry.coefficients.phase.pending.input)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    ((run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.helper) world).run.2.Sublist
        (runPrefix first.position program world).run.2 ∧
      ∀ slot : Fin ctx.registry.val.length,
        (run (NativeBrakedownContext.context NativeGoldBlockCode.description.row (ctx.registry.val.get slot).parameters) world).run.2.Sublist
          (runPrefix first.position program world).run.2) ∨ ProgramContextTarget.Bad program world := by
  have known := AllocatedParentPrefix.known entries helperHandle references template chooseHelper chooseBatch memory result executed
    lookup progress after phase origin rootsFit statementFits domain entry member program observed framing first safe
  exact AllocatedContextCoverage.all_contexts entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed
    lookup progress after phase program observed first.position framing known

end
end FormalProof4FHE.HasteBoots.AllocatedFirstContextCoverage
