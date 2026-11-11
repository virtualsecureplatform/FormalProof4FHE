module
public import FormalProof4FHE.HasteBoots.OriginalScalarFamily
@[expose] public section

/-! Actual allocated scalar first-read execution supplies both the original
parent family and complete helper-root vector at their literal scalar input. -/
namespace FormalProof4FHE.HasteBoots.AllocatedScalarFamily
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
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests) :
    ∃ family : OriginalScalarFamily.Family program first.position world,
      family.parent.registry = ctx.registry ∧ family.parent.helper = ctx.helper ∧ family.parent.requests = ctx.requests ∧
        family.parent.input = LookupScalarSeedQuote.forkInput ctx world ∧ family.roots = ctx.proof.roots ∧
          family.input = entry.coefficients.phase.pending.input := by
  obtain ⟨parent,registry,helper,requests,parentInput⟩ := AllocatedFirstParentFamily.at_scalar_first entries helperHandle references template
    chooseHelper chooseBatch memory result executed lookup progress after phase origin rootsFit statementFits domain entry member program observed framing first safe
    before bytes valid parentDomain
  have quoted := LookupScalarSeedQuote.completed_quote origin rootsFit statementFits domain entry member
  rw [← parentInput] at quoted
  exact ⟨⟨parent,entry.coefficients.phase.pending.input,ctx.proof.roots,
    OriginalHelperRoots.completed_roots origin rootsFit statementFits domain entry member,quoted⟩,
    registry,helper,requests,parentInput,rfl,rfl⟩

end
end FormalProof4FHE.HasteBoots.AllocatedScalarFamily
