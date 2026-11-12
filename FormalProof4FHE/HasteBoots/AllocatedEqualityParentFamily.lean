module
public import FormalProof4FHE.HasteBoots.OriginalScalarFamily
public import FormalProof4FHE.HasteBoots.AllocatedParentFamily
public import FormalProof4FHE.HasteBoots.AllocatedEqualityParentPrefix
@[expose] public section

/-! The original allocated parent family is recovered at equality first
reads, before any scalar-reader receipt or sumcheck metadata is needed. -/
namespace FormalProof4FHE.HasteBoots.AllocatedEqualityParentFamily
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (World)
open OracleProgram (Program run runPrefix)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World}

theorem at_equality_first {Memory A : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (draw : NativeLookupEquality.Draw origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3)
    (member : draw ∈ origin.ready.machine.draws)
    (program : Program A)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist
      (run program world).run.2)
    (framing : AllocatedLookupReadStability.Framing ctx world)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests) :
    ∃ family : OriginalParentFamily.Family program first.position world,
      family.registry = ctx.registry ∧ family.helper = ctx.helper ∧ family.requests = ctx.requests ∧
        family.input = LookupScalarSeedQuote.forkInput ctx world := by
  have known := AllocatedEqualityParentPrefix.known entries helperHandle references template chooseHelper chooseBatch memory result executed
    lookup progress after phase origin rootsFit draw member program observed framing first safe
  exact AllocatedParentFamily.recover entries helperHandle references template chooseHelper chooseBatch memory result executed lookup progress after phase
    before bytes valid parentDomain program first.position observed known framing

/-- The complete ordered helper-root family is available at the same original
equality read, without a later scalar-input or equality-receipt premise. -/
theorem with_roots {Memory A : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
    (template : Context (Vector Opening)) (chooseHelper : NativeGoldPcsProgram.Scheduler Memory)
    (chooseBatch : NativeGoldBatchPcsProgram.Scheduler Memory) (memory : Memory)
    (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.1 = .verification ctx result)
    (lookup : NativeGoldLookupVerification.Prepared Memory) (progress : NativeSharedSourceClaims.Progress)
    (after : NativeDeferredBatchVerification.Progress Memory) (phase : result.phase = .batches lookup progress (.verification (.done after)))
    (origin : AllocatedLookupIdentity.NativeOrigin ctx world lookup.body)
    (rootsFit : (NativeRootMessage.encode ctx.proof.roots.val ctx.proof.roots.property).length < TranscriptFrame.lengthLimit)
    (draw : NativeLookupEquality.Draw origin.geometry.geometry.1.val NativeExtensionFields.Goldilocks3)
    (member : draw ∈ origin.ready.machine.draws)
    (program : Program A)
    (observed : (run (AllocatedLookupExecution.program entries helperHandle references template chooseHelper chooseBatch memory) world).run.2.Sublist
      (run program world).run.2)
    (framing : AllocatedLookupReadStability.Framing ctx world)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (parentDomain : NativeLookupParentFraming.Domain ctx.registry.val ctx.requests) :
    ∃ family : OriginalScalarFamily.Family program first.position world,
      family.parent.registry = ctx.registry ∧ family.parent.helper = ctx.helper ∧ family.parent.requests = ctx.requests ∧
        family.input = draw.coefficients.phase.pending.input ∧ family.roots = ctx.proof.roots := by
  obtain ⟨parent,registry,helper,requests,input⟩ := at_equality_first entries helperHandle references template chooseHelper chooseBatch memory
    result executed lookup progress after phase origin rootsFit draw member program observed framing first safe before bytes valid parentDomain
  have recovered := EqualityInputFamilyView.recover origin rootsFit draw member
  let family : OriginalScalarFamily.Family program first.position world :=
    ⟨parent,draw.coefficients.phase.pending.input,ctx.proof.roots,recovered.1,by rw [input]; exact recovered.2⟩
  exact ⟨family,registry,helper,requests,rfl,rfl⟩

end
end FormalProof4FHE.HasteBoots.AllocatedEqualityParentFamily
