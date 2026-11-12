module
public import FormalProof4FHE.HasteBoots.EqualityInputFamilyView
public import FormalProof4FHE.HasteBoots.ParentMatchFixation
public import FormalProof4FHE.HasteBoots.AllocatedScalarExposure
@[expose] public section

/-! Original equality first reads recover the caller's named helper parent
before exposure, using the same seed-order argument and original full run. -/
namespace FormalProof4FHE.HasteBoots.AllocatedEqualityParentPrefix
open NativeGoldParameterStore (Entry Reference)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeGoldHelperVerification (Context)
open InputIndexedOracle (World)
open OracleProgram (Program run runPrefix)
noncomputable section
variable {ctx : Context (Vector Opening)} {world : World}

theorem known {Memory A : Type} (entries : List Entry) (helperHandle : ℕ) (references : Vector Reference)
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
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    NativeSeedAncestry.Known world (runPrefix first.position program world).run.2 (LookupScalarSeedQuote.forkInput ctx world)
      (.helper (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper))) := by
  have ancestry := AllocatedRegistrySeed.helper_from_binding entries helperHandle references template chooseHelper chooseBatch memory world ctx result executed
    lookup progress after phase (run program world).run.2 observed framing.parentFrames framing.parentBytes framing.parentValid framing.groupedFits framing.flatFits
    framing.binding framing.bound framing.helper
  obtain ⟨parentPosition,realized⟩ := ancestry
  obtain ⟨fuel,completed⟩ := OracleProgramMachine.complete program world
  have logs := congrArg Prod.snd completed
  have actual : NativeSeedAncestry.Realized world (run (OracleMachine.take OracleProgramMachine.step fuel program) world).run.2
      (LookupScalarSeedQuote.forkInput ctx world) parentPosition (.helper (InputIndexedOracle.sha512 world (GoldContextInput.bytes ctx.helper))) := by
    rw [logs]
    exact realized
  have positive : InputIndexedOracle.bytes world draw.coefficients.phase.pending.input first.offset first.count ≠ [] := by
    simpa only [ne_eq,← List.length_eq_zero_iff,InputIndexedOracle.bytes_length] using Nat.ne_of_gt first.positive
  have quoted : NativeChildSeedView.candidate (.output draw.coefficients.phase.pending.input first.offset
      (InputIndexedOracle.bytes world draw.coefficients.phase.pending.input first.offset first.count)) =
      some (InputIndexedOracle.block world (LookupScalarSeedQuote.forkInput ctx world) 0 64) := by
    simp only [NativeChildSeedView.candidate,positive,ite_false]
    exact (EqualityInputFamilyView.recover origin rootsFit draw member).2
  have earlier := actual.before_quote OracleProgramMachine.step fuel program world safe first.position _
    (by rw [logs]; exact first.outputAt) quoted
  rw [logs,← first.history] at earlier
  exact earlier

end
end FormalProof4FHE.HasteBoots.AllocatedEqualityParentPrefix
