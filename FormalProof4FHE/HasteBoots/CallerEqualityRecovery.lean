module
public import FormalProof4FHE.HasteBoots.CallerEqualityExposure
public import FormalProof4FHE.HasteBoots.CallerEqualityResidual
public import FormalProof4FHE.HasteBoots.EqualityLifetime
@[expose] public section

/-! Recover an attained adaptive equality event from the original caller's
actual nonzero residual missed by its stored native EQ point. Framing,
first exposure, endpoint factors and complete tables come from the same run. -/
namespace FormalProof4FHE.HasteBoots.CallerEqualityRecovery
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open OracleProgram (Program)
noncomputable section

theorem covered {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}
    (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (inputs : SequencedCallerInputs.Inputs data) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame) (dummy : NativeRootMessage.Digest)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (missed : LookupInitialArithmetic.EqualityMiss data dummy) : EqualityLifetime.Event program dummy world := by
  obtain ⟨draw,drawAt,evidence⟩ := data.job.equality
  have positive : 0 < data.origin.geometry.geometry.1.val := by
    rw [data.job.view.dimension]
    exact CallerEqualityResidual.positive (LookupInitialArithmetic.residual data dummy) _ missed
  obtain ⟨first⟩ := CallerEqualityExposure.first data draw (List.mem_of_getElem? drawAt) positive
  let framing := CallerPairedPreparation.framing data inputs helperWidth sourceWidths before bytes valid
  obtain ⟨recovered⟩ := CallerEqualityFamily.recover data draw (List.mem_of_getElem? drawAt) first framing safe before bytes valid inputs.parent_domain
  let family := CallerEqualityFamily.candidate data draw first drawAt recovered
  have native := CallerEqualityFamily.native data
  obtain ⟨candidate,named⟩ := EqualityFactorCandidate.attach family native.1 native.2
  have tested := CallerEqualityResidual.test data draw first drawAt recovered candidate named evidence dummy safe missed
  have event := EqualityCandidateKernel.of_test candidate dummy tested
  exact ⟨first.position,candidate.family.selection.family.input,candidate.family.selection.index.val,
    ⟨⟨candidate,rfl,rfl⟩,event⟩⟩

end
end FormalProof4FHE.HasteBoots.CallerEqualityRecovery
