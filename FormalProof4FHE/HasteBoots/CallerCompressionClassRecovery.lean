module
public import FormalProof4FHE.HasteBoots.CallerCompressionRecovery
public import FormalProof4FHE.HasteBoots.CompressionContinuation
@[expose] public section

/-! Actual original caller compression misses enter attained adaptive
classes with their exact request complexity. The existing shared seed-order
and reference bad alternatives remain explicit and are not charged per class. -/
namespace FormalProof4FHE.HasteBoots.CallerCompressionClassRecovery
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open OracleProgram (Program)
noncomputable section

theorem covered {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}
    (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (inputs : SequencedCallerInputs.Inputs data) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame) (dummy : Digest)
    (collision : CallerCompressionRecovery.Collision data dummy) :
    SeedQuoteOrder.Bad OracleProgramMachine.step program world ∨ GlobalReferenceBad.Bad program dummy world ∨
      ∃ position input ordinal cost, CompressionClassKernel.SafeEvent program position input ordinal cost dummy world := by
  by_cases ordered : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world
  · right
    by_cases safe : ¬GlobalReferenceBad.Bad program dummy world
    · right
      obtain ⟨position,candidate,_,_,occurred⟩ := CallerCompressionRecovery.recover data inputs helperWidth sourceWidths before bytes valid dummy ordered collision
      obtain ⟨position,input,ordinal,cost,event⟩ := CompressionClassKernel.of_candidate candidate dummy occurred
      exact ⟨position,input,ordinal,cost,event,safe⟩
    · exact Or.inl (not_not.mp safe)
  · exact Or.inl (not_not.mp ordered)

end
end FormalProof4FHE.HasteBoots.CallerCompressionClassRecovery
