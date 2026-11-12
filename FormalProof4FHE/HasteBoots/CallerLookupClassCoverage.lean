module
public import FormalProof4FHE.HasteBoots.CallerLookupOffsetRecovery
public import FormalProof4FHE.HasteBoots.OffsetClassKernel
public import FormalProof4FHE.HasteBoots.CallerCompressionClassRecovery
@[expose] public section

/-! Actual rebuilt caller misses reach attained compression/reciprocal
classes. Original input domains derive all characteristic and row association
premises; shared seed-order/reference alternatives are retained once. -/
namespace FormalProof4FHE.HasteBoots.CallerLookupClassCoverage
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open OracleProgram (Program run)
noncomputable section

variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}
    (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (policy : NativeSharedLookupValues.Policy) (original : Vector NativeLookupRequestWire.Request)
    (template : Context (Vector Opening)) (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (RebuiltLookupExecution.program policy original allocation.entries allocation.helperHandle allocation.references template
      data.chooseHelper data.chooseBatch data.memory) world).run.1 = .allocated (.verification ctx result))
    (inputs : SequencedCallerInputs.Inputs data) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame) (dummy : Digest)
include executed inputs helperWidth sourceWidths bytes valid

theorem reciprocal (miss : RebuiltCallerLookupCoverage.ReciprocalMiss data dummy) :
    SeedQuoteOrder.Bad OracleProgramMachine.step program world ∨ GlobalReferenceBad.Bad program dummy world ∨
      ∃ position input ordinal cost, OffsetClassKernel.SafeEvent program position input ordinal cost dummy world := by
  by_cases ordered : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world
  · right
    by_cases safe : ¬GlobalReferenceBad.Bad program dummy world
    · right
      obtain ⟨draw,first,recovered,member,lastAt,event⟩ := CallerLookupOffsetRecovery.recover data dummy miss inputs helperWidth sourceWidths before bytes valid ordered
      let candidate := CallerLookupOffsetRecovery.candidate data draw member first recovered lastAt
      have small := RebuiltJobPublicGeometry.logical_lt_characteristic policy original allocation.entries allocation.helperHandle allocation.references template
        data.chooseHelper data.chooseBatch data.memory result executed data.origin data.index data.job
      obtain ⟨position,input,ordinal,cost,event⟩ := OffsetClassKernel.of_candidate candidate dummy small event
      exact ⟨position,input,ordinal,cost,event,safe⟩
    · exact Or.inl (not_not.mp safe)
  · exact Or.inl (not_not.mp ordered)

/-- Original public tuple nonmembership reaches the already priced arithmetic
witness or one of the two attained native challenge classes, modulo the same
shared lifetime bad events. No independent y/r or table/count witness enters. -/
theorem nonmember (bad : RebuiltCallerLookupCoverage.Nonmember data dummy) :
    Nonempty (LookupInitialPairedWork.Witness (Memory := Memory) ctx allocation program dummy world) ∨
      SeedQuoteOrder.Bad OracleProgramMachine.step program world ∨ GlobalReferenceBad.Bad program dummy world ∨
      (∃ position input ordinal cost, CompressionClassKernel.SafeEvent program position input ordinal cost dummy world) ∨
      (∃ position input ordinal cost, OffsetClassKernel.SafeEvent program position input ordinal cost dummy world) := by
  rcases RebuiltCallerLookupCoverage.nonmember_covered data policy original template result executed dummy inputs before bytes valid bad with
    arithmetic | compression | offset
  · exact Or.inl arithmetic
  · rcases CallerCompressionClassRecovery.covered data inputs helperWidth sourceWidths before bytes valid dummy compression with seed | reference | attained
    · exact Or.inr (Or.inl seed)
    · exact Or.inr (Or.inr (Or.inl reference))
    · exact Or.inr (Or.inr (Or.inr (Or.inl attained)))
  · rcases reciprocal data policy original template result executed inputs helperWidth sourceWidths before bytes valid dummy offset with seed | reference | attained
    · exact Or.inr (Or.inl seed)
    · exact Or.inr (Or.inr (Or.inl reference))
    · exact Or.inr (Or.inr (Or.inr (Or.inr attained)))

end
end FormalProof4FHE.HasteBoots.CallerLookupClassCoverage
