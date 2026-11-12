module
public import FormalProof4FHE.HasteBoots.CallerLookupClassCoverage
public import FormalProof4FHE.HasteBoots.OffsetLifetimeWork
@[expose] public section

/-! Actual caller reciprocal misses reach the lifetime event aggregating all stream
inputs, original jobs, first-read positions and degree classes, priced by work. -/
namespace FormalProof4FHE.HasteBoots.CallerOffsetWorkCoverage
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
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
      OffsetLifetimeWork.Event program dummy world := by
  rcases CallerLookupClassCoverage.reciprocal data policy original template result executed inputs helperWidth sourceWidths before bytes valid dummy miss with
    seed | reference | ⟨position,input,ordinal,cost,⟨⟨packet,event⟩,_⟩⟩
  · exact Or.inl seed
  · exact Or.inr (Or.inl reference)
  · exact Or.inr (Or.inr ⟨position,input,ordinal,cost,packet,event⟩)

theorem nonmember (bad : RebuiltCallerLookupCoverage.Nonmember data dummy) :
    Nonempty (LookupInitialPairedWork.Witness (Memory := Memory) ctx allocation program dummy world) ∨
      SeedQuoteOrder.Bad OracleProgramMachine.step program world ∨ GlobalReferenceBad.Bad program dummy world ∨
      (∃ position input ordinal cost, CompressionClassKernel.SafeEvent program position input ordinal cost dummy world) ∨
      (OffsetLifetimeWork.Event program dummy world) := by
  rcases CallerLookupClassCoverage.nonmember data policy original template result executed inputs helperWidth sourceWidths before bytes valid dummy bad with
    arithmetic | seed | reference | compression | ⟨position,input,ordinal,cost,⟨⟨packet,event⟩,_⟩⟩
  · exact Or.inl arithmetic
  · exact Or.inr (Or.inl seed)
  · exact Or.inr (Or.inr (Or.inl reference))
  · exact Or.inr (Or.inr (Or.inr (Or.inl compression)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨position,input,ordinal,cost,packet,event⟩)))

end
end FormalProof4FHE.HasteBoots.CallerOffsetWorkCoverage
