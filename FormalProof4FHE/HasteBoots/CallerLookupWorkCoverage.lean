module
public import FormalProof4FHE.HasteBoots.FirstCompressionLifetime
public import FormalProof4FHE.HasteBoots.CallerOffsetWorkCoverage
@[expose] public section

/-! Actual rebuilt caller nonmembership reaches work-priced original
compression/reciprocal lifetime events. Serialization and native rebuilding
derive the compression degree cap and literal first-draw association. -/
namespace FormalProof4FHE.HasteBoots.CallerLookupWorkCoverage
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

theorem recover_compression (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world)
    (collision : CallerCompressionRecovery.Collision data dummy) : FirstCompressionLifetime.Event program dummy world := by
  obtain ⟨draw,_,drawAt,_,decoded,_⟩ := LookupProducedEndpoints.draws _ _ _ _ data.job.view.produced
  have member : draw ∈ data.job.view.producer.selection.draws := List.mem_of_mem_head? (by rw [drawAt]; rfl)
  obtain ⟨first,⟨recovered⟩⟩ := CallerLookupSourceRecovery.recover_first data draw member inputs helperWidth sourceWidths before bytes valid safe
  let base := CallerLookupSourceRecovery.candidate data draw member first recovered
  obtain ⟨_,_,_,_,requestsValid,_⟩ := RebuiltLookupExecution.verification_origin policy original allocation.entries allocation.helperHandle allocation.references template
    data.chooseHelper data.chooseBatch data.memory world ctx result executed
  have bounded := FirstCompressionCandidate.budget_of_payload base requestsValid inputs.parent_domain.1
  let candidate : FirstCompressionCandidate.Candidate program first.position world := ⟨base,drawAt,bounded⟩
  have value : base.draw.value = NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y :=
    (LookupCompressionKernel.draw_value base).trans (LookupScalarKernel.decoded_value draw.coefficients _ decoded).symm
  have tested : LookupTupleTest.test base dummy base.draw.value := by
    rw [LookupTupleTest.test_full base dummy safe,value]
    exact collision
  exact ⟨first.position,candidate,LookupCompressionKernel.of_test base dummy tested⟩

theorem compression (collision : CallerCompressionRecovery.Collision data dummy) :
    SeedQuoteOrder.Bad OracleProgramMachine.step program world ∨ FirstCompressionLifetime.Event program dummy world := by
  by_cases safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world
  · exact Or.inr (recover_compression data policy original template result executed inputs helperWidth sourceWidths before bytes valid dummy safe collision)
  · exact Or.inl (not_not.mp safe)

/-- Both original native miss branches now enter lifetime events whose safe
probabilities are bounded by specified interpreter work. Arithmetic/PCS and
shared lifetime bad alternatives remain explicit for final composition. -/
theorem nonmember (bad : RebuiltCallerLookupCoverage.Nonmember data dummy) :
    Nonempty (LookupInitialPairedWork.Witness (Memory := Memory) ctx allocation program dummy world) ∨
      SeedQuoteOrder.Bad OracleProgramMachine.step program world ∨ GlobalReferenceBad.Bad program dummy world ∨
      FirstCompressionLifetime.Event program dummy world ∨ OffsetLifetimeWork.Event program dummy world := by
  rcases RebuiltCallerLookupCoverage.nonmember_covered data policy original template result executed dummy inputs before bytes valid bad with
    arithmetic | collision | reciprocal
  · exact Or.inl arithmetic
  · rcases compression data policy original template result executed inputs helperWidth sourceWidths before bytes valid dummy collision with seed | event
    · exact Or.inr (Or.inl seed)
    · exact Or.inr (Or.inr (Or.inr (Or.inl event)))
  · rcases CallerOffsetWorkCoverage.reciprocal data policy original template result executed inputs helperWidth sourceWidths before bytes valid dummy reciprocal with seed | reference | event
    · exact Or.inr (Or.inl seed)
    · exact Or.inr (Or.inr (Or.inl reference))
    · exact Or.inr (Or.inr (Or.inr (Or.inr event)))

end
end FormalProof4FHE.HasteBoots.CallerLookupWorkCoverage
