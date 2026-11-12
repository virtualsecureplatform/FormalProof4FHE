module
public import FormalProof4FHE.HasteBoots.CallerLookupSourceRecovery
public import FormalProof4FHE.HasteBoots.LookupCompressionKernel
@[expose] public section

/-! A collision on the original caller's complete decoded source tuples at
its literal produced y recovers an attained compression kernel candidate.
No preselected stream, snapshot equality or challenge-value flag is required. -/
namespace FormalProof4FHE.HasteBoots.CallerCompressionRecovery
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open InputIndexedOracle (World)
open OracleProgram (Program run)
noncomputable section
variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}

def Collision (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (dummy : NativeRootMessage.Digest) : Prop :=
  LookupTupleTest.compression (data.origin.ready.jobs.get data.index).tag.request
    (NativeScalarQueryShape.checked_power _ _ _ data.job.view.shape) data.job.view.enough
    (CanonicalAllocatedTables.sources allocation data.origin data.index data.job data.geometry dummy (run program world).run.2)
    (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y)

theorem recover (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (inputs : SequencedCallerInputs.Inputs data) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame) (dummy : NativeRootMessage.Digest)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) (collision : Collision data dummy) :
    ∃ position, ∃ candidate : LookupSourceCandidate.Candidate program position world,
      candidate.ctx = ctx ∧ candidate.index.val = data.index.val ∧ LookupCompressionKernel.Event candidate dummy world := by
  obtain ⟨draw,_,drawAt,_,decoded,_⟩ := LookupProducedEndpoints.draws _ _ _ _ data.job.view.produced
  have member : draw ∈ data.job.view.producer.selection.draws := List.mem_of_mem_head? (by rw [drawAt]; rfl)
  obtain ⟨first,⟨recovered⟩⟩ := CallerLookupSourceRecovery.recover_first data draw member inputs helperWidth sourceWidths before bytes valid safe
  let candidate := CallerLookupSourceRecovery.candidate data draw member first recovered
  have value : candidate.draw.value = NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y :=
    (LookupCompressionKernel.draw_value candidate).trans (LookupScalarKernel.decoded_value draw.coefficients _ decoded).symm
  have tested : LookupTupleTest.test candidate dummy candidate.draw.value := by
    rw [LookupTupleTest.test_full candidate dummy safe,value]
    exact collision
  exact ⟨first.position,candidate,rfl,rfl,LookupCompressionKernel.of_test candidate dummy tested⟩

end
end FormalProof4FHE.HasteBoots.CallerCompressionRecovery
