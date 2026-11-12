module
public import FormalProof4FHE.HasteBoots.LookupSourceCandidate
public import FormalProof4FHE.HasteBoots.CallerLookupScalars
@[expose] public section

/-! Actual caller execution and sequenced input framing recover the original
source candidate at a lookup draw's earliest read. Parent chronology and the
complete decoded source snapshot are proved rather than supplied as flags. -/
namespace FormalProof4FHE.HasteBoots.CallerLookupSourceRecovery
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeExtensionFields (Goldilocks3)
open InputIndexedOracle (World)
open OracleProgram (Program run runPrefix)
noncomputable section
variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}

structure Recovery (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupChallenge.Draw Goldilocks3)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input) where
  parent : OriginalParentFamily.Family program first.position world
  registry : parent.registry = ctx.registry
  helper : parent.helper = ctx.helper
  requests : parent.requests = ctx.requests
  input : parent.input = LookupScalarSeedQuote.forkInput ctx world
  ancestry : AllocatedLookupReadStability.Ancestry data.origin data.index data.job (run program world).run.2

def candidate (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupChallenge.Draw Goldilocks3) (member : draw ∈ data.job.view.producer.selection.draws)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (recovered : Recovery data draw first) : LookupSourceCandidate.Candidate program first.position world :=
  ⟨ctx,data.lookup.body,allocation,data.origin,data.index,data.job,data.geometry,recovered.parent,recovered.registry,recovered.helper,
    recovered.requests,recovered.input,draw,member,first,rfl,recovered.ancestry⟩

theorem recover (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupChallenge.Draw Goldilocks3) (member : draw ∈ data.job.view.producer.selection.draws)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (inputs : SequencedCallerInputs.Inputs data) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) : Nonempty (Recovery data draw first) := by
  let framing := CallerPairedPreparation.framing data inputs helperWidth sourceWidths before bytes valid
  have ancestry := AllocatedLookupReadStability.allocated_ancestry allocation.entries allocation.helperHandle allocation.references allocation.template
    data.chooseHelper data.chooseBatch data.memory _ (congrArg Prod.fst (CallerEqualityFamily.execution data))
    data.lookup data.progress data.after data.executed data.origin data.index data.job framing (run program world).run.2
    (CallerEqualityFamily.observed data)
  obtain ⟨parentPosition,realized⟩ := ancestry.helper
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
    exact LookupDrawSeedQuote.quote data.origin data.job draw member
  have known := actual.before_quote OracleProgramMachine.step fuel program world safe first.position _
    (by rw [logs]; exact first.outputAt) quoted
  rw [logs,← first.history] at known
  obtain ⟨parent,registry,helper,requests,input⟩ := AllocatedParentFamily.recover allocation.entries allocation.helperHandle allocation.references allocation.template
    data.chooseHelper data.chooseBatch data.memory _ (congrArg Prod.fst (CallerEqualityFamily.execution data))
    data.lookup data.progress data.after data.executed before bytes valid inputs.parent_domain program first.position
    (CallerEqualityFamily.observed data) known framing
  exact ⟨⟨parent,registry,helper,requests,input,ancestry⟩⟩

/-- The earliest read is itself a consequence of the original observed
collector, including possible adversarial prequeries before verification. -/
theorem recover_first (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupChallenge.Draw Goldilocks3) (member : draw ∈ data.job.view.producer.selection.draws)
    (inputs : SequencedCallerInputs.Inputs data) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    ∃ first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input, Nonempty (Recovery data draw first) := by
  have traced := (CallerLookupScalars.producer_trace data).2 draw member
  obtain ⟨first⟩ := LookupCollectorTrace.source_first draw.coefficients world program traced.1 traced.2
  exact ⟨first,recover data draw member first inputs helperWidth sourceWidths before bytes valid safe⟩

end
end FormalProof4FHE.HasteBoots.CallerLookupSourceRecovery
