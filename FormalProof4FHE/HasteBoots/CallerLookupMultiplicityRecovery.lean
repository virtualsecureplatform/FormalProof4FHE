module
public import FormalProof4FHE.HasteBoots.LookupReciprocalStatement
public import FormalProof4FHE.HasteBoots.CallerLookupSourceRecovery
public import FormalProof4FHE.HasteBoots.CallerReciprocalKernel
@[expose] public section

/-! Actual allocated execution and serialized caller domains supply the
multiplicity/parent link. No grouped-payload equality is requested from the
caller when constructing this original lookup candidate. -/
namespace FormalProof4FHE.HasteBoots.CallerLookupMultiplicityRecovery
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeExtensionFields (Goldilocks3)
open InputIndexedOracle (World)
open OracleProgram (Program run)
noncomputable section
variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}

theorem grouped (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupChallenge.Draw Goldilocks3)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (recovered : CallerLookupSourceRecovery.Recovery data draw first)
    (framing : AllocatedLookupReadStability.Framing ctx world) :
    recovered.parent.parent.grouped = NativeLookupMultiplicityWire.grouped ctx.proof.multiplicities := by
  obtain ⟨view,parsed,_,_,grouped,_⟩ := AllocatedParentData.recover allocation.entries allocation.helperHandle allocation.references allocation.template
    data.chooseHelper data.chooseBatch data.memory _ (congrArg Prod.fst (CallerEqualityFamily.execution data))
    data.lookup data.progress data.after data.executed framing
  have parentParsed := recovered.parent.parsed
  rw [recovered.input,parsed] at parentParsed
  have same := Option.some.inj parentParsed
  exact (congrArg SharedParentInputView.View.grouped same).symm.trans grouped

structure Recovery (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupChallenge.Draw Goldilocks3)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input) where
  source : CallerLookupSourceRecovery.Recovery data draw first
  grouped : source.parent.parent.grouped = NativeLookupMultiplicityWire.grouped ctx.proof.multiplicities

def candidate (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupChallenge.Draw Goldilocks3) (member : draw ∈ data.job.view.producer.selection.draws)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (recovered : Recovery data draw first) : LookupMultiplicityFixation.Candidate program first.position world :=
  ⟨CallerLookupSourceRecovery.candidate data draw member first recovered.source,recovered.grouped⟩

/-- The retained original draw and its first read determine the candidate;
all remaining premises are the original caller's serialization/domain data. -/
theorem recover (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupChallenge.Draw Goldilocks3) (member : draw ∈ data.job.view.producer.selection.draws)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (inputs : SequencedCallerInputs.Inputs data) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) : Nonempty (Recovery data draw first) := by
  obtain ⟨recovered⟩ := CallerLookupSourceRecovery.recover data draw member first inputs helperWidth sourceWidths before bytes valid safe
  exact ⟨⟨recovered,grouped data draw first recovered
    (CallerPairedPreparation.framing data inputs helperWidth sourceWidths before bytes valid)⟩⟩

/-- The enriched candidate's prefix test is exactly the original caller's
full reciprocal statement, at its literal produced compression value. -/
theorem test_full (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupChallenge.Draw Goldilocks3) (member : draw ∈ data.job.view.producer.selection.draws)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (recovered : Recovery data draw first) (dummy : NativeRootMessage.Digest)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    LookupReciprocalStatement.test (candidate data draw member first recovered) dummy
        (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y) =
      LookupReciprocalKernel.test (CallerReciprocalKernel.sources data dummy)
        (CallerReciprocalKernel.table data) (CallerReciprocalKernel.multiplicities data) := by
  rw [LookupReciprocalStatement.test_full _ dummy _ safe]
  rfl

/-- A reciprocal miss recovers the enriched candidate on its actual accepted
offset stream. Neither a chosen draw nor a parent/count equality is supplied. -/
theorem reciprocal (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (dummy : NativeRootMessage.Digest) (miss : RebuiltCallerLookupCoverage.ReciprocalMiss data dummy)
    (inputs : SequencedCallerInputs.Inputs data) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    ∃ last : NativeLookupChallenge.Draw Goldilocks3,
      ∃ first : ProgramFirstStreamRead.First program world last.coefficients.phase.pending.input,
        data.job.view.producer.selection.draws.getLast? = some last ∧
        CallerReciprocalKernel.Event data dummy last.coefficients.phase.pending.input world ∧
        Nonempty (Recovery data last first) := by
  obtain ⟨last,lastAt,⟨first⟩,event⟩ := CallerReciprocalKernel.recover data dummy miss
  exact ⟨last,first,lastAt,event,recover data last (List.mem_of_mem_getLast? (by rw [lastAt]; rfl))
    first inputs helperWidth sourceWidths before bytes valid safe⟩

/-- Recover the attained reciprocal event on the source prefix at the
original first read, ready for cross-world statement fixation. -/
theorem kernel (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (dummy : NativeRootMessage.Digest) (miss : RebuiltCallerLookupCoverage.ReciprocalMiss data dummy)
    (inputs : SequencedCallerInputs.Inputs data) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    ∃ last : NativeLookupChallenge.Draw Goldilocks3,
      ∃ first : ProgramFirstStreamRead.First program world last.coefficients.phase.pending.input,
        ∃ recovered : Recovery data last first,
          ∃ member : last ∈ data.job.view.producer.selection.draws,
            data.job.view.producer.selection.draws.getLast? = some last ∧
            LookupScalarKernel.Event last.coefficients.phase.pending.input
              (LookupReciprocalStatement.test (candidate data last member first recovered) dummy
                (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y)) world := by
  obtain ⟨last,first,lastAt,event,⟨recovered⟩⟩ := reciprocal data dummy miss inputs helperWidth sourceWidths before bytes valid safe
  have member := List.mem_of_mem_getLast? (by rw [lastAt]; rfl)
  refine ⟨last,first,recovered,member,lastAt,?_⟩
  rw [test_full data last member first recovered dummy safe]
  exact event

end
end FormalProof4FHE.HasteBoots.CallerLookupMultiplicityRecovery
