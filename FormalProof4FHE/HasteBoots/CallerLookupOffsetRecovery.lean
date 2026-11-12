module
public import FormalProof4FHE.HasteBoots.LookupOffsetKernel
public import FormalProof4FHE.HasteBoots.CallerLookupMultiplicityRecovery
@[expose] public section

/-! Actual caller receipt logs construct original accepted-offset candidates.
The y-fixation interface is recovered from the same missed job, not supplied
as a digest equality, named payload or independently chosen challenge. -/
namespace FormalProof4FHE.HasteBoots.CallerLookupOffsetRecovery
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open InputIndexedOracle (World)
open OracleProgram (Program run)
open MeasureTheory ProbabilityTheory
noncomputable section
variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}

theorem receipts (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    LookupReceiptLogs.Reads world data.job.view.producer.selection.draws (run program world).run.2 := by
  let transcript := LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world
  let actions := NativeLookupBatch.schedule ctx.requests.property.le (fun i => (NativeSharedLookupParent.models ctx.requests i).sampling)
  have reads := (LookupBatchReceiptLogs.initialized goldilocksBasis 7 ctx.lookupFuel actions transcript world).2 _ data.job.producerMember
  have batchInPrelude : (NativeLookupBatch.execute goldilocksBasis 7 ctx.lookupFuel
      (NativeLookupBatch.initial actions transcript) world).2.Sublist
      (run (NativeSharedLookupPrelude.protocol ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
        data.origin.geometry.geometry.1 ctx.proof.values.multiplicities ctx.proof.roots.val ctx.proof.roots.property
        7 ctx.lookupFuel ctx.equalityFuel transcript) world).run.2 := by
    rw [NativeSharedLookupPrelude.run_protocol]
    exact List.sublist_append_left _ _
  have native := CallerEqualityFamily.native data
  have logged := (LookupPreludeTrace.logged_of_success data.origin native.1).trans native.2
  exact LookupReceiptLogs.mono world _ _ _ reads (batchInPrelude.trans logged)

def candidate (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupChallenge.Draw Goldilocks3) (member : draw ∈ data.job.view.producer.selection.draws)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (recovered : CallerLookupMultiplicityRecovery.Recovery data draw first)
    (lastAt : data.job.view.producer.selection.draws.getLast? = some draw) :
    LookupOffsetCompressionFixation.Candidate program first.position world :=
  ⟨CallerLookupMultiplicityRecovery.candidate data draw member first recovered,lastAt,receipts data⟩

/-- Recover the same job's attained prefix kernel and the original offset
candidate to which source/count/y fixation applies. -/
theorem recover (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (dummy : NativeRootMessage.Digest) (miss : RebuiltCallerLookupCoverage.ReciprocalMiss data dummy)
    (inputs : SequencedCallerInputs.Inputs data) (helperWidth : ctx.helper.width.val ≤ 4)
    (sourceWidths : ∀ slot : Fin ctx.registry.val.length, (ctx.registry.val.get slot).parameters.width.val ≤ 4)
    (before : List TranscriptFrame.Frame) (bytes : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (safe : ¬SeedQuoteOrder.Bad OracleProgramMachine.step program world) :
    ∃ draw : NativeLookupChallenge.Draw Goldilocks3,
      ∃ first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input,
        ∃ recovered : CallerLookupMultiplicityRecovery.Recovery data draw first,
          ∃ member : draw ∈ data.job.view.producer.selection.draws,
            ∃ lastAt : data.job.view.producer.selection.draws.getLast? = some draw,
              LookupOffsetKernel.Event (candidate data draw member first recovered lastAt) dummy world := by
  obtain ⟨draw,first,recovered,member,lastAt,event⟩ := CallerLookupMultiplicityRecovery.kernel data dummy miss inputs helperWidth sourceWidths before bytes valid safe
  exact ⟨draw,first,recovered,member,lastAt,event⟩

/-- Actual rebuilt execution discharges the characteristic guard for the
same original candidate's refined reciprocal bound. -/
theorem bound (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world)
    (draw : NativeLookupChallenge.Draw Goldilocks3) (member : draw ∈ data.job.view.producer.selection.draws)
    (first : ProgramFirstStreamRead.First program world draw.coefficients.phase.pending.input)
    (recovered : CallerLookupMultiplicityRecovery.Recovery data draw first)
    (lastAt : data.job.view.producer.selection.draws.getLast? = some draw) (dummy : NativeRootMessage.Digest)
    (policy : NativeSharedLookupValues.Policy) (original : Vector NativeLookupRequestWire.Request)
    (template : Context (Vector Opening)) (result : NativeGoldLookupVerification.Outcome Memory)
    (executed : (run (RebuiltLookupExecution.program policy original allocation.entries allocation.helperHandle allocation.references template
      data.chooseHelper data.chooseBatch data.memory) world).run.1 = .allocated (.verification ctx result)) :
    (InputIndexedOracle.law[|{other | (ParentFactorFiber.extend (OracleProgram.runPrefix first.position program) other).run =
      (ParentFactorFiber.extend (OracleProgram.runPrefix first.position program) world).run}])
      {other | LookupOffsetKernel.Event (candidate data draw member first recovered lastAt) dummy other} ≤
      (LookupOffsetKernel.complexity (candidate data draw member first recovered lastAt) : ENNReal)/(NativeFields.goldilocksModulus^3 : ℕ) := by
  exact LookupOffsetKernel.bound program first.position world (candidate data draw member first recovered lastAt) dummy
    (RebuiltJobPublicGeometry.logical_lt_characteristic policy original allocation.entries allocation.helperHandle allocation.references template
      data.chooseHelper data.chooseBatch data.memory result executed data.origin data.index data.job)

end
end FormalProof4FHE.HasteBoots.CallerLookupOffsetRecovery
