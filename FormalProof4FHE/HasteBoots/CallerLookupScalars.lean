module
public import FormalProof4FHE.HasteBoots.LookupBatchCollectorTrace
public import FormalProof4FHE.HasteBoots.CallerEqualityFamily
@[expose] public section

/-! The same retained caller job supplies original compression/offset scalar
kernel values and their earliest positive reads. No independently chosen y/r,
postselected successful-draw law or first-exposure certificate is introduced. -/
namespace FormalProof4FHE.HasteBoots.CallerLookupScalars
open NativeGoldHelperVerification (Context)
open NativePrefixCodec (Vector)
open NativeGoldBatchOpening (Opening)
open NativeExtensionFields (Goldilocks3 goldilocksBasis)
open InputIndexedOracle (World)
open OracleProgram (Program run)
noncomputable section
variable {Memory A : Type} {ctx : Context (Vector Opening)} {allocation : AllocatedFamilyFunctions.Allocation ctx}
    {program : Program A} {world : World}

theorem producer_trace (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    LookupCollectorTrace.Traced data.job.view.producer.selection world (run program world).run.2 := by
  let transcript := LookupExecutionOrigin.childStart NativeGoldBlockCode.description.row ctx.registry ctx.helper ctx.parent ctx.requests ctx.proof world
  let actions := NativeLookupBatch.schedule ctx.requests.property.le (fun i => (NativeSharedLookupParent.models ctx.requests i).sampling)
  have traced := (LookupBatchCollectorTrace.initialized ctx.lookupFuel actions transcript world).2 _ data.job.producerMember
  have batchInPrelude : (NativeLookupBatch.execute goldilocksBasis 7 ctx.lookupFuel
      (NativeLookupBatch.initial actions transcript) world).2.Sublist
      (run (NativeSharedLookupPrelude.protocol ctx.requests.property.le (NativeSharedLookupParent.models ctx.requests)
        data.origin.geometry.geometry.1 ctx.proof.values.multiplicities ctx.proof.roots.val ctx.proof.roots.property
        7 ctx.lookupFuel ctx.equalityFuel transcript) world).run.2 := by
    rw [NativeSharedLookupPrelude.run_protocol]
    exact List.sublist_append_left _ _
  have native := CallerEqualityFamily.native data
  have logged := (LookupPreludeTrace.logged_of_success data.origin native.1).trans native.2
  exact LookupCollectorTrace.traced_mono _ world _ _ traced (batchInPrelude.trans logged)

theorem endpoints (data : CallerFramedAllocatedJob.Job (Memory := Memory) ctx allocation program world) :
    ∃ first last : NativeLookupChallenge.Draw Goldilocks3,
      data.job.view.producer.selection.draws.head? = some first ∧
      data.job.view.producer.selection.draws.getLast? = some last ∧
      (∃ budget, GoldScalarChallengeLaw.values budget (LookupScalarKernel.phase first.coefficients.phase.pending.input) world =
        some (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.y)) ∧
      (∃ budget, GoldScalarChallengeLaw.values budget (LookupScalarKernel.phase last.coefficients.phase.pending.input) world =
        some (NativeFieldWire.goldExtensionValue (data.origin.ready.jobs.get data.index).output.r)) ∧
      Nonempty (ProgramFirstStreamRead.First program world first.coefficients.phase.pending.input) ∧
      Nonempty (ProgramFirstStreamRead.First program world last.coefficients.phase.pending.input) := by
  obtain ⟨first,last,firstAt,lastAt,yDecode,rDecode⟩ := LookupProducedEndpoints.draws _ _ _ _ data.job.view.produced
  have traced := producer_trace data
  have firstSource := traced.2 first (List.mem_of_mem_head? (by rw [firstAt]; rfl))
  have lastSource := traced.2 last (List.mem_of_mem_getLast? (by rw [lastAt]; rfl))
  exact ⟨first,last,firstAt,lastAt,
    LookupScalarKernel.source_word first.coefficients world _ firstSource.1 firstSource.2 _ yDecode,
    LookupScalarKernel.source_word last.coefficients world _ lastSource.1 lastSource.2 _ rDecode,
    LookupCollectorTrace.source_first first.coefficients world program firstSource.1 firstSource.2,
    LookupCollectorTrace.source_first last.coefficients world program lastSource.1 lastSource.2⟩

end
end FormalProof4FHE.HasteBoots.CallerLookupScalars
