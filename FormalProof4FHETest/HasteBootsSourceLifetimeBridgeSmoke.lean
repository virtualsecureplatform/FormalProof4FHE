module
import all FormalProof4FHE.HasteBoots.SourceOpeningLifetimeWitness
import all FormalProof4FHETest.HasteBootsNativeFinishingSmoke
import all FormalProof4FHETest.HasteBootsDeferredAvailabilitySmoke

namespace FormalProof4FHE.HasteBoots.SourceLifetimeBridgeSmoke
open InputIndexedOracle (World Byte)
open NativeTranscript (Transcript)
open OracleProgram (run)
noncomputable section

/-- The accepted original batch retains the profile of its actual parent. -/
example : HasteBootsNativeFinishingSmoke.parent.profile = HasteBootsBatchMeaningSmoke.ctx.parent.profile :=
  BatchOpeningProfileLineage.accepted_profile _ _ _ _ _ _ _ HasteBootsNativeFinishingSmoke.executed _ HasteBootsNativeFinishingSmoke.accepted

example : HasteBootsNativeFinishingSmoke.work.sample.transcript.profile = HasteBootsBatchMeaningSmoke.ctx.parent.profile := by
  have origin := NativeGoldBatchPcsProgram.completed_origin _ _ _ _ _ _ _ HasteBootsNativeFinishingSmoke.executed
  exact BatchOpeningProfileLineage.prepared_profile _ _ _ origin.prepared

open HasteBootsDeferredAvailabilitySmoke (ctxTwo executionTwo)

/-- The second native batch rejects its altered root, retaining the first
original owner receipt and both of that receipt's original parent profiles. -/
example : ∃ result : NativeDeferredBatchVerification.Result Unit,
    executionTwo.1 = .verification result ∧ result.progress.receipts.length = 1 ∧
    (match result with | .stopped _ call _ => some call.slot | _ => none) = some 2 ∧
    DeferredBatchProfileLineage.Consistent ctxTwo.state.parent.profile result.progress := by
  have existsResult : ∃ result : NativeDeferredBatchVerification.Result Unit,
      executionTwo.1 = .verification result := by
    cases actual : executionTwo.1 with
    | sealRejected state reason =>
      have tag : HasteBootsDeferredAvailabilitySmoke.resultTag executionTwo.1 = 2 := by decide +kernel
      rw [actual] at tag
      contradiction
    | verification result => exact ⟨result,rfl⟩
  obtain ⟨result,same⟩ := existsResult
  refine ⟨result,same,?_,?_,?_⟩
  · have length : (HasteBootsDeferredAvailabilitySmoke.receiptsOf executionTwo.1).length = 1 := by decide +kernel
    simpa only [same,HasteBootsDeferredAvailabilitySmoke.receiptsOf] using length
  · have stopped : (match executionTwo.1 with | .verification (.stopped _ call _) => some call.slot | _ => none) = some 2 := by decide +kernel
    rw [same] at stopped
    cases result <;> exact stopped
  · exact DeferredBatchProfileLineage.program_profiles ctxTwo (HasteBootsBatchPcsSmoke.choose false) ()
      HasteBootsDeferredAvailabilitySmoke.world result same

/-- Sealing cannot change arbitrary nonconstant trusted-profile metadata. -/
example (state : NativeDeferredOpeningBatch.State) (profile : Fin 64 → Byte) (packets : ℕ) :
    (NativeDeferredOpeningBatch.sealBatch {state with parent := {state.parent with profile := profile}} packets).1.parent.profile = profile :=
  SourceClaimProfileLineage.seal_profile _ _

/-- Original slot insertion preserves profile in every dimension/index/error case. -/
example (registry : NativePrefixCodec.Vector (NativeSharedLookupParent.Oracle NativeGoldBlockCode.Stored))
    (state : NativeDeferredOpeningBatch.State) (slot : NativeUsizeMessage.Usize)
    (query : NativeGoldPcsWire.Query) (values : NativeLookupRequestWire.Row) :
    (NativeDeferredOpeningBatch.push registry state slot query values).1.parent.profile = state.parent.profile :=
  SourceClaimProfileLineage.push_profile _ _ _ _ _

/-- Targeting the fixed public context never replaces the selected original
constructor request or reachable constructor state. -/
example (candidate target : NativeGoldBatchPcsProgram.Context) (origin : CacheBackedCodeOrigin.Origin candidate)
    (same : candidate.parameters = target.parameters) :
    (SourceOpeningLifetimeWitness.retarget origin target same).request = origin.request ∧
    (SourceOpeningLifetimeWitness.retarget origin target same).config = origin.config :=
  SourceOpeningLifetimeWitness.retarget_data origin target same

end
end FormalProof4FHE.HasteBoots.SourceLifetimeBridgeSmoke
