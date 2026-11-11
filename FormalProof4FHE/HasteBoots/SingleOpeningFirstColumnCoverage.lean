module
public import FormalProof4FHE.HasteBoots.SingleOpeningEarlyReceiptNative
public import FormalProof4FHE.HasteBoots.SingleOpeningConcreteExposureCoverage
@[expose] public section

/-! Actual accepted false single-opening claims at the first column read.
The source log is recovered from that packet's history, or the native true
receipt supplies the early-event branch. Shared disagreement stays explicit.
Global inherited and earlier-field classification still follows separately. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningFirstColumnCoverage
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsProgram (Scheduler)
open InputIndexedOracle (World)
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (shape)
open NativeGoldBatchFamilyAvailability (reconstructed)
open NativeIndexExposureRisk (Packet)
open SingleOpeningConcreteColumnFamily (source Domain)
open SingleOpeningFixedResponseData (left right claimed)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem accepted_first_column_cover {S A Memory : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (dummy : Digest) (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample) (origin : CacheBackedSingleOpening.Origin ctx)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (first : CausalStreamExposure.firstRead step packet = some (SingleOpeningColumnLaw.input receipt world))
    (suffix : List Observation) (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (accepted : SingleOpeningAvailability.Accepted world (packet.2++suffix) ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world (packet.2++suffix)) (radius : ℕ) (width : 3 ≤ ctx.parameters.width.val)
    (falseClaim : ∀ sourceLog, SingleOpeningFirstFieldSource.recover dummy packet.2 decoded.field = some sourceLog →
      claimed ctx decoded.field.data.claimed ≠ matrixEvaluation (left ctx.parameters decoded.field.data.query)
        (right ctx.parameters decoded.field.data.query)
        (RectangularMatrixOpeningKernel.extract (Domain ctx origin.primitive) origin.capacity radius (source dummy ctx decoded sourceLog))) :
    CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy (packet.2++suffix)) ∨
      SingleOpeningEarlyReceiptBound.event ctx.transcript.profile step packet world ∨
      ∃ sourceLog, SingleOpeningFirstFieldSource.recover dummy packet.2 decoded.field = some sourceLog ∧
        (SingleOpeningProfileColumnExposure.event dummy ctx origin.primitive ctx.transcript.profile step packet radius world ∨
          SingleOpeningFieldProximity.matrixBad ctx origin.primitive (source dummy ctx decoded sourceLog) radius
            (SingleOpeningRecoveredMatrix.random ctx receipt.state)) := by
  classical
  by_cases failed : CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy (packet.2++suffix))
  · exact Or.inl failed
  · right
    have acceptedCopy := accepted
    obtain ⟨⟨before,parent,valid,fits⟩,completion,_,executed,_,_⟩ := acceptedCopy
    have prepared := (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
    rcases SingleOpeningEarlyReceiptNative.first_column_sources dummy receipt prepared before parent valid fits responseFits width step packet
      first decoded parsed with early | available
    · exact Or.inl early
    · right
      obtain ⟨sourceLog,found⟩ := available
      refine ⟨sourceLog,found,?_⟩
      rcases SingleOpeningConcreteCoverage.false_claim_cases dummy receipt origin choose fuel memory packet.2 suffix decoded parsed responseFits
        sourceLog found accepted truthful failed radius (falseClaim sourceLog found) with column | proximity
      · left
        have selected := SingleOpeningProfileColumnNative.selected_native receipt prepared before parent valid fits responseFits decoded parsed
          origin step packet first
        unfold SingleOpeningProfileColumnExposure.event
        rw [selected]
        exact column
      · exact Or.inr proximity

end
end FormalProof4FHE.HasteBoots.SingleOpeningFirstColumnCoverage
