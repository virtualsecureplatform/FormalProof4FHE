module
public import FormalProof4FHE.HasteBoots.SingleOpeningConcreteCoverage
public import FormalProof4FHE.HasteBoots.SingleOpeningProfileColumnNative
@[expose] public section

/-! Once the original field and column first-exposure boundaries are
identified, an actual accepted false single claim lies in one of the two
concrete exposure events. Global inherited/early-receipt classification
still has to identify those boundaries in an arbitrary machine lifetime. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningConcreteExposureCoverage
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsProgram (Scheduler)
open InputIndexedOracle (Input World)
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
open NativeRootFamilySourceSelection (Log)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (shape)
open NativeGoldBatchFamilyAvailability (reconstructed)
open NativeIndexExposureRisk (Packet)
open SingleOpeningConcreteColumnFamily (source Domain)
open SingleOpeningFixedResponseData (left right claimed)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem false_claim_events {S A Memory : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (dummy : Digest) (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample) (origin : CacheBackedSingleOpening.Origin ctx)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (step : S → OracleMachine.Command S A)
    (columnPacket fieldPacket : Packet S A) (suffix : List Observation) (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (firstColumn : CausalStreamExposure.firstRead step columnPacket = some (SingleOpeningColumnLaw.input receipt world))
    (firstField : CausalStreamExposure.firstRead step fieldPacket = some (SingleOpeningFirstFieldSource.input decoded.field))
    (sourceLog : Log) (found : SingleOpeningFirstFieldSource.recover dummy columnPacket.2 decoded.field = some sourceLog)
    (offset : ℕ) (values : Input) (positive : values ≠ []) (middle : List Observation)
    (split : columnPacket.2 = fieldPacket.2 ++ .output (SingleOpeningFirstFieldSource.input decoded.field) offset values :: middle)
    (accepted : SingleOpeningAvailability.Accepted world (columnPacket.2++suffix) ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world (columnPacket.2++suffix))
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy (columnPacket.2++suffix)))
    (radius : ℕ)
    (falseClaim : claimed ctx decoded.field.data.claimed ≠ matrixEvaluation
      (left ctx.parameters decoded.field.data.query) (right ctx.parameters decoded.field.data.query)
      (RectangularMatrixOpeningKernel.extract (Domain ctx origin.primitive) origin.capacity radius (source dummy ctx decoded sourceLog))) :
    SingleOpeningProfileColumnExposure.event dummy ctx origin.primitive ctx.transcript.profile step columnPacket radius world ∨
      SingleOpeningFieldProximity.event dummy ctx origin.primitive radius ctx.transcript.profile step fieldPacket world := by
  have acceptedCopy := accepted
  obtain ⟨⟨before,parent,valid,fits⟩,completion,_,executed,_,_⟩ := acceptedCopy
  have prepared := (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  rcases SingleOpeningConcreteCoverage.false_claim_cases dummy receipt origin choose fuel memory columnPacket.2 suffix decoded parsed
    responseFits sourceLog found accepted truthful noDisagreement radius falseClaim with column | proximity
  · left
    have selected := SingleOpeningProfileColumnNative.selected_native receipt prepared before parent valid fits responseFits decoded parsed
      origin step columnPacket firstColumn
    unfold SingleOpeningProfileColumnExposure.event
    rw [selected]
    exact column
  · right
    exact SingleOpeningFieldProximityCoverage.later_proximity dummy receipt prepared before parent valid fits responseFits decoded parsed
      origin.primitive radius step fieldPacket firstField columnPacket.2 sourceLog found offset values positive middle split proximity

end
end FormalProof4FHE.HasteBoots.SingleOpeningConcreteExposureCoverage
