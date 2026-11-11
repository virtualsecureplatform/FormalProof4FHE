module
public import FormalProof4FHE.HasteBoots.SingleOpeningConcreteColumnWitness
public import FormalProof4FHE.HasteBoots.SingleOpeningParsedDraws
public import FormalProof4FHE.HasteBoots.SingleOpeningFieldProximityCoverage
@[expose] public section

/-! Pointwise coverage of actual accepted false single-opening claims at a
recovered source: the concrete shared-column event or the earlier-field
proximity obstruction. Causal first-exposure/early-receipt classification,
public application extraction and physical work remain separate. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningConcreteCoverage
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsProgram (Scheduler)
open InputIndexedOracle (World)
open NativeTranscript (Observation)
open NativeRootMessage (Digest)
open NativeRootFamilySourceSelection (Log)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (shape)
open NativeGoldBatchFamilyAvailability (reconstructed)
open SingleOpeningConcreteColumnFamily (source raw claim Test Position Symbol Domain)
open SingleOpeningConcreteColumnBound (distance)
open SingleOpeningFixedResponseData (left right claimed)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem witnessed_event {Memory : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (dummy : Digest) (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample) (origin : CacheBackedSingleOpening.Origin ctx)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (columnHistory suffix : List Observation) (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (sourceLog : Log) (found : SingleOpeningFirstFieldSource.recover dummy columnHistory decoded.field = some sourceLog)
    (accepted : SingleOpeningAvailability.Accepted world (columnHistory++suffix) ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world (columnHistory++suffix))
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy (columnHistory++suffix)))
    (radius : ℕ)
    (witness : ∃ test : Test ctx, distance ctx origin.primitive radius ≤
      hammingDist (raw dummy ctx decoded sourceLog receipt.state test) (claim ctx origin.primitive decoded receipt.state test)) :
    SingleOpeningConcreteColumnBound.event dummy ctx origin.primitive ctx.transcript.profile decoded columnHistory radius world := by
  have acceptedCopy := accepted
  obtain ⟨⟨before,parent,valid,fits⟩,completion,_,executed,_,_⟩ := acceptedCopy
  have prepared := (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  have foundFull := SingleOpeningFirstFieldSource.recover_append dummy columnHistory suffix decoded.field sourceLog found
  obtain ⟨draw,typed,_,checks⟩ := SingleOpeningSelectedChecks.recovered_checks dummy receipt origin choose fuel memory
    (columnHistory++suffix) decoded sourceLog foundFull accepted truthful noDisagreement before parent valid fits responseFits parsed
  have data := SingleOpeningPreparedChallenge.parsed_origin receipt prepared before parent valid fits responseFits decoded parsed
  have collected : (SingleOpeningFieldColumnLaw.collected ctx.transcript.profile ctx.fieldFuel decoded world).1 = receipt.state := data.2.2.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,count,_,_⟩ := data
  have sampled := SingleOpeningParsedDraws.values_typed receipt prepared before parent valid fits responseFits decoded parsed
  rw [collected] at checks
  unfold SingleOpeningConcreteColumnBound.event
  rw [found]
  refine ⟨ctx.fieldFuel,?_⟩
  unfold SingleOpeningFieldColumnLaw.event
  rw [count] at sampled ⊢
  rw [sampled,typed]
  simp only [Option.elim_some,collected]
  exact ⟨SingleOpeningFieldProximityCoverage.complete receipt,witness,checks⟩

theorem false_claim_cases {Memory : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (dummy : Digest) (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample) (origin : CacheBackedSingleOpening.Origin ctx)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (columnHistory suffix : List Observation) (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (sourceLog : Log) (found : SingleOpeningFirstFieldSource.recover dummy columnHistory decoded.field = some sourceLog)
    (accepted : SingleOpeningAvailability.Accepted world (columnHistory++suffix) ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world (columnHistory++suffix))
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy (columnHistory++suffix)))
    (radius : ℕ)
    (falseClaim : claimed ctx decoded.field.data.claimed ≠ matrixEvaluation
      (left ctx.parameters decoded.field.data.query) (right ctx.parameters decoded.field.data.query)
      (RectangularMatrixOpeningKernel.extract (Domain ctx origin.primitive) origin.capacity radius (source dummy ctx decoded sourceLog))) :
    SingleOpeningConcreteColumnBound.event dummy ctx origin.primitive ctx.transcript.profile decoded columnHistory radius world ∨
      SingleOpeningFieldProximity.matrixBad ctx origin.primitive (source dummy ctx decoded sourceLog) radius
        (SingleOpeningRecoveredMatrix.random ctx receipt.state) := by
  classical
  by_cases near : ∃ close, CommonSource.RowsIn (BlockCode.code (Domain ctx origin.primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val) close ∧
      hammingDist (source dummy ctx decoded sourceLog) close ≤ radius
  · left
    have witness := SingleOpeningConcreteColumnWitness.near_distance dummy receipt origin (columnHistory++suffix) choose fuel memory
      accepted responseFits decoded parsed sourceLog receipt.state radius near falseClaim
    exact witnessed_event dummy receipt origin choose fuel memory columnHistory suffix decoded parsed responseFits sourceLog found
      accepted truthful noDisagreement radius witness
  · by_cases close : ∀ lane : Fin ctx.parameters.width.val,
      Code.distFromCode (StructuredOpening.combine (SingleOpeningRecoveredMatrix.random ctx receipt.state lane) (source dummy ctx decoded sourceLog))
        (BlockCode.code (Domain ctx origin.primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
          Set (Position ctx → Symbol ctx)) ≤ radius
    · exact Or.inr ⟨near,close⟩
    · left
      have acceptedCopy := accepted
      obtain ⟨_,completion,_,executed,_,_⟩ := acceptedCopy
      have prepared := (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
      have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
        (SingleOpeningRectangularData.geometry ctx world work prepared)
      let : NeZero ctx.parameters.code.blockWidth.val := ⟨geometry.code.2.2.2.2⟩
      have witness := SingleOpeningConcreteColumnWitness.far_distance dummy ctx origin.primitive decoded sourceLog receipt.state radius close
      exact witnessed_event dummy receipt origin choose fuel memory columnHistory suffix decoded parsed responseFits sourceLog found
        accepted truthful noDisagreement radius witness

end
end FormalProof4FHE.HasteBoots.SingleOpeningConcreteCoverage
