module
public import FormalProof4FHE.HasteBoots.SingleOpeningSelectedChecks
public import FormalProof4FHE.HasteBoots.RectangularMatrixDisagreement
@[expose] public section

/-! Actual single-opening finishing turns falsity against the common source
extractor into a structured-column disagreement in the near-source branch.
All query/claim/response data are recovered from the original native nonce. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningFalseClaimWitness
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsProgram (Scheduler)
open InputIndexedOracle (World)
open NativeTranscript (Observation)
open SingleOpeningChallengeLink (View)
open SingleOpeningFixedResponseData (left right messages claimed)
open SingleOpeningConcreteColumnFamily (Domain Position Symbol)
noncomputable section

theorem finishes {Memory : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (history : List Observation) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : SingleOpeningAvailability.Accepted world history ctx choose fuel memory work)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : View) (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded) :
    claimed ctx decoded.field.data.claimed = RectangularMatrixResponse.finishMessage
      (right ctx.parameters decoded.field.data.query) (messages ctx decoded.column.opening) := by
  obtain ⟨⟨before,parent,valid,fits⟩,completion,next,executed,status,_⟩ := accepted
  have prepared := (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  obtain ⟨_,_,_,_,_,evaluation,_,query,claim,_,_,_,_⟩ :=
    SingleOpeningPreparedChallenge.parsed_origin receipt prepared before parent valid fits responseFits decoded parsed
  have messageEq : messages ctx decoded.column.opening = SingleOpeningRectangularData.messages ctx ctx.opening.evaluation.val := by
    simp only [messages,evaluation]
  rw [query,claim,SingleOpeningFixedResponseData.right_native ctx world work prepared,messageEq]
  exact SingleOpeningRectangularData.accepted_claim ctx world work prepared choose fuel memory completion executed next status

theorem near_witness {Memory : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample) (origin : CacheBackedSingleOpening.Origin ctx)
    (history : List Observation) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : SingleOpeningAvailability.Accepted world history ctx choose fuel memory work)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : View) (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded)
    (radius : ℕ) (sourceWord : Position ctx → SingleOpeningRectangularData.Row ctx → Symbol ctx)
    (near : ∃ close, CommonSource.RowsIn (BlockCode.code (Domain ctx origin.primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val) close ∧ hammingDist sourceWord close ≤ radius)
    (falseClaim : claimed ctx decoded.field.data.claimed ≠ matrixEvaluation
      (left ctx.parameters decoded.field.data.query) (right ctx.parameters decoded.field.data.query)
      (RectangularMatrixOpeningKernel.extract (Domain ctx origin.primitive) origin.capacity radius sourceWord)) :
    ∃ lane : Fin ctx.parameters.width.val,
      Code.minDist (BlockCode.code (Domain ctx origin.primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (Position ctx → Symbol ctx)) - radius ≤
      hammingDist (StructuredOpening.combine (RectangularMatrixResponse.weights (left ctx.parameters decoded.field.data.query) lane) sourceWord)
        (BlockEncoder.encode (Domain ctx origin.primitive)
          (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
            (messages ctx decoded.column.opening lane))) := by
  have finished := finishes receipt history choose fuel memory accepted responseFits decoded parsed
  have acceptedCopy := accepted
  obtain ⟨_,completion,_,executed,_,_⟩ := acceptedCopy
  have prepared := (NativeGoldPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
    (SingleOpeningRectangularData.geometry ctx world work prepared)
  have dimensions := NativeGoldBlockCodeMeaning.constructor_dimensions origin.tables origin.request.message origin.request.block
    origin.request.blowup ctx.parameters.code origin.constructed
  let : NeZero ctx.parameters.code.messageBlocks.val := ⟨Nat.ne_of_gt dimensions.1⟩
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨geometry.code.2.2.2.2⟩
  rw [finished] at falseClaim
  exact RectangularMatrixDisagreement.near_witness (Domain ctx origin.primitive)
    (by simpa only [Fintype.card_fin] using Nat.le_of_lt dimensions.2.1) origin.capacity radius sourceWord
    (left ctx.parameters decoded.field.data.query) (right ctx.parameters decoded.field.data.query)
    (messages ctx decoded.column.opening) near falseClaim

end
end FormalProof4FHE.HasteBoots.SingleOpeningFalseClaimWitness
