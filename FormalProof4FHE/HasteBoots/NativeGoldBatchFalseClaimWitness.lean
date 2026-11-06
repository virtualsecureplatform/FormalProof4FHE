module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchParsedResponseData
public import FormalProof4FHE.HasteBoots.RectangularBatchDisagreement
@[expose] public section

/-! Actual accepted native finishing turns a false original claimed value
into a shared structured-column disagreement. All response and query data
below are computed from the parsed nonce and fixed parameters. This is a
pointwise near-source lemma; global Fiat–Shamir, public extraction and
physical-work security still require their separate reductions. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchFalseClaimWitness
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldBatchRectangularData (Group Query groupOf)
open NativeGoldBatchRectangularWeights (Row)
open NativeGoldBlockCode (Tables logSize)
open NativeFieldRepresentation (goldValue)
open NativeFields (Goldilocks)
open NativeGoldBatchChallengeLink (View)
open NativeGoldBatchFixedResponseData (leftAt groupLeft rightAt messages claimed)
open InputIndexedOracle (World)
open NativeTranscript (Observation)
open OracleProgram (run)
noncomputable section

theorem near_witness {Memory : Type} (ctx : Context) (world : World) (work : Prepared)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (history : List Observation) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world history ctx choose fuel memory work)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (radius : ℕ)
    (sourceWord : Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks)
    (near : ∃ source, CommonSource.RowsIn (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val) source ∧ hammingDist sourceWord source ≤ radius)
    (falseClaim : ∃ query : Query work,
      (fun lane : Fin ctx.parameters.width.val => claimed decoded.field.data.values query.val lane.val) ≠
        matrixEvaluation (leftAt ctx.parameters decoded.field.data.queries query.val) (rightAt ctx.parameters decoded.field.data.queries query.val)
          (RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity radius sourceWord)) :
    ∃ group : ℕ, group < NativeGoldQueryGroups.groupCount ctx.parameters.leftVariables.val decoded.field.data.queries ∧
      ∃ lane : Fin ctx.parameters.width.val, Code.minDist (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
        ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (Fin (2^(logSize ctx.parameters.code)) → Fin ctx.parameters.code.blockWidth.val → Goldilocks)) - radius ≤
      hammingDist
        (StructuredOpening.combine (RectangularMatrixResponse.weights
          (groupLeft ctx.parameters decoded.field.data.queries group) lane) sourceWord)
        (BlockEncoder.encode (NativeGoldBatchResponseMeaning.Domain ctx primitive)
          (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
            (messages ctx.parameters decoded.column.opening group lane.val))) := by
  obtain ⟨⟨before,parent,valid,fits⟩,completion,next,executed,status,_⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  have binding := NativeGoldBatchParsedResponseData.binding_of_native ctx world work prepared before parent valid fits responseFits decoded parsed
  have dimensions := NativeGoldBlockCodeMeaning.constructor_dimensions tables message block blowup ctx.parameters.code constructed
  have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work prepared)
  let : NeZero ctx.parameters.code.messageBlocks.val := ⟨Nat.ne_of_gt dimensions.1⟩
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨geometry.code.2.2.2.2⟩
  have rightEq : NativeGoldBatchRectangularData.right ctx world work prepared =
      fun query => rightAt ctx.parameters decoded.field.data.queries query.val :=
    funext (fun query => (NativeGoldBatchParsedResponseData.right_native ctx world work decoded prepared binding query).symm)
  have messagesEq : NativeGoldBatchRectangularData.messages ctx work =
      fun group lane => messages ctx.parameters decoded.column.opening group.val lane.val :=
    funext (fun group => (NativeGoldBatchParsedResponseData.messages_native ctx work decoded binding group).symm)
  have finished (query : Query work) :
      (fun lane : Fin ctx.parameters.width.val => claimed decoded.field.data.values query.val lane.val) =
      RectangularBatchOpeningKernel.finishMessage (groupOf ctx work)
        (fun query => rightAt ctx.parameters decoded.field.data.queries query.val)
        (fun group lane => messages ctx.parameters decoded.column.opening group.val lane.val) query := by
    rw [NativeGoldBatchParsedResponseData.claimed_native ctx work decoded binding query]
    have result := NativeGoldBatchRectangularData.accepted_claim ctx world work prepared choose fuel memory completion executed next status query
    rw [rightEq,messagesEq] at result
    exact result
  have generic := RectangularBatchDisagreement.near_witness (NativeGoldBatchResponseMeaning.Domain ctx primitive)
    (by simpa only [Fintype.card_fin] using Nat.le_of_lt dimensions.2.1) capacity radius sourceWord
    (groupOf ctx work) (fun group => groupLeft ctx.parameters decoded.field.data.queries group.val)
    (fun query => rightAt ctx.parameters decoded.field.data.queries query.val)
    (fun group lane => messages ctx.parameters decoded.column.opening group.val lane.val) near
  have falseFinish : ∃ query : Query work,
      RectangularBatchOpeningKernel.finishMessage (groupOf ctx work)
        (fun query => rightAt ctx.parameters decoded.field.data.queries query.val)
        (fun group lane => messages ctx.parameters decoded.column.opening group.val lane.val) query ≠
      matrixEvaluation (groupLeft ctx.parameters decoded.field.data.queries (groupOf ctx work query).val)
        (rightAt ctx.parameters decoded.field.data.queries query.val)
        (RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity radius sourceWord) := by
    obtain ⟨query,different⟩ := falseClaim
    refine ⟨query,?_⟩
    have grouped : groupLeft ctx.parameters decoded.field.data.queries (groupOf ctx work query).val =
        leftAt ctx.parameters decoded.field.data.queries query.val := by
      rw [NativeGoldBatchParsedResponseData.groupLeft_native ctx world work decoded prepared binding,
        NativeGoldBatchRectangularData.original_left,
        ← NativeGoldBatchParsedResponseData.left_native ctx world work decoded prepared binding]
    rw [← finished query,grouped]
    exact different
  obtain ⟨test,distance⟩ := generic falseFinish
  refine ⟨test.1.val,?_,test.2,distance⟩
  rw [binding.queries]
  exact test.1.isLt

/-- Outside the matrix proximity event, an actual recovered test row and
its parsed raw response supply a radius+1 witness with no response certificate. -/
theorem far_witness (ctx : Context) [NeZero ctx.parameters.code.blockWidth.val]
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (decoded : View) (state : NativeFieldVector.State) (radius : ℕ)
    (sourceWord : Fin (2^(logSize ctx.parameters.code)) → Row ctx → Fin ctx.parameters.code.blockWidth.val → Goldilocks)
    (outside : ¬∀ lane : Fin ctx.parameters.width.val,
      Code.distFromCode (StructuredOpening.combine (NativeGoldBatchRecoveredMatrix.random ctx state lane) sourceWord)
        (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
          Set (Fin (2^(logSize ctx.parameters.code)) → Fin ctx.parameters.code.blockWidth.val → Goldilocks)) ≤ radius) :
    ∃ lane : Fin ctx.parameters.width.val, radius+1 ≤
      hammingDist (StructuredOpening.combine (NativeGoldBatchRecoveredMatrix.random ctx state lane) sourceWord)
        (BlockEncoder.encode (NativeGoldBatchResponseMeaning.Domain ctx primitive)
          (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
            (NativeGoldBatchFixedResponseData.testMessages ctx.parameters decoded.column.opening lane.val))) :=
  RectangularBatchDisagreement.far_witness (NativeGoldBatchResponseMeaning.Domain ctx primitive) radius ctx.parameters.width.val
    sourceWord (NativeGoldBatchRecoveredMatrix.random ctx state)
    (fun lane => BlockEncoder.encode (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      (RowLayout.padded (m := ctx.parameters.code.messageBlocks.val) (b := ctx.parameters.code.blockWidth.val)
        (NativeGoldBatchFixedResponseData.testMessages ctx.parameters decoded.column.opening lane.val)))
    (fun _ => BlockEncoder.encode_mem_code _ _) outside

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchFalseClaimWitness
