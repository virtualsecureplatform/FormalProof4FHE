module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteColumnExposure
@[expose] public section

/-! Native false-claim witnesses enter the concrete combined family at the
single minimum distance used by its causal bound. These are pointwise
witness lifts, not complete application event coverage or physical work. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteColumnWitness
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldBatchConcreteColumnFamily (source raw claim Test Position)
open NativeGoldBatchConcreteColumnBound (distance)
open NativeGoldBatchChallengeLink (View)
open NativeRootMessage (Digest)
open NativeRootFamilySourceSelection (Log)
open NativeGoldBlockCode (Tables logSize)
open NativeGoldBatchFixedResponseData (leftAt rightAt claimed)
open InputIndexedOracle (World)
open NativeTranscript (Observation)
open OracleProgram (run)
noncomputable section

theorem near_distance {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (history : List Observation) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world history ctx choose fuel memory work)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : View) (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (sourceLog : Log) (state : NativeFieldVector.State) (radius : ℕ)
    (near : ∃ close, CommonSource.RowsIn (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
      ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val) close ∧ hammingDist (source dummy ctx decoded sourceLog) close ≤ radius)
    (falseClaim : ∃ query : NativeGoldBatchRectangularData.Query work,
      (fun lane : Fin ctx.parameters.width.val => claimed decoded.field.data.values query.val lane.val) ≠
        matrixEvaluation (leftAt ctx.parameters decoded.field.data.queries query.val) (rightAt ctx.parameters decoded.field.data.queries query.val)
          (RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity radius (source dummy ctx decoded sourceLog))) :
    ∃ test : Test ctx decoded, distance ctx primitive radius ≤
      hammingDist (raw dummy ctx decoded sourceLog state test) (claim ctx primitive decoded state test) := by
  have branch := NativeGoldBatchFalseClaimWitness.near_witness ctx world work tables message block blowup constructed primitive
    history choose fuel memory accepted responseFits decoded parsed capacity radius (source dummy ctx decoded sourceLog) near falseClaim
  obtain ⟨test,bounded⟩ := NativeGoldBatchConcreteColumnFamily.structured_witness dummy ctx primitive decoded sourceLog state _ branch
  exact ⟨test,(Nat.min_le_left _ _).trans bounded⟩

theorem far_distance (dummy : Digest) (ctx : Context) [NeZero ctx.parameters.code.blockWidth.val]
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (decoded : View) (sourceLog : Log) (state : NativeFieldVector.State) (radius : ℕ)
    (outside : ¬∀ lane : Fin ctx.parameters.width.val,
      Code.distFromCode (StructuredOpening.combine (NativeGoldBatchRecoveredMatrix.random ctx state lane) (source dummy ctx decoded sourceLog))
        (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
          Set (Position ctx → NativeGoldBatchConcreteColumnFamily.Symbol ctx)) ≤ radius) :
    ∃ test : Test ctx decoded, distance ctx primitive radius ≤
      hammingDist (raw dummy ctx decoded sourceLog state test) (claim ctx primitive decoded state test) := by
  have branch := NativeGoldBatchFalseClaimWitness.far_witness ctx primitive decoded state radius (source dummy ctx decoded sourceLog) outside
  obtain ⟨test,bounded⟩ := NativeGoldBatchConcreteColumnFamily.random_witness dummy ctx primitive decoded sourceLog state _ branch
  exact ⟨test,(Nat.min_le_right _ _).trans bounded⟩
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteColumnWitness
