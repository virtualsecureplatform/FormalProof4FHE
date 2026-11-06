module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteAcceptedChecks
public import FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteColumnWitness
@[expose] public section

/-! Pointwise coverage of actual accepted false claims with a recovered
source. The matrix-proximity obstruction is explicit; this is not yet the
public application extractor or a physical-work bound. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteCoverage
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldBlockCode (Tables logSize)
open NativeGoldColumnAuthentication (encoding)
open NativeGoldBatchConcreteColumnFamily (source raw claim Test Position Symbol)
open NativeGoldBatchConcreteColumnBound (distance)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem witnessed_event {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (columnHistory suffix : List Observation) (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (sourceLog : NativeRootFamilySourceSelection.Log)
    (found : NativeGoldBatchFirstFieldSource.recover dummy columnHistory decoded.field = some sourceLog)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world (columnHistory++suffix) ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world (columnHistory++suffix))
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed dummy (columnHistory++suffix)))
    (radius : ℕ)
    (witness : ∃ test : Test ctx decoded, distance ctx primitive radius ≤
      hammingDist (raw dummy ctx decoded sourceLog work.state test) (claim ctx primitive decoded work.state test)) :
    NativeGoldBatchConcreteColumnBound.event dummy ctx primitive ctx.parent.profile decoded columnHistory radius world := by
  obtain ⟨draw,sampled,_,checks⟩ := NativeGoldBatchConcreteAcceptedChecks.accepted_checks dummy ctx world work tables message block blowup
    constructed primitive choose fuel memory columnHistory suffix decoded parsed responseFits sourceLog found accepted truthful noDisagreement
  obtain ⟨⟨frames,parent,valid,fits⟩,completion,_,executed,_,_⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  have collected := (NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared frames parent valid fits responseFits decoded parsed).2.2.1
  have complete := NativeGoldBatchRecoveredCollector.prepared_complete ctx world work prepared
  unfold NativeGoldBatchConcreteColumnBound.event
  rw [found]
  refine ⟨ctx.fieldFuel,?_⟩
  unfold NativeGoldBatchFieldColumnLaw.event
  rw [sampled]
  simp only [Option.elim_some,collected]
  exact ⟨complete,witness,checks⟩

def Near (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (decoded : NativeGoldBatchChallengeLink.View) (sourceLog : NativeRootFamilySourceSelection.Log) (radius : ℕ) : Prop :=
  ∃ close, CommonSource.RowsIn (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive)
    ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val) close ∧
    hammingDist (source dummy ctx decoded sourceLog) close ≤ radius

def Proximity (dummy : Digest) (ctx : Context)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (decoded : NativeGoldBatchChallengeLink.View) (sourceLog : NativeRootFamilySourceSelection.Log)
    (state : NativeFieldVector.State) (radius : ℕ) : Prop :=
  ¬Near dummy ctx primitive decoded sourceLog radius ∧
  ∀ lane : Fin ctx.parameters.width.val,
    Code.distFromCode (StructuredOpening.combine (NativeGoldBatchRecoveredMatrix.random ctx state lane) (source dummy ctx decoded sourceLog))
      (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
        Set (Position ctx → Symbol ctx)) ≤ radius

theorem false_claim_cases {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (columnHistory suffix : List Observation) (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (sourceLog : NativeRootFamilySourceSelection.Log)
    (found : NativeGoldBatchFirstFieldSource.recover dummy columnHistory decoded.field = some sourceLog)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world (columnHistory++suffix) ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world (columnHistory++suffix))
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed dummy (columnHistory++suffix)))
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (radius : ℕ)
    (falseClaim : ∃ query : NativeGoldBatchRectangularData.Query work,
      (fun lane : Fin ctx.parameters.width.val => NativeGoldBatchFixedResponseData.claimed decoded.field.data.values query.val lane.val) ≠
        matrixEvaluation (NativeGoldBatchFixedResponseData.leftAt ctx.parameters decoded.field.data.queries query.val)
          (NativeGoldBatchFixedResponseData.rightAt ctx.parameters decoded.field.data.queries query.val)
          (RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity radius (source dummy ctx decoded sourceLog))) :
    Proximity dummy ctx primitive decoded sourceLog work.state radius ∨
      NativeGoldBatchConcreteColumnBound.event dummy ctx primitive ctx.parent.profile decoded columnHistory radius world := by
  classical
  have spec := NativeGoldBlockCode.build_spec tables message block blowup ctx.parameters.code constructed
  let : NeZero ctx.parameters.code.blockWidth.val := ⟨by rw [spec.blockEq]; exact spec.dimensions.2.1⟩
  by_cases near : Near dummy ctx primitive decoded sourceLog radius
  · right
    apply witnessed_event dummy ctx world work tables message block blowup constructed primitive choose fuel memory
      columnHistory suffix decoded parsed responseFits sourceLog found accepted truthful noDisagreement radius
    exact NativeGoldBatchConcreteColumnWitness.near_distance dummy ctx world work tables message block blowup constructed primitive
      (columnHistory++suffix) choose fuel memory accepted responseFits decoded parsed capacity sourceLog work.state radius near falseClaim
  · by_cases allNear : ∀ lane : Fin ctx.parameters.width.val,
        Code.distFromCode (StructuredOpening.combine (NativeGoldBatchRecoveredMatrix.random ctx work.state lane) (source dummy ctx decoded sourceLog))
          (BlockCode.code (NativeGoldBatchResponseMeaning.Domain ctx primitive) ctx.parameters.code.messageBlocks.val ctx.parameters.code.blockWidth.val :
            Set (Position ctx → Symbol ctx)) ≤ radius
    · exact Or.inl ⟨near,allNear⟩
    · right
      apply witnessed_event dummy ctx world work tables message block blowup constructed primitive choose fuel memory
        columnHistory suffix decoded parsed responseFits sourceLog found accepted truthful noDisagreement radius
      exact NativeGoldBatchConcreteColumnWitness.far_distance dummy ctx primitive decoded sourceLog work.state radius allNear

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteCoverage
