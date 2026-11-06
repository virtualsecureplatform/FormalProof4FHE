module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteCoverage
@[expose] public section

/-! Actual first-column reads enter the concrete selector. Missing old
field sources enter the existing early-receipt event, without a supplied
receipt or collector-completion certificate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteExposureCoverage
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeTranscript (Observation)
open NativeGoldColumnAuthentication (encoding)
open NativeGoldBatchChallengeLink (View)
open NativeGoldBlockCode (Tables logSize)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeIndexExposureRisk (Packet)
open TranscriptFrame (Frame)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem selected_native {S A : Type} (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (first : CausalStreamExposure.firstRead step packet = some (NativeGoldBatchColumnRequestLaw.input ctx work world)) :
    NativeGoldBatchConcreteColumnExposure.select ctx step packet = some decoded := by
  obtain ⟨_,_,_,_,_,_,_,_,_,domain,count,label,_⟩ :=
    NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared before parent valid fits responseFits decoded parsed
  have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work prepared)
  have positive : 0 < ctx.parameters.queries.val := Nat.pos_of_ne_zero geometry.basic.2.2.2
  have power := (NativeGoldBlockCodeMeaning.constructor_log tables message block blowup ctx.parameters.code constructed).2
  unfold NativeGoldBatchConcreteColumnExposure.select
  simp only [first,Option.bind_eq_bind,Option.bind_some,parsed]
  exact ite_eq_left ⟨label,by rw [count]; exact positive,by rw [domain]; exact power⟩

theorem source_or_early {S A : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (width : 3 ≤ ctx.parameters.width.val)
    (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (first : CausalStreamExposure.firstRead step packet = some (NativeGoldBatchColumnRequestLaw.input ctx work world)) :
    (∃ sourceLog, NativeGoldBatchFirstFieldSource.recover dummy packet.2 decoded.field = some sourceLog) ∨
      NativeEarlyReceiptBound.event ctx.parent.profile step packet world := by
  have phase := (NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared before parent valid fits responseFits decoded parsed).2.1
  have inputEq : NativeGoldBatchFirstFieldSource.input decoded.field = (NativeGoldBatchRandomLaw.phase work).pending.input := by
    rw [← phase,NativeGoldBatchFieldInputView.phase_input]
    rfl
  obtain seen | early := NativeGoldBatchRecoveredCollector.first_column_cases ctx world work prepared before parent valid fits responseFits width step packet first
  · left
    apply NativeGoldBatchFirstFieldSource.recover_exists
    rw [inputEq]
    exact seen
  · exact Or.inr early
/-- With an actual recovered source, the native false-claim split uses the
same causal event as the existing conditional and lifetime column bounds. -/
theorem accepted_first_column_cases {S A Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (first : CausalStreamExposure.firstRead step packet = some (NativeGoldBatchColumnRequestLaw.input ctx work world))
    (suffix : List Observation) (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world (packet.2++suffix) ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world (packet.2++suffix))
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed dummy (packet.2++suffix)))
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (radius : ℕ)
    (width : 3 ≤ ctx.parameters.width.val)
    (falseClaim : ∀ sourceLog, NativeGoldBatchFirstFieldSource.recover dummy packet.2 decoded.field = some sourceLog → ∃ query : NativeGoldBatchRectangularData.Query work,
      (fun lane : Fin ctx.parameters.width.val => NativeGoldBatchFixedResponseData.claimed decoded.field.data.values query.val lane.val) ≠
        matrixEvaluation (NativeGoldBatchFixedResponseData.leftAt ctx.parameters decoded.field.data.queries query.val)
          (NativeGoldBatchFixedResponseData.rightAt ctx.parameters decoded.field.data.queries query.val)
          (RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity radius (NativeGoldBatchConcreteColumnFamily.source dummy ctx decoded sourceLog))) :
    NativeEarlyReceiptBound.event ctx.parent.profile step packet world ∨
      ∃ sourceLog, NativeGoldBatchFirstFieldSource.recover dummy packet.2 decoded.field = some sourceLog ∧
        (NativeGoldBatchConcreteCoverage.Proximity dummy ctx primitive decoded sourceLog work.state radius ∨
          NativeGoldBatchConcreteColumnExposure.event dummy ctx primitive ctx.parent.profile step packet radius world) := by
  have nativeAccepted := accepted
  obtain ⟨⟨frames,parent,valid,fits⟩,completion,_,executed,_,_⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  have selected := selected_native ctx world work prepared frames parent valid fits responseFits decoded parsed tables message block blowup constructed step packet first
  obtain available | early := source_or_early dummy ctx world work prepared frames parent valid fits responseFits decoded parsed width step packet first
  · obtain ⟨sourceLog,found⟩ := available
    right
    refine ⟨sourceLog,found,?_⟩
    obtain proximity | column := NativeGoldBatchConcreteCoverage.false_claim_cases dummy ctx world work tables message block blowup constructed primitive
      choose fuel memory packet.2 suffix decoded parsed responseFits sourceLog found nativeAccepted truthful noDisagreement capacity radius (falseClaim sourceLog found)
    · exact Or.inl proximity
    · right
      unfold NativeGoldBatchConcreteColumnExposure.event
      rw [selected]
      exact column
  · exact Or.inl early
/-- Source disagreement remains an explicit global failure branch. -/
theorem accepted_first_column_cover {S A Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory)
    (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (first : CausalStreamExposure.firstRead step packet = some (NativeGoldBatchColumnRequestLaw.input ctx work world))
    (suffix : List Observation) (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (accepted : NativeGoldBatchAnySourceRisk.Accepted world (packet.2++suffix) ctx choose fuel memory work)
    (truthful : ObservationReplay.Agrees world (packet.2++suffix))
    (capacity : ctx.parameters.code.messageLength.val ≤ ctx.parameters.code.messageBlocks.val*ctx.parameters.code.blockWidth.val)
    (radius : ℕ)
    (width : 3 ≤ ctx.parameters.width.val)
    (falseClaim : ∀ sourceLog, NativeGoldBatchFirstFieldSource.recover dummy packet.2 decoded.field = some sourceLog → ∃ query : NativeGoldBatchRectangularData.Query work,
      (fun lane : Fin ctx.parameters.width.val => NativeGoldBatchFixedResponseData.claimed decoded.field.data.values query.val lane.val) ≠
        matrixEvaluation (NativeGoldBatchFixedResponseData.leftAt ctx.parameters decoded.field.data.queries query.val)
          (NativeGoldBatchFixedResponseData.rightAt ctx.parameters decoded.field.data.queries query.val)
          (RectangularMatrixOpeningKernel.extract (NativeGoldBatchResponseMeaning.Domain ctx primitive) capacity radius (NativeGoldBatchConcreteColumnFamily.source dummy ctx decoded sourceLog))) :
    CheckpointAvailability.Disagreement encoding dummy NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed dummy (packet.2++suffix)) ∨
    NativeEarlyReceiptBound.event ctx.parent.profile step packet world ∨
      ∃ sourceLog, NativeGoldBatchFirstFieldSource.recover dummy packet.2 decoded.field = some sourceLog ∧
        (NativeGoldBatchConcreteCoverage.Proximity dummy ctx primitive decoded sourceLog work.state radius ∨
          NativeGoldBatchConcreteColumnExposure.event dummy ctx primitive ctx.parent.profile step packet radius world) := by
  classical
  by_cases failed : CheckpointAvailability.Disagreement encoding dummy NativeMerkleShapeFamily.shape
      (NativeGoldBatchFamilyAvailability.reconstructed dummy (packet.2++suffix))
  · exact Or.inl failed
  · right
    exact accepted_first_column_cases dummy ctx world work tables message block blowup constructed primitive choose fuel memory
      step packet first suffix decoded parsed responseFits accepted truthful failed capacity radius width falseClaim

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteExposureCoverage
