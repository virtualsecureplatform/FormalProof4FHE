module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchProfileColumnExposure
public import FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteExposureCoverage
@[expose] public section

/-! Native execution derives the trusted quota and complete coefficient count
at the actual first column read. Restricting the exposure charge preserves
accepted native coverage without a supplied eligibility certificate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchProfileColumnNative
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBatchChallengeLink (View)
open NativeGoldBlockCode (Tables logSize)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeIndexExposureRisk (Packet)
open TranscriptFrame (Frame)
open OracleProgram (run)
noncomputable section

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
    NativeGoldBatchProfileColumnExposure.select ctx step packet = some decoded := by
  obtain ⟨fieldCount,_,_,_,_,_,_,_,_,domain,count,label,_⟩ :=
    NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared before parent valid fits responseFits decoded parsed
  have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work prepared)
  have positive : 0 < ctx.parameters.queries.val := Nat.pos_of_ne_zero geometry.basic.2.2.2
  have power := (NativeGoldBlockCodeMeaning.constructor_log tables message block blowup ctx.parameters.code constructed).2
  unfold NativeGoldBatchProfileColumnExposure.select
  simp only [first,Option.bind_eq_bind,Option.bind_some,parsed]
  have coefficients : decoded.field.count.val = NativeGoldBatchFieldMatrix.count ctx := by
    rw [fieldCount,geometry.computed]
    rfl
  exact ite_eq_left ⟨label,by rw [count]; exact positive,by rw [domain]; exact power,count,coefficients⟩

theorem event_of_native {S A : Type} (ctx : Context) (world : World) (work : Prepared)
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
    (first : CausalStreamExposure.firstRead step packet = some (NativeGoldBatchColumnRequestLaw.input ctx work world))
    (dummy : Digest)
    (primitive : IsPrimitiveRoot (NativeFieldRepresentation.goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (radius : ℕ)
    (event : NativeGoldBatchConcreteColumnExposure.event dummy ctx primitive ctx.parent.profile step packet radius world) :
    NativeGoldBatchProfileColumnExposure.event dummy ctx primitive ctx.parent.profile step packet radius world := by
  have broad := NativeGoldBatchConcreteExposureCoverage.selected_native ctx world work prepared before parent valid fits responseFits decoded parsed
    tables message block blowup constructed step packet first
  have filtered := selected_native ctx world work prepared before parent valid fits responseFits decoded parsed
    tables message block blowup constructed step packet first
  unfold NativeGoldBatchConcreteColumnExposure.event at event
  unfold NativeGoldBatchProfileColumnExposure.event
  rw [broad] at event
  rw [filtered]
  exact event
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchProfileColumnNative
