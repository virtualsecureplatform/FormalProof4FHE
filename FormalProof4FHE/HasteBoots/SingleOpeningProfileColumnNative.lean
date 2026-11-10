module
public import FormalProof4FHE.HasteBoots.SingleOpeningProfileColumnExposure
@[expose] public section

/-! The actual single-opening preparation and retained code constructor
supply eligibility at its first column read: original label, positive quota,
code domain and full coefficient count. No caller eligibility certificate. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningProfileColumnNative
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open SingleOpeningChallengeLink (View)
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeIndexExposureRisk (Packet)
open TranscriptFrame (Frame)
open OracleProgram (run)
noncomputable section

theorem selected_native {S A : Type} {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.transcript.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded)
    (origin : CacheBackedSingleOpening.Origin ctx)
    (step : S → OracleMachine.Command S A) (packet : Packet S A)
    (first : CausalStreamExposure.firstRead step packet = some (SingleOpeningColumnLaw.input receipt world)) :
    SingleOpeningProfileColumnExposure.select ctx step packet = some decoded := by
  obtain ⟨fieldCount,_,_,_,_,_,_,_,_,domain,count,label,_⟩ :=
    SingleOpeningPreparedChallenge.parsed_origin receipt prepared before parent valid fits responseFits decoded parsed
  have geometry := NativeBrakedownParameters.build_spec NativeGoldBlockCode.description ctx.parameters work.geometry
    (SingleOpeningRectangularData.geometry ctx world work prepared)
  have positive : 0 < ctx.parameters.queries.val := Nat.pos_of_ne_zero geometry.basic.2.2.2
  have power := (NativeGoldBlockCodeMeaning.constructor_log origin.tables origin.request.message origin.request.block
    origin.request.blowup ctx.parameters.code origin.constructed).2
  unfold SingleOpeningProfileColumnExposure.select
  simp only [first,Option.bind_eq_bind,Option.bind_some,parsed]
  have coefficients : decoded.field.count.val = SingleOpeningFieldMatrix.count ctx := by
    rw [fieldCount]
    exact SingleOpeningFieldMatrix.prepared_count ctx world work prepared
  exact ite_eq_left ⟨label,by rw [count]; exact positive,by rw [domain]; exact power,count,coefficients⟩

end
end FormalProof4FHE.HasteBoots.SingleOpeningProfileColumnNative
