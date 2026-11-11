module
public import FormalProof4FHE.HasteBoots.NativeIndexInputValues
public import FormalProof4FHE.HasteBoots.SingleOpeningPreparedChallenge
@[expose] public section

/-! Parsing the actual complete single-opening nonce preserves the original
ordered native sample. No freshness or fully read receipt is assumed. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningParsedDraws
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open InputIndexedOracle (World)
open TranscriptFrame (Frame)
open OracleProgram (run)
noncomputable section

theorem values_typed {ctx : Context} {world : World} {work : Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.transcript.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : (NativeGoldPcsWire.opening ctx.root ctx.query ctx.claimed).length < TranscriptFrame.lengthLimit)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded) :
    NativeIndexFirstReadLaw.values (NativeGoldBlockCode.logSize ctx.parameters.code)
      (decoded.column.index.request ctx.transcript.profile).transcript decoded.column.index.label
      decoded.column.index.domain decoded.column.index.count world =
      NativeGoldPcsDraws.typed (NativeGoldBlockCode.logSize ctx.parameters.code) decoded.column.index.count.val sample.draws := by
  obtain ⟨_,_,_,_,_,_,_,_,_,domain,count,label,_⟩ :=
    SingleOpeningPreparedChallenge.parsed_origin receipt prepared before parent valid fits responseFits decoded parsed
  have linked := SingleOpeningChallengeLink.parse_sound _ decoded parsed ctx.transcript.profile
  have inputEq := (SingleOpeningColumnInputView.parse_sound _ decoded.column linked.1 ctx.transcript.profile).1
  rw [domain,count,label] at inputEq ⊢
  have same := NativeIndexInputValues.input_congr (NativeGoldBlockCode.logSize ctx.parameters.code)
    (decoded.column.index.request ctx.transcript.profile).transcript (SingleOpeningColumnLaw.transcript receipt world)
    NativeGoldPcsColumns.label ctx.parameters.code.blocks ctx.parameters.queries (SingleOpeningColumnLaw.prepared_check receipt) inputEq world
  exact same.trans (SingleOpeningColumnLaw.values_original receipt)

end
end FormalProof4FHE.HasteBoots.SingleOpeningParsedDraws
