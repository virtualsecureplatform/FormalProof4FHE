module
public import FormalProof4FHE.HasteBoots.NativeIndexInputValues
public import FormalProof4FHE.HasteBoots.NativeGoldBatchPreparedChallenge
@[expose] public section

/-! The parsed complete native nonce reproduces the original ordered draws,
including every duplicate. No prior full receipt read or freshness premise
is needed for this pointwise execution identity. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchParsedDraws
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBatchChallengeLink (View)
open NativeGoldBlockCode (Tables logSize)
open InputIndexedOracle (World)
open TranscriptFrame (Frame)
open OracleProgram (run)
noncomputable section

theorem values_typed (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded) :
    NativeIndexFirstReadLaw.values (logSize ctx.parameters.code) (decoded.column.index.request ctx.parent.profile).transcript
      decoded.column.index.label decoded.column.index.domain decoded.column.index.count world =
      NativeGoldPcsDraws.typed (logSize ctx.parameters.code) decoded.column.index.count.val work.sample.draws := by
  obtain ⟨_,_,_,_,_,_,_,_,_,domain,count,label,_⟩ :=
    NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared before parent valid fits responseFits decoded parsed
  have linked := NativeGoldBatchChallengeLink.parse_sound _ decoded parsed ctx.parent.profile
  have inputEq := (NativeGoldBatchColumnInputView.parse_sound _ decoded.column linked.1 ctx.parent.profile).1
  rw [domain,count,label] at inputEq ⊢
  have same := NativeIndexInputValues.input_congr (logSize ctx.parameters.code) (decoded.column.index.request ctx.parent.profile).transcript
    (NativeGoldBatchColumnRequestLaw.transcript ctx work world) NativeGoldBatchColumns.label ctx.parameters.code.blocks ctx.parameters.queries
    (NativeGoldBatchColumnRequestLaw.prepared_check ctx world work prepared) inputEq world
  exact same.trans (NativeGoldBatchColumnRequestLaw.values_original ctx world work prepared)

theorem draws (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (tables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build tables message block blowup = .ok ctx.parameters.code)
    (before : List Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded) :
    ∃ draw, NativeIndexFirstReadLaw.values (logSize ctx.parameters.code) (decoded.column.index.request ctx.parent.profile).transcript
      decoded.column.index.label decoded.column.index.domain decoded.column.index.count world = some draw ∧
      (List.ofFn draw).map Fin.val = work.sample.draws := by
  have values := values_typed ctx world work prepared before parent valid fits responseFits decoded parsed
  have count := (NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared before parent valid fits responseFits decoded parsed).2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨draw,typed,ordered,_⟩ := NativeGoldBatchDraws.prepared_typed ctx world work prepared tables message block blowup constructed
  rw [count] at values ⊢
  exact ⟨draw,values.trans typed,ordered⟩
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchParsedDraws
