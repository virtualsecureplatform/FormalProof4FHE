module
public import FormalProof4FHE.HasteBoots.GoldCommonSourceTable
public import FormalProof4FHE.HasteBoots.GoldContextCollision
@[expose] public section

/-! Actual native preparation and strict parsing bind the common analysis
table to the computed parameter digest and original commitment root.
Exact old-log association and application ownership remain separate. -/
namespace FormalProof4FHE.HasteBoots.GoldCommonSourceBinding
open NativeRootMessage (Digest)
open NativeRootFamilySourceSelection (Log)
open InputIndexedOracle (World sha512)
open OracleProgram (run)
open GoldCommonSourceTable (Primitive Capacity table)
noncomputable section

/-- The context/root in a parsed original batch are execution conclusions. -/
theorem batch_binding (ctx : NativeGoldBatchPcsProgram.Context) (world : World) (work : NativeGoldBatchPcsProgram.Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (framed : NativeGoldBatchSourceRisk.Framed ctx)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded) :
    decoded.field.data.context = sha512 world (GoldContextInput.bytes ctx.parameters) ∧ decoded.field.data.root = ctx.root := by
  obtain ⟨before,parent,valid,fits⟩ := framed
  obtain ⟨_,_,_,_,_,_,root,_,_,_,_,_,computed⟩ := NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared
    before parent valid fits responseFits decoded parsed
  rw [GoldContextCollision.context_run] at computed
  exact ⟨(Option.some.inj computed).symm,root⟩

theorem batch_table (dummy : Digest) (ctx : NativeGoldBatchPcsProgram.Context)
    (primitive : Primitive ctx.parameters) (capacity : Capacity ctx.parameters)
    (world : World) (work : NativeGoldBatchPcsProgram.Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (framed : NativeGoldBatchSourceRisk.Framed ctx)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : NativeGoldBatchChallengeLink.View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded)
    (sourceLog : Log) (radius : ℕ) :
    BatchOpeningNativeObligation.source dummy ctx primitive capacity world work prepared decoded radius sourceLog =
      table ctx.parameters primitive capacity dummy (sha512 world (GoldContextInput.bytes ctx.parameters)) ctx.root sourceLog radius
        (BatchOpeningNativeObligation.dimensions ctx world work prepared) := by
  rw [GoldCommonSourceTable.batch_cube]
  obtain ⟨context,root⟩ := batch_binding ctx world work prepared framed responseFits decoded parsed
  rw [context,root]
  rfl

theorem single_binding {ctx : NativeGoldPcsExecution.Context} {world : World} {work : NativeGoldPcsWorkers.Prepared}
    {sample : NativeIndexRequest.Result} (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (framed : SingleOpeningAvailability.Framed ctx)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded) :
    decoded.field.data.context = sha512 world (GoldContextInput.bytes ctx.parameters) ∧ decoded.field.data.root = ctx.root := by
  obtain ⟨before,parent,valid,fits⟩ := framed
  obtain ⟨_,_,_,_,_,_,root,_,_,_,_,_,computed⟩ := SingleOpeningPreparedChallenge.parsed_origin receipt prepared
    before parent valid fits responseFits decoded parsed
  rw [GoldContextCollision.context_run] at computed
  exact ⟨(Option.some.inj computed).symm,root⟩

theorem single_table (dummy : Digest) {ctx : NativeGoldPcsExecution.Context} (origin : CacheBackedSingleOpening.Origin ctx)
    {world : World} {work : NativeGoldPcsWorkers.Prepared} {sample : NativeIndexRequest.Result}
    (receipt : SingleOpeningSamplingReceipt.Receipt ctx world work sample)
    (prepared : (run ctx.prefix world).run.1 = .prepared work)
    (framed : SingleOpeningAvailability.Framed ctx)
    (responseFits : (SingleOpeningColumnLaw.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : SingleOpeningChallengeLink.View)
    (parsed : SingleOpeningChallengeLink.parse (SingleOpeningColumnLaw.input receipt world) = some decoded)
    (sourceLog : Log) (radius : ℕ) :
    SingleOpeningNativeObligation.source dummy ctx origin world work prepared decoded sourceLog radius =
      table ctx.parameters origin.primitive origin.capacity dummy (sha512 world (GoldContextInput.bytes ctx.parameters)) ctx.root sourceLog radius
        (SingleOpeningExtractedTableMeaning.prepared_dimensions ctx world work prepared) := by
  rw [GoldCommonSourceTable.single_cube]
  obtain ⟨context,root⟩ := single_binding receipt prepared framed responseFits decoded parsed
  rw [context,root]
  rfl

end
end FormalProof4FHE.HasteBoots.GoldCommonSourceBinding
