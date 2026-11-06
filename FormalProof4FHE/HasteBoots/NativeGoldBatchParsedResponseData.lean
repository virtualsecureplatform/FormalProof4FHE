module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFixedResponseData
@[expose] public section

/-! The actual complete column nonce supplies all data used by the response
family. Binding below is derived from native execution and used only in
analysis; it is not a verifier input or freshness/source certificate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchParsedResponseData
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBatchChallengeLink (View)
open NativeGoldBatchFixedResponseData (leftAt groupLeft rightAt messages testMessages claimed)
open InputIndexedOracle (World)
open TranscriptFrame (Frame)
open OracleProgram (run)
noncomputable section

structure Binding (ctx : Context) (work : Prepared) (decoded : View) : Prop where
  queries : decoded.field.data.queries = work.binding.queries
  values : decoded.field.data.values = work.binding.values
  test : decoded.column.opening.test = ctx.opening.test
  evaluations : decoded.column.opening.evaluations = ctx.opening.evaluations

theorem binding_of_native (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (before : List Frame) (parent : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ frame ∈ before, TranscriptFrame.Valid frame)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit)
    (responseFits : (NativeGoldBatchResponseBinding.payload ctx.opening).length < TranscriptFrame.lengthLimit)
    (decoded : View)
    (parsed : NativeGoldBatchChallengeLink.parse (NativeGoldBatchColumnRequestLaw.input ctx work world) = some decoded) : Binding ctx work decoded := by
  obtain ⟨_,_,_,_,test,evaluations,_,queries,values,_⟩ :=
    NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared before parent valid fits responseFits decoded parsed
  have bound := NativeGoldBatchPcsProgram.prepared_binding ctx world work prepared
  exact ⟨queries.trans bound.2.2.1.symm,values.trans bound.2.2.2.symm,test,evaluations⟩

theorem left_native (ctx : Context) (world : World) (work : Prepared) (decoded : View)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (binding : Binding ctx work decoded) (query : Fin work.binding.queries.val.length) :
    leftAt ctx.parameters decoded.field.data.queries query.val = NativeGoldBatchRectangularWeights.left ctx world work prepared query := by
  rw [binding.queries]
  exact NativeGoldBatchFixedResponseData.left_native ctx world work prepared query

theorem groupLeft_native (ctx : Context) (world : World) (work : Prepared) (decoded : View)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (binding : Binding ctx work decoded) (group : NativeGoldBatchRectangularData.Group ctx work) :
    groupLeft ctx.parameters decoded.field.data.queries group.val = NativeGoldBatchRectangularData.left ctx world work prepared group := by
  rw [binding.queries]
  exact NativeGoldBatchFixedResponseData.groupLeft_native ctx world work prepared group

theorem right_native (ctx : Context) (world : World) (work : Prepared) (decoded : View)
    (prepared : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (binding : Binding ctx work decoded) (query : Fin work.binding.queries.val.length) :
    rightAt ctx.parameters decoded.field.data.queries query.val = NativeGoldBatchRectangularData.right ctx world work prepared query := by
  rw [binding.queries]
  exact NativeGoldBatchFixedResponseData.right_native ctx world work prepared query

theorem messages_native (ctx : Context) (work : Prepared) (decoded : View) (binding : Binding ctx work decoded)
    (group : NativeGoldBatchRectangularData.Group ctx work) :
    (fun lane : Fin ctx.parameters.width.val => messages ctx.parameters decoded.column.opening group.val lane.val) =
      NativeGoldBatchRectangularData.messages ctx work group := by
  unfold messages NativeGoldBatchRectangularData.messages NativeGoldBatchRectangularData.raw
  rw [binding.evaluations]
  rfl

theorem testMessages_native (ctx : Context) (work : Prepared) (decoded : View) (binding : Binding ctx work decoded) :
    (fun lane : Fin ctx.parameters.width.val => testMessages ctx.parameters decoded.column.opening lane.val) =
      NativeGoldBatchRectangularData.testMessages ctx work := by
  unfold testMessages NativeGoldBatchRectangularData.testMessages
  rw [binding.test]
  rfl

theorem claimed_native (ctx : Context) (work : Prepared) (decoded : View) (binding : Binding ctx work decoded)
    (query : Fin work.binding.queries.val.length) :
    (fun lane : Fin ctx.parameters.width.val => claimed decoded.field.data.values query.val lane.val) =
      NativeGoldBatchRectangularData.claimed ctx work query := by
  rw [binding.values]
  rfl
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchParsedResponseData
