module
public import FormalProof4FHE.HasteBoots.NativeGoldBatchParsedDraws
public import FormalProof4FHE.HasteBoots.NativeGoldBatchSelectedChecks
public import FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteColumnFamily
@[expose] public section

/-! Native acceptance checks every concrete parsed response on the exact
ordered parsed draws and the source recovered from the old column history. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteAcceptedChecks
open InputIndexedOracle (World)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeGoldBatchPcsProgram (Context Prepared Scheduler)
open NativeGoldBlockCode (Tables logSize)
open NativeGoldColumnAuthentication (encoding)
open OracleProgram (run)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem accepted_checks {Memory : Type} (dummy : Digest) (ctx : Context) (world : World) (work : Prepared)
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
      (NativeGoldBatchFamilyAvailability.reconstructed dummy (columnHistory++suffix))) :
    ∃ draw, NativeIndexFirstReadLaw.values (logSize ctx.parameters.code)
      (decoded.column.index.request ctx.parent.profile).transcript decoded.column.index.label
      decoded.column.index.domain decoded.column.index.count world = some draw ∧
      (List.ofFn draw).map Fin.val = work.sample.draws ∧
      ∀ test : NativeGoldBatchConcreteColumnFamily.Test ctx decoded, ColumnOpening.Agrees
        (NativeGoldBatchConcreteColumnFamily.raw dummy ctx decoded sourceLog work.state test)
        (NativeGoldBatchConcreteColumnFamily.claim ctx primitive decoded work.state test) draw := by
  have nativeAccepted := accepted
  obtain ⟨⟨frames,parent,valid,fits⟩,completion,_,executed,_,_⟩ := accepted
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  obtain ⟨_,phase,_,_,_,_,root,_,_,_,count,_,_⟩ :=
    NativeGoldBatchPreparedChallenge.parsed_origin ctx world work prepared frames parent valid fits responseFits decoded parsed
  have binding := NativeGoldBatchParsedResponseData.binding_of_native ctx world work prepared frames parent valid fits responseFits decoded parsed
  have fieldParsed : NativeGoldBatchFieldInputView.parse (NativeGoldBatchRandomLaw.phase work).pending.input = some decoded.field := by
    rw [← phase,NativeGoldBatchFieldInputView.phase_input]
    exact NativeGoldBatchFirstFieldSource.linked_field_parsed _ decoded parsed
  obtain ⟨before,offset,values,after,_,positive,split,same⟩ :=
    NativeGoldBatchFirstFieldSource.recover_sound dummy columnHistory decoded.field sourceLog found
  have inputEq := (NativeGoldBatchFieldInputView.parse_sound _ decoded.field fieldParsed ctx.parent.profile).1
  rw [NativeGoldBatchFieldInputView.phase_input] at inputEq
  change NativeGoldBatchFirstFieldSource.input decoded.field = _ at inputEq
  rw [inputEq] at split
  rw [split,List.append_assoc,List.cons_append] at nativeAccepted truthful noDisagreement
  obtain ⟨prepared',draw,typed,ordered,random,groups,_⟩ :=
    NativeGoldBatchSelectedChecks.accepted_checks dummy ctx world work tables message block blowup constructed primitive
      choose fuel memory before (after++suffix) decoded.field fieldParsed offset values positive nativeAccepted truthful noDisagreement
  have sampled := NativeGoldBatchParsedDraws.values_typed ctx world work prepared frames parent valid fits responseFits decoded parsed
  rw [count] at sampled ⊢
  refine ⟨draw,sampled.trans typed,ordered,?_⟩
  have sourceEq : NativeGoldBatchConcreteColumnFamily.source dummy ctx decoded sourceLog =
      NativeGoldBatchSelectedWord.word dummy decoded.field.data.context ctx.root ctx (NativeGoldBatchSelectedSource.log dummy before decoded.field) := by
    unfold NativeGoldBatchConcreteColumnFamily.source
    rw [root,same]
  intro test
  cases test with
  | inl lane =>
    change ColumnOpening.Agrees (StructuredOpening.combine _ _) (BlockEncoder.encode _ (RowLayout.padded _)) draw
    rw [sourceEq]
    have messages := congrFun (NativeGoldBatchParsedResponseData.testMessages_native ctx work decoded binding) lane
    rw [messages]
    exact random lane
  | inr pair =>
    obtain ⟨group,lane⟩ := pair
    let nativeGroup : NativeGoldBatchRectangularData.Group ctx work := ⟨group.val,by
      rw [← binding.queries]
      exact group.isLt⟩
    change ColumnOpening.Agrees (StructuredOpening.combine _ _) (BlockEncoder.encode _ (RowLayout.padded _)) draw
    rw [sourceEq]
    have left := NativeGoldBatchParsedResponseData.groupLeft_native ctx world work decoded prepared' binding nativeGroup
    have messages := congrFun (NativeGoldBatchParsedResponseData.messages_native ctx work decoded binding nativeGroup) lane
    change NativeGoldBatchFixedResponseData.groupLeft ctx.parameters decoded.field.data.queries group.val = _ at left
    change NativeGoldBatchFixedResponseData.messages ctx.parameters decoded.column.opening group.val lane.val = _ at messages
    rw [left,messages]
    exact groups (nativeGroup,lane)
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchConcreteAcceptedChecks
