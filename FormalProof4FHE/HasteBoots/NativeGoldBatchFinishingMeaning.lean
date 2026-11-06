module

public import FormalProof4FHE.HasteBoots.NativeGoldSuffixFinishing
public import FormalProof4FHE.HasteBoots.NativeGoldBatchResponseMeaning
@[expose] public section

/-! Every accepted original batch claim is the rectangular finishing of its
actual computed encoded response group. Query/message counts and encodings
are derived from execution; retained constructor/root correctness remain the
explicit backend premises. This is deterministic finishing, not FS soundness. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchFinishingMeaning
open NativeGoldBatchPcsProgram (Context Prepared Completion Scheduler)
open NativeGoldBlockCode (Tables encoding logSize description)
open NativeUsizeMessage (Usize)
open NativeLookupRequestWire (Row)
open NativeFieldRepresentation (goldValue)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem prepared_query_length (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (index : Fin work.binding.queries.val.length) :
    (work.binding.queries.val.get index).models.length = ctx.parameters.numVariables.val := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ := NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  obtain ⟨next,prelude,_,_,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  have bound := (NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude).2.1
  obtain ⟨valid,_,_,same,_⟩ := NativeGoldBatchBinding.bound_origin description.row ctx.parameters ctx.parent ctx.root ctx.queries ctx.values world binding bound
  cases same
  have checks := (NativeGoldBatchBinding.check_iff _ _ _).mp valid
  have valueBound : index.val < ctx.values.val.length := by rw [← checks.2.1]; exact index.isLt
  have pair := checks.2.2.get index.isLt valueBound
  simpa only [NativeGoldPcsWire.Query.models,List.length_map] using ((NativeGoldPcsBinding.check_iff _ _ _).mp pair).1

theorem prepared_message_length (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    ctx.parameters.code.messageLength.val = 2^(ctx.parameters.numVariables.val-ctx.parameters.leftVariables.val) :=
  (NativeBrakedownParameters.build_spec description ctx.parameters work.geometry
    (NativeGoldBatchResponseMeaning.prepared_geometry ctx world work executed)).code.1

theorem prepared_encoding (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (index : Fin work.evaluations.length) :
    ∃ response : Row, ctx.opening.evaluations.val[index.val]? = some response ∧
      NativeGoldRowEncoding.encodeResponses (encoding ctx.parameters.code work.planRoot) ctx.parameters.width.val response.val = some (work.evaluations.get index) := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,_,_,_,encoded,_,rfl⟩ := NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  have paired := NativeGoldBatchPcsProgram.encodeAll_spec ctx.parameters planRoot ctx.opening.evaluations.val evaluations encoded
  have inside : index.val < ctx.opening.evaluations.val.length := by rw [paired.length_eq]; exact index.isLt
  exact ⟨ctx.opening.evaluations.val[index.val],List.getElem?_eq_getElem inside,paired.get inside index.isLt⟩

/-- Every original right query finishes its assigned actual encoded group;
no result vector, encoding certificate or per-query success flag is supplied. -/
theorem accepted_value {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World)
    (work : Prepared) (completion : Completion Memory work.jobs.length)
    (executed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code)
    (primitive : IsPrimitiveRoot (goldValue ctx.parameters.code.domainRoot) (2^(logSize ctx.parameters.code+1)))
    (index : Fin work.binding.queries.val.length) :
    ∃ (response claimed : Row) (group : Fin work.evaluations.length)
      (size : (work.binding.queries.val.get index).models.length = ctx.parameters.numVariables.val)
      (shape : (encoding ctx.parameters.code work.planRoot).messageLength = 2^(ctx.parameters.numVariables.val-ctx.parameters.leftVariables.val)),
      group.val = (NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index).val ∧
      ctx.opening.evaluations.val[group.val]? = some response ∧ work.binding.values.val[index.val]? = some claimed ∧
      claimed.val.map goldValue = List.ofFn (RectangularMatrixResponse.finishEncoded
        (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) primitive)
        (NativeGoldBlockCodeMeaning.constructor_dimensions constructorTables message block blowup ctx.parameters.code constructed).2.2.1
        (NativeGoldSuffixFinishing.encodedRight ctx.parameters (work.binding.queries.val.get index) (encoding ctx.parameters.code work.planRoot) size shape)
        (fun lane => NativeGoldResponseMeaning.laneWord (encoding ctx.parameters.code work.planRoot) (work.evaluations.get group) lane.val)) := by
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  have counts := NativeGoldBatchPcsProgram.prepared_counts ctx world work prepared
  let original := NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index
  let group : Fin work.evaluations.length := ⟨original.val,by rw [counts.2.1,counts.1]; exact original.isLt⟩
  obtain ⟨response,claimed,responseRead,claimedRead,verified⟩ := NativeGoldBatchPcsProgram.accepted_claims ctx choose fuel memory world work completion executed parent accepted index
  obtain ⟨encodedResponse,encodedRead,computed⟩ := prepared_encoding ctx world work prepared group
  have same : encodedResponse = response := Option.some.inj (encodedRead.symm.trans responseRead)
  subst encodedResponse
  have size := prepared_query_length ctx world work prepared index
  have shape : (encoding ctx.parameters.code work.planRoot).messageLength = 2^(ctx.parameters.numVariables.val-ctx.parameters.leftVariables.val) :=
    prepared_message_length ctx world work prepared
  have dimensions := NativeGoldBlockCodeMeaning.constructor_dimensions constructorTables message block blowup ctx.parameters.code constructed
  refine ⟨response,claimed,group,size,shape,rfl,responseRead,claimedRead,?_⟩
  exact NativeGoldSuffixFinishing.claim_encoded ctx.parameters (work.binding.queries.val.get index) response.val (work.evaluations.get group) claimed
    (NativeGoldBatchPcsProgram.prepared_query_valid ctx world work prepared index) verified (encoding ctx.parameters.code work.planRoot) ctx.parameters.code.messageBlocks.val
    computed (Nat.le_of_lt dimensions.2.1) dimensions.2.2.1 primitive size shape
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchFinishingMeaning
