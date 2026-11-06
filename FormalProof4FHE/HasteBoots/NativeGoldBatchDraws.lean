module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchLinearEquations
public import FormalProof4FHE.HasteBoots.NativeGoldPcsDraws
@[expose] public section

/-! Exact original ordered draws through native batch worker deduplication.
Every occurrence has a computed raw request; authentication is still performed
once per distinct column. These identities make no freshness assumption. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchDraws
open NativeGoldBatchPcsProgram (Context Prepared)
open NativeGoldBlockCode (Tables logSize description)
open NativeUsizeMessage (Usize)
open NativeRootMessage (Digest)
open InputIndexedOracle (World)
open OracleProgram (run)
noncomputable section

theorem prepared_sample (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) :
    work.sample.draws.length = ctx.parameters.queries.val ∧
      work.sample.indices = NativeIndexRequest.distinct work.sample.draws ∧
      ∀ index ∈ work.sample.draws, index < ctx.parameters.code.blocks.val ∧ ∃ job ∈ work.jobs, job.index = index := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,attached,rfl⟩ := NativeGoldBatchPcsProgram.prepared_origin ctx world work executed
  obtain ⟨next,_,_,drawn,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  have shape := NativeIndexRequest.accepted_shape _ _ _ _ world sample drawn
  have paired := NativeGoldPcsWorkers.attach_spec sample.indices ctx.opening.columns.val jobs attached
  refine ⟨shape.1,shape.2.1,?_⟩
  intro index member
  have present : index ∈ jobs.map NativeGoldColumnWorker.Job.index := by
    rw [paired.1,shape.2.1]
    exact (NativeIndexRequest.mem_distinct sample.draws index).mpr member
  obtain ⟨job,jobMember,same⟩ := List.mem_map.mp present
  exact ⟨shape.2.2.2.2.1 index member,job,jobMember,same⟩

/-- The checked typed vector is computed from the actual atomic block, with
its original quota, ordering and repetitions unchanged. -/
theorem prepared_typed (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (constructorTables : Tables) (message block blowup : Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok ctx.parameters.code) :
    ∃ draw : Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code)),
      NativeGoldPcsDraws.typed (logSize ctx.parameters.code) ctx.parameters.queries.val work.sample.draws = some draw ∧
      (List.ofFn draw).map Fin.val = work.sample.draws ∧
      ∀ index, ∃ job ∈ work.jobs, job.index = (draw index).val := by
  obtain ⟨size,_,covered⟩ := prepared_sample ctx world work executed
  have blocks := (NativeGoldBlockCodeMeaning.constructor_log constructorTables message block blowup ctx.parameters.code constructed).2
  obtain ⟨draw,read⟩ := NativeGoldPcsDraws.typed_complete (logSize ctx.parameters.code) ctx.parameters.queries.val work.sample.draws size
    (fun index member => by rw [← blocks]; exact (covered index member).1)
  have ordered := NativeGoldPcsDraws.typed_values _ _ _ _ read
  refine ⟨draw,read,ordered,?_⟩
  intro index
  apply (covered (draw index).val ?_).2
  rw [← ordered]
  exact List.mem_map.mpr ⟨draw index,List.mem_ofFn.mpr ⟨index,rfl⟩,rfl⟩

/-- Every original draw occurrence is represented by an actual computed raw
request, although several occurrences may use the same authenticated column. -/
theorem draw_request (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (context : Digest) (requests : List (NativeGoldColumnWorker.Job × NativeGoldRawRequests.Request NativeMerkleShapeFamily.height))
    (computed : NativeGoldBatchFamilyRequests.prepare context work = some requests)
    (draw : Fin ctx.parameters.queries.val → Fin (2^(logSize ctx.parameters.code)))
    (ordered : (List.ofFn draw).map Fin.val = work.sample.draws) (index : Fin ctx.parameters.queries.val) :
    ∃ entry ∈ requests, entry.2.position.val = (draw index).val := by
  have member : (draw index).val ∈ work.sample.draws := by
    rw [← ordered]
    exact List.mem_map.mpr ⟨draw index,List.mem_ofFn.mpr ⟨index,rfl⟩,rfl⟩
  obtain ⟨_,job,jobMember,same⟩ := (prepared_sample ctx world work executed).2.2 _ member
  have spec := NativeGoldBatchRawRequests.prepare_spec NativeMerkleShapeFamily.height (NativeMerkleShapeFamily.tag context work) work requests computed
  have found : job ∈ requests.map Prod.fst := by rw [spec.1]; exact jobMember
  obtain ⟨entry,entryMember,jobEq⟩ := List.mem_map.mp found
  obtain ⟨_,_,_,_,requestEq⟩ := NativeGoldRawRequests.fromJob_spec _ _ _ _ _ (spec.2 entry entryMember)
  refine ⟨entry,entryMember,?_⟩
  rw [requestEq]
  exact jobEq ▸ same
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchDraws
