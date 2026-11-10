module
public import FormalProof4FHE.HasteBoots.SingleOpeningRectangularChecks
@[expose] public section

/-! Native rectangular checks at a specified source log. No existential
source selection can replace that log on the way to the ordered draw checks. -/
namespace FormalProof4FHE.HasteBoots.SingleOpeningFixedSourceChecks
open NativeGoldPcsExecution (Context)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldBlockCode (logSize description)
open NativeFieldRepresentation (goldValue)
open NativeRootMessage (Digest)
open InputIndexedOracle (World)
open OracleProgram (run)
open SingleOpeningRectangularData
open SingleOpeningRectangularChecks (layout source Frozen column_equations Sampled)
open NativeMerkleShapeFamily (height)
noncomputable section

theorem combinations (dummy context : Digest) (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (origin : CacheBackedSingleOpening.Origin ctx)
    (requests : List (NativeGoldColumnWorker.Job × NativeGoldRawRequests.Request height))
    (computed : SingleOpeningAvailability.prepare context work = some requests)
    (log : MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest)
    (checks : ∀ entry ∈ requests,
      NativeGoldRawAvailability.Equations work.geometry work.width work.random work.structured work.test work.evaluation
        (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position) entry.2.position.val) :
    ∀ entry ∈ requests, ∃ bound : entry.2.position.val < 2^logSize ctx.parameters.code,
      ∀ lane : Fin ctx.parameters.width.val,
        StructuredOpening.combine (Weights ctx world work prepared work.random lane)
          (source ctx world work prepared (Frozen dummy context work log)) ⟨entry.2.position.val,bound⟩ =
            Lane ctx work.test lane.val ⟨entry.2.position.val,bound⟩ ∧
        StructuredOpening.combine (Weights ctx world work prepared work.structured lane)
          (source ctx world work prepared (Frozen dummy context work log)) ⟨entry.2.position.val,bound⟩ =
            Lane ctx work.evaluation lane.val ⟨entry.2.position.val,bound⟩ := by
  have dims := layout ctx world work prepared origin
  have sameHeight : height (SingleOpeningAvailability.tag context work) = logSize ctx.parameters.code :=
    (SingleOpeningAvailability.tag_height context ctx world work prepared).trans dims.2.2
  have spec := NativeGoldRawRequests.entries_spec height (SingleOpeningAvailability.tag context work) work.root work.jobs requests computed
  intro entry member
  obtain ⟨inside,leaf,siblings,_,same⟩ := NativeGoldRawRequests.fromJob_spec height (SingleOpeningAvailability.tag context work)
    work.root entry.1 entry.2 (spec.2 entry member)
  have bounded : entry.2.position.val < 2^logSize ctx.parameters.code := by
    rw [same]
    simpa only [sameHeight] using inside
  refine ⟨bounded,?_⟩
  apply column_equations ctx world work prepared origin (Frozen dummy context work log) ⟨entry.2.position.val,bounded⟩
  have equations := checks entry member
  have values : Frozen dummy context work log entry.2.position.val =
      NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position := by
    rw [same]
    unfold Frozen
    congr 1
    apply Fin.ext
    exact Nat.mod_eq_of_lt inside
  rw [values]
  exact equations

theorem checks (dummy context : Digest) (ctx : Context) (world : World) (work : Prepared)
    (prepared : (run ctx.prefix world).run.1 = .prepared work) (origin : CacheBackedSingleOpening.Origin ctx)
    (requests : List (NativeGoldColumnWorker.Job × NativeGoldRawRequests.Request height))
    (computed : SingleOpeningAvailability.prepare context work = some requests)
    (log : MerkleTreeExtractor.QueryLog InputIndexedOracle.Input Digest)
    (equations : ∀ entry ∈ requests,
      NativeGoldRawAvailability.Equations work.geometry work.width work.random work.structured work.test work.evaluation
        (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position) entry.2.position.val) :
    ∃ (sample : NativeIndexRequest.Result) (draw : Fin ctx.parameters.queries.val → Fin (2^logSize ctx.parameters.code)),
      Sampled ctx world work sample ∧
      work.jobs.map NativeGoldColumnWorker.Job.index = NativeIndexRequest.distinct sample.draws ∧
      NativeGoldPcsDraws.typed (logSize ctx.parameters.code) ctx.parameters.queries.val sample.draws = some draw ∧
      (List.ofFn draw).map Fin.val = sample.draws ∧
      RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val)
        (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
        (source ctx world work prepared (Frozen dummy context work log)) (Weights ctx world work prepared work.random)
        (messages ctx ctx.opening.test.val) draw ∧
      RectangularMatrixOpeningKernel.Checks (m := ctx.parameters.code.messageBlocks.val)
        (NTTButterfly.domain (logSize ctx.parameters.code) (goldValue ctx.parameters.code.domainRoot) origin.primitive)
        (source ctx world work prepared (Frozen dummy context work log)) (RectangularMatrixResponse.weights (left ctx world work prepared))
        (messages ctx ctx.opening.evaluation.val) draw := by
  have checks := combinations dummy context ctx world work prepared origin requests computed log equations
  obtain ⟨geom,state,weights,sample,planRoot,test,evaluation,jobs,encoded,attached,workEq⟩ :=
    NativeGoldPcsWorkers.prepared_origin ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed ctx.opening ctx.fieldFuel world work prepared
  have original := (NativeGoldPcsEncoding.encoded_origin ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world geom state weights sample planRoot test evaluation encoded).1
  obtain ⟨next,_,_,sampled,_⟩ := NativeGoldPcsColumns.columns_origin description ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
    ctx.opening ctx.fieldFuel world geom state weights sample original
  have shape := NativeIndexRequest.accepted_shape _ _ _ _ world sample sampled
  have indices : work.jobs.map NativeGoldColumnWorker.Job.index = sample.indices := by
    rw [workEq]
    exact (NativeGoldPcsWorkers.attach_spec sample.indices ctx.opening.columns.val jobs attached).1
  have receipt : Sampled ctx world work sample := by
    refine ⟨state,?_,?_,?_⟩
    · rw [workEq]; exact original
    · rw [workEq]
    · rw [workEq]
  have covered (index : ℕ) (member : index ∈ sample.draws) :
      index < 2^work.geometry.height ∧ ∃ job ∈ work.jobs, job.index = index := by
    have present : index ∈ work.jobs.map NativeGoldColumnWorker.Job.index := by
      rw [indices,shape.2.1]
      exact (NativeIndexRequest.mem_distinct sample.draws index).mpr member
    obtain ⟨job,jobMember,same⟩ := List.mem_map.mp present
    exact ⟨by rw [← same]; exact (NativeGoldPcsPaths.prepared_paths ctx.tables ctx.parameters ctx.transcript ctx.root ctx.query ctx.claimed
      ctx.opening ctx.fieldFuel world work prepared job jobMember).1,job,jobMember,same⟩
  have dims := layout ctx world work prepared origin
  obtain ⟨draw,typed⟩ := NativeGoldPcsDraws.typed_complete (logSize ctx.parameters.code) ctx.parameters.queries.val sample.draws shape.1
    (fun index member => by rw [← dims.2.2]; exact (covered index member).1)
  have ordered := NativeGoldPcsDraws.typed_values _ _ _ _ typed
  refine ⟨sample,draw,receipt,indices.trans shape.2.1,typed,ordered,?_⟩
  have spec := NativeGoldRawRequests.entries_spec height (SingleOpeningAvailability.tag context work) work.root work.jobs requests computed
  have each (lane : Fin ctx.parameters.width.val) (index : Fin ctx.parameters.queries.val) :
      StructuredOpening.combine (Weights ctx world work prepared work.random lane) (source ctx world work prepared (Frozen dummy context work log)) (draw index) = Lane ctx work.test lane.val (draw index) ∧
      StructuredOpening.combine (Weights ctx world work prepared work.structured lane) (source ctx world work prepared (Frozen dummy context work log)) (draw index) = Lane ctx work.evaluation lane.val (draw index) := by
    have present : (draw index).val ∈ sample.draws := by
      rw [← ordered]
      exact List.mem_map.mpr ⟨draw index,List.mem_ofFn.mpr ⟨index,rfl⟩,rfl⟩
    obtain ⟨job,member,sameIndex⟩ := (covered (draw index).val present).2
    have requestMember : job ∈ requests.map Prod.fst := by rw [spec.1]; exact member
    obtain ⟨entry,entryMember,sameJob⟩ := List.mem_map.mp requestMember
    obtain ⟨inside,leaf,siblings,_,sameRequest⟩ := NativeGoldRawRequests.fromJob_spec height (SingleOpeningAvailability.tag context work)
      work.root entry.1 entry.2 (spec.2 entry entryMember)
    obtain ⟨bound,checked⟩ := checks entry entryMember
    have position : (⟨entry.2.position.val,bound⟩ : Fin (2^logSize ctx.parameters.code)) = draw index := by
      apply Fin.ext
      change entry.2.position.val = (draw index).val
      rw [sameRequest]
      change entry.1.index = (draw index).val
      rw [sameJob]
      exact sameIndex
    exact position ▸ checked lane
  have coded := encoded_messages ctx world work prepared origin
  constructor
  · intro lane index
    have checked := (each lane index).1
    rw [congrFun coded.1 lane] at checked
    exact checked
  · intro lane index
    have checked := (each lane index).2
    rw [structured_weights ctx world work prepared,congrFun coded.2 lane] at checked
    exact checked

end
end FormalProof4FHE.HasteBoots.SingleOpeningFixedSourceChecks
