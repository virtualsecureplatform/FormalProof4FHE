module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsPaths

@[expose] public section

/-! Preserve original with-replacement draw order through sorted/deduplicated
transport. This identifies the actual samples; it does not assert freshness. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsDraws

open NativeGoldBlockCode (Tables Stored description)
open NativeBrakedownContext (Parameters)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldPcsWire (Query)
open NativeGoldPcsOpening (Opening)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open OracleProgram (run)

/-- Checked interpretation retains each original index, including duplicates. -/
def typed (height count : ℕ) (values : List ℕ) : Option (Fin count → Fin (2^height)) :=
  if size : values.length = count then
    if bounded : values.all (fun value => decide (value < 2^height)) = true then
      some (fun index =>
        let bound : index.val < values.length := by rw [size]; exact index.isLt
        ⟨values[index.val]'bound,of_decide_eq_true ((List.all_eq_true.mp bounded) _ (List.getElem_mem bound))⟩)
    else none
  else none

theorem typed_values (height count : ℕ) (values : List ℕ) (draw : Fin count → Fin (2^height))
    (success : typed height count values = some draw) : (List.ofFn draw).map Fin.val = values := by
  unfold typed at success
  split at success
  next size =>
    split at success
    next bounded =>
      cases success
      apply List.ext_getElem
      · simp only [List.length_map,List.length_ofFn,size]
      · intro index inside other
        simp only [List.getElem_map,List.getElem_ofFn]
    next => contradiction
  next => contradiction

theorem typed_complete (height count : ℕ) (values : List ℕ) (size : values.length = count)
    (bounded : ∀ value ∈ values, value < 2^height) : ∃ draw, typed height count values = some draw := by
  have checked : values.all (fun value => decide (value < 2^height)) = true := by
    apply List.all_eq_true.mpr
    intro value member
    exact decide_eq_true (bounded value member)
  simp only [typed,dite_eq_left size,dite_eq_left checked]
  exact ⟨_,rfl⟩

/-- The sample is the original actual atomic request result. Every ordered
draw is represented by an unchanged prepared job; deduplication loses none. -/
theorem prepared_sample (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) (work : Prepared)
    (success : (run (NativeGoldPcsWorkers.protocol tables parameters transcript root query values opening fuel) world).run.1 = .prepared work) :
    ∃ sample : NativeIndexRequest.Result,
      work.jobs.map NativeGoldColumnWorker.Job.index = sample.indices ∧
      sample.indices = NativeIndexRequest.distinct sample.draws ∧ sample.draws.length = parameters.queries.val ∧
      work.transcript = sample.transcript ∧
      (∀ index ∈ sample.draws, index < 2^work.geometry.height ∧ ∃ job ∈ work.jobs, job.index = index) ∧
      ∃ next, (run (NativeIndexRequest.request (NativeGoldPcsWire.bindResponses next opening.test opening.evaluation)
        NativeGoldPcsColumns.label (description.row.blocks parameters.code) parameters.queries) world).run.1 = some sample := by
  have paths := NativeGoldPcsPaths.prepared_paths tables parameters transcript root query values opening fuel world work success
  obtain ⟨geometry,state,weights,sample,planRoot,test,evaluation,jobs,encoded,attached,rfl⟩ :=
    NativeGoldPcsWorkers.prepared_origin tables parameters transcript root query values opening fuel world work success
  have original := (NativeGoldPcsEncoding.encoded_origin tables parameters transcript root query values opening fuel world geometry state weights sample planRoot test evaluation encoded).1
  obtain ⟨next,_,_,drawn,_⟩ := NativeGoldPcsColumns.columns_origin description parameters transcript root query values opening fuel world geometry state weights sample original
  have shape := NativeIndexRequest.accepted_shape _ _ _ _ world sample drawn
  have paired := NativeGoldPcsWorkers.attach_spec sample.indices opening.columns.val jobs attached
  refine ⟨sample,paired.1,shape.2.1,shape.1,rfl,?_,next,drawn⟩
  intro index member
  have present : index ∈ jobs.map NativeGoldColumnWorker.Job.index := by
    rw [paired.1,shape.2.1]
    exact (NativeIndexRequest.mem_distinct sample.draws index).mpr member
  obtain ⟨job,jobMember,same⟩ := List.mem_map.mp present
  exact ⟨by rw [← same]; exact (paths job jobMember).1,job,jobMember,same⟩

/-- A typed original draw vector is computed from the actual request, with
exact quota length and native order, rather than supplied as a certificate. -/
theorem prepared_typed (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) (work : Prepared)
    (success : (run (NativeGoldPcsWorkers.protocol tables parameters transcript root query values opening fuel) world).run.1 = .prepared work) :
    ∃ sample : NativeIndexRequest.Result, ∃ draw : Fin parameters.queries.val → Fin (2^work.geometry.height),
      work.jobs.map NativeGoldColumnWorker.Job.index = NativeIndexRequest.distinct sample.draws ∧
      typed work.geometry.height parameters.queries.val sample.draws = some draw ∧
      (List.ofFn draw).map Fin.val = sample.draws ∧
      (∀ index : Fin parameters.queries.val, ∃ job ∈ work.jobs, job.index = (draw index).val) ∧
      ∃ next, (run (NativeIndexRequest.request (NativeGoldPcsWire.bindResponses next opening.test opening.evaluation)
        NativeGoldPcsColumns.label (description.row.blocks parameters.code) parameters.queries) world).run.1 = some sample := by
  obtain ⟨sample,indices,distinct,size,_,covered,actual⟩ := prepared_sample tables parameters transcript root query values opening fuel world work success
  obtain ⟨draw,read⟩ := typed_complete work.geometry.height parameters.queries.val sample.draws size (fun index member => (covered index member).1)
  have ordered := typed_values _ _ _ _ read
  refine ⟨sample,draw,indices.trans distinct,read,ordered,?_,actual⟩
  intro index
  apply (covered (draw index).val ?_).2
  rw [← ordered]
  exact List.mem_map.mpr ⟨draw index,List.mem_ofFn.mpr ⟨index,rfl⟩,rfl⟩

end FormalProof4FHE.HasteBoots.NativeGoldPcsDraws
