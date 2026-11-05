module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsAgrees

@[expose] public section

/-! Actual checked-prefix samples feed both semantic PCS check families.
This is an opening-check interface, not full PCS acceptance or a freshness
claim for a checkpoint chosen in the native mixed execution. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks

open NativeGoldBlockCode (Tables Stored description)
open NativeBrakedownContext (Parameters)
open NativeGoldPcsWorkers (Prepared)
open NativeGoldRawRequests (Request)
open NativeGoldColumnAuthentication (encoding)
open NativeGoldPcsWire (Query)
open NativeGoldPcsOpening (Opening)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeTranscript (Transcript)
open InputIndexedOracle (Input World)
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- The geometry is the deterministic result of trusted parameter construction;
the query, challenge values and world do not supply it. -/
theorem prepared_parameters (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) (work : Prepared)
    (success : (OracleProgram.run (NativeGoldPcsWorkers.protocol tables parameters transcript root query values opening fuel) world).run.1 = .prepared work) :
    NativeBrakedownParameters.build description parameters = some work.geometry ∧
      work.width = parameters.width.val ∧ work.root = root := by
  obtain ⟨geometry,state,weights,sample,planRoot,test,evaluation,jobs,encoded,_,rfl⟩ :=
    NativeGoldPcsWorkers.prepared_origin tables parameters transcript root query values opening fuel world work success
  have original := (NativeGoldPcsEncoding.encoded_origin tables parameters transcript root query values opening fuel world geometry state weights sample planRoot test evaluation encoded).1
  obtain ⟨next,prior,_,_,_⟩ := NativeGoldPcsColumns.columns_origin description parameters transcript root query values opening fuel world geometry state weights sample original
  have constructed := (NativeGoldPcsPrelude.sampling_origin description parameters transcript root query values opening fuel world geometry (.finished state next) prior).1
  exact ⟨constructed,rfl,rfl⟩

/-- Retyping at the trusted checkpoint height computes the actual ordered
quota-sized draw function, preserving every repeated draw and its worker. -/
theorem original_draws {Cfg : Type} (height : Cfg → ℕ) (tag : Cfg)
    (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) (work : Prepared)
    (success : (OracleProgram.run (NativeGoldPcsWorkers.protocol tables parameters transcript root query values opening fuel) world).run.1 = .prepared work)
    (matchesHeight : work.geometry.height = height tag) :
    ∃ sample : NativeIndexRequest.Result, ∃ draw : Fin parameters.queries.val → Fin (2^(height tag)),
      NativeGoldPcsDraws.typed (height tag) parameters.queries.val sample.draws = some draw ∧
      (List.ofFn draw).map Fin.val = sample.draws ∧
      work.jobs.map NativeGoldColumnWorker.Job.index = NativeIndexRequest.distinct sample.draws ∧
      (∀ index : Fin parameters.queries.val, ∃ job ∈ work.jobs, job.index = (draw index).val) ∧
      ∃ next, (OracleProgram.run (NativeIndexRequest.request (NativeGoldPcsWire.bindResponses next opening.test opening.evaluation)
        NativeGoldPcsColumns.label (description.row.blocks parameters.code) parameters.queries) world).run.1 = some sample := by
  obtain ⟨sample,indices,distinct,size,_,covered,actual⟩ :=
    NativeGoldPcsDraws.prepared_sample tables parameters transcript root query values opening fuel world work success
  have bounded : ∀ index ∈ sample.draws, index < 2^(height tag) := by
    intro index member
    rw [← matchesHeight]
    exact (covered index member).1
  obtain ⟨draw,read⟩ := NativeGoldPcsDraws.typed_complete (height tag) parameters.queries.val sample.draws size bounded
  have ordered := NativeGoldPcsDraws.typed_values _ _ _ _ read
  refine ⟨sample,draw,read,ordered,indices.trans distinct,?_,actual⟩
  intro index
  apply (covered (draw index).val ?_).2
  rw [← ordered]
  exact List.mem_map.mpr ⟨draw index,List.mem_ofFn.mpr ⟨index,rfl⟩,rfl⟩

noncomputable section
variable {Cfg Memory : Type} [SampleableType Digest]

/-- The input checked native execution supplies the draw vector and complete
coverage. The actual raw pool flag supplies both response check families on
that original vector outside one shared availability event. -/
theorem prepared_agrees (height : Cfg → ℕ) (tag : Cfg)
    (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fieldFuel : ℕ) (world : World) (work : Prepared)
    (success : (OracleProgram.run (NativeGoldPcsWorkers.protocol tables parameters transcript root query values opening fieldFuel) world).run.1 = .prepared work)
    (result : List (NativeGoldColumnWorker.Job × Request height))
    (prepared : NativeGoldPcsRawAvailability.prepare height tag work = some result)
    (matchesHeight : work.geometry.height = height tag) (dummy : Digest)
    (choose : HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (outcome : HashWorkerPool.Outcome Input Digest Memory work.jobs.length ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy (fun tag => Skeleton.perfect (height tag)))
      (NativeGoldPcsWorkerSoundness.program work choose fuel memory)).run before))
    (accepted : HashWorkerPool.allAccepted outcome.1.workers = true)
    (noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height (result.map Prod.snd) outcome.2)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (recorded : ⟨tag,checkpoint⟩ ∈ outcome.2.checkpoints.checkpoints) (matchingRoot : checkpoint.root = work.root) :
    ∃ sample : NativeIndexRequest.Result, ∃ draw : Fin parameters.queries.val → Fin (2^(height tag)),
      NativeGoldPcsDraws.typed (height tag) parameters.queries.val sample.draws = some draw ∧
      (List.ofFn draw).map Fin.val = sample.draws ∧
      work.jobs.map NativeGoldColumnWorker.Job.index = NativeIndexRequest.distinct sample.draws ∧
      (∃ next, (OracleProgram.run (NativeIndexRequest.request (NativeGoldPcsWire.bindResponses next opening.test opening.evaluation)
        NativeGoldPcsColumns.label (description.row.blocks parameters.code) parameters.queries) world).run.1 = some sample) ∧
      (∀ lane, ColumnOpening.Agrees
        (StructuredOpening.combine (NativeGoldPcsAgrees.weights work.geometry.rows work.width work.random lane)
          (NativeGoldPcsAgrees.source dummy height tag checkpoint work.geometry.rows work.geometry.blockWidth))
        (NativeGoldPcsAgrees.response work.geometry work.width (height tag) work.test lane) draw) ∧
      (∀ lane, ColumnOpening.Agrees
        (StructuredOpening.combine (NativeGoldPcsAgrees.weights work.geometry.rows work.width work.structured lane)
          (NativeGoldPcsAgrees.source dummy height tag checkpoint work.geometry.rows work.geometry.blockWidth))
        (NativeGoldPcsAgrees.response work.geometry work.width (height tag) work.evaluation lane) draw) := by
  obtain ⟨sample,draw,typed,ordered,indices,covered,actual⟩ := original_draws height tag tables parameters transcript root query values opening fieldFuel world work success matchesHeight
  have agreements := NativeGoldPcsAgrees.pool_agrees height tag work result prepared matchesHeight dummy choose fuel memory before outcome supported accepted noFailure
    checkpoint recorded matchingRoot parameters.queries.val draw covered
  exact ⟨sample,draw,typed,ordered,indices,actual,agreements⟩

end
end FormalProof4FHE.HasteBoots.NativeGoldPcsOpeningChecks
