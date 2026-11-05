module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsEncoding
public import FormalProof4FHE.HasteBoots.NativeGoldPcsColumnsShape
public import FormalProof4FHE.HasteBoots.NativeGoldColumnWorker

@[expose] public section

/-! Worker inputs derived from the actual checked PCS encoding boundary.
Pairing preserves every received column and every sorted sampled index.
Prepared workers are not acceptance; their interleaved execution is supplied
by NativeGoldColumnWorker and the existing shared hash pool. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers

open NativeGoldColumnWorker (Job)
open NativeGoldColumnAuthentication (Column)
open NativeGoldBlockCode (Stored Tables description)
open NativeBrakedownContext (Parameters)
open NativeBrakedownParameters (Geometry)
open NativeGoldPcsOpening (Opening)
open NativeGoldPcsWire (Query)
open NativeLookupRequestWire (Row)
open NativeRootMessage (Digest)
open NativeFieldRepresentation (GoldWord)
open NativeTranscript (Transcript)
open InputIndexedOracle (World)
open OracleProgram (Program bind run)

def attach : List ℕ → List Column → Option (List Job)
  | [],[] => some []
  | index :: indices,column :: columns => (attach indices columns).map (fun jobs => ⟨index,column⟩ :: jobs)
  | _,_ => none

theorem attach_spec (indices : List ℕ) (columns : List Column) (jobs : List Job)
    (success : attach indices columns = some jobs) :
    jobs.map Job.index = indices ∧ jobs.map Job.column = columns := by
  induction indices generalizing columns jobs with
  | nil =>
    cases columns with
    | nil => cases success; exact ⟨rfl,rfl⟩
    | cons column tail => contradiction
  | cons index indices ih =>
    cases columns with
    | nil => contradiction
    | cons column columns =>
      obtain ⟨tail,read,same⟩ := Option.map_eq_some_iff.mp success
      subst jobs
      have previous := ih columns tail read
      exact ⟨congrArg (List.cons index) previous.1,congrArg (List.cons column) previous.2⟩

theorem attach_complete (indices : List ℕ) (columns : List Column) (size : indices.length = columns.length) :
    ∃ jobs, attach indices columns = some jobs := by
  induction indices generalizing columns with
  | nil =>
    cases columns with
    | nil => exact ⟨[],rfl⟩
    | cons column tail => simp only [List.length_nil,List.length_cons] at size; omega
  | cons index indices ih =>
    cases columns with
    | nil => simp only [List.length_cons,List.length_nil] at size; omega
    | cons column columns =>
      obtain ⟨jobs,read⟩ := ih columns (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using size)
      exact ⟨⟨index,column⟩::jobs,by simp only [attach,read,Option.map_some]⟩

structure Prepared where
  geometry : Geometry
  width : ℕ
  random : List GoldWord
  structured : List GoldWord
  test : List GoldWord
  evaluation : List GoldWord
  root : Digest
  jobs : List Job
  transcript : Transcript

inductive Outcome where
  | prefix (prior : NativeGoldPcsEncoding.Outcome)
  | pairingUnavailable
  | prepared (work : Prepared)

def advance (width : ℕ) (root : Digest) (opening : Opening) : NativeGoldPcsEncoding.Outcome → Outcome
  | .encoded geometry state weights sample _ test evaluation =>
    match attach sample.indices opening.columns.val with
    | none => .pairingUnavailable
    | some jobs => .prepared ⟨geometry,width,NativeGoldPcsColumns.random state,weights,test,evaluation,root,jobs,sample.transcript⟩
  | prior => .prefix prior

def protocol (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) : Program Outcome :=
  bind (NativeGoldPcsEncoding.protocol tables parameters transcript root query values opening fuel)
    (fun prior => .pure (advance parameters.width.val root opening prior))

theorem run_protocol (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) :
    (run (protocol tables parameters transcript root query values opening fuel) world).run =
      let prior := (run (NativeGoldPcsEncoding.protocol tables parameters transcript root query values opening fuel) world).run
      (advance parameters.width.val root opening prior.1,prior.2) := by
  rw [protocol,OracleProgram.run_bind,ObservationReplay.run_bind]
  simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem prepared_origin (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) (work : Prepared)
    (success : (run (protocol tables parameters transcript root query values opening fuel) world).run.1 = .prepared work) :
    ∃ geometry state weights sample planRoot test evaluation jobs,
      (run (NativeGoldPcsEncoding.protocol tables parameters transcript root query values opening fuel) world).run.1 =
        .encoded geometry state weights sample planRoot test evaluation ∧
      attach sample.indices opening.columns.val = some jobs ∧
      work = ⟨geometry,parameters.width.val,NativeGoldPcsColumns.random state,weights,test,evaluation,root,jobs,sample.transcript⟩ := by
  rw [run_protocol] at success
  cases prior : (run (NativeGoldPcsEncoding.protocol tables parameters transcript root query values opening fuel) world).run.1 <;>
    simp only [prior,advance] at success
  all_goals try contradiction
  split at success
  next => contradiction
  next jobs attached =>
    cases success
    exact ⟨_,_,_,_,_,_,_,jobs,rfl,attached,rfl⟩

/-- The real distinct-count gate makes pairing complete; no received column
or original sampled index is dropped. -/
theorem encoded_complete (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World)
    (geometry : Geometry) (state : NativeFieldVector.State) (weights : List GoldWord) (sample : NativeIndexRequest.Result)
    (planRoot : NativeGoldSolinas.Word) (test evaluation : List GoldWord)
    (success : (run (NativeGoldPcsEncoding.protocol tables parameters transcript root query values opening fuel) world).run.1 =
      .encoded geometry state weights sample planRoot test evaluation) :
    ∃ work, (run (protocol tables parameters transcript root query values opening fuel) world).run.1 = .prepared work ∧
      work.jobs.map Job.index = sample.indices ∧ work.jobs.map Job.column = opening.columns.val := by
  have original := (NativeGoldPcsEncoding.encoded_origin tables parameters transcript root query values opening fuel world geometry state weights sample planRoot test evaluation success).1
  obtain ⟨_,_,_,_,count⟩ := NativeGoldPcsColumns.columns_origin description parameters transcript root query values opening fuel world geometry state weights sample original
  obtain ⟨jobs,attached⟩ := attach_complete sample.indices opening.columns.val count.symm
  refine ⟨⟨geometry,parameters.width.val,NativeGoldPcsColumns.random state,weights,test,evaluation,root,jobs,sample.transcript⟩,?_,attach_spec _ _ _ attached⟩
  rw [run_protocol]
  simp only [success,advance,attached]

/-- Every native array bound for every actual worker is derived from the
checked prefix and the retained code constructor, before any hash is issued. -/
theorem prepared_shape (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) (work : Prepared)
    (success : (run (protocol tables parameters transcript root query values opening fuel) world).run.1 = .prepared work)
    (constructorTables : Tables) (message block blowup : NativeUsizeMessage.Usize)
    (constructed : NativeGoldBlockCode.build constructorTables message block blowup = .ok parameters.code) :
    ∀ job ∈ work.jobs, NativeGoldColumnChecks.Shape work.geometry work.width job.index
      work.random work.structured work.test work.evaluation job.column.values.val := by
  obtain ⟨geometry,state,weights,sample,planRoot,test,evaluation,jobs,encoded,attached,rfl⟩ :=
    prepared_origin tables parameters transcript root query values opening fuel world work success
  have original := NativeGoldPcsEncoding.encoded_origin tables parameters transcript root query values opening fuel world geometry state weights sample planRoot test evaluation encoded
  obtain ⟨next,prior,_,_,_⟩ := NativeGoldPcsColumns.columns_origin description parameters transcript root query values opening fuel world geometry state weights sample original.1
  obtain ⟨parametersRead,shape,_,_,_⟩ := NativeGoldPcsPrelude.sampling_origin description parameters transcript root query values opening fuel world geometry (.finished state next) prior
  have checked := (NativeGoldPcsOpening.check_iff geometry parameters.queries opening).mp shape
  have sizes := NativeBrakedownParameters.computed_sizes description parameters geometry parametersRead
  obtain ⟨randomSize,_,weightSize,_,_,_,_,bounded,_⟩ := NativeGoldPcsColumnsShape.columns_shape description parameters transcript root query values opening fuel world geometry state weights sample original.1
  have blocks := (NativeGoldBlockCodeMeaning.constructor_log constructorTables message block blowup parameters.code constructed).2
  have stride : geometry.stride = 2^(NativeGoldBlockCode.logSize parameters.code)*parameters.code.blockWidth.val := by
    rw [sizes.2.2.2.2.1,sizes.2.1,sizes.2.2.1]
    exact congrArg (fun count => count*parameters.code.blockWidth.val) blocks
  have paired := attach_spec sample.indices opening.columns.val jobs attached
  intro job member
  have indexMember : job.index ∈ sample.indices := by rw [← paired.1]; exact List.mem_map.mpr ⟨job,member,rfl⟩
  have columnMember : job.column ∈ opening.columns.val := by rw [← paired.2]; exact List.mem_map.mpr ⟨job,member,rfl⟩
  have testSize := (NativeGoldRowEncoding.encodeResponses_shape _ _ _ _ original.2.2.1).2.1
  have evaluationSize := (NativeGoldRowEncoding.encodeResponses_shape _ _ _ _ original.2.2.2).2.1
  refine ⟨sizes.2.2.2.2.1,bounded job.index indexMember,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.mul_comm] using randomSize
  · simpa only [Nat.mul_comm] using weightSize
  · rw [stride]; exact testSize
  · rw [stride]; exact evaluationSize
  · rw [(checked.columns job.column columnMember).1,sizes.2.2.2.2.2.1]

end FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers
