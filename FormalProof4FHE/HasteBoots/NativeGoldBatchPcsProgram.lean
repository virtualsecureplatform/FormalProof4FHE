module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchColumns
public import FormalProof4FHE.HasteBoots.NativeGoldBatchColumnWorker
public import FormalProof4FHE.HasteBoots.NativeGoldPcsProgram
@[expose] public section

/-! Native non-hiding Goldilocks batch PCS execution in one causal oracle
program: checked binding, shared random test and columns, actual retained-code
response encoding, one raw worker per distinct column, and finishing every
original claim against its computed prefix group. Acceptance is computed.
Analysis unavailability/suspension remains distinct from native rejection.
Raw authentication is not availability or an application soundness theorem;
global FS, physical work, strict decoding, and native/compiler/scheduler
refinement remain required. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchPcsProgram
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeFieldRepresentation (GoldWord)
open NativeGoldBlockCode (Tables Stored description encoding logSize)
open NativeBrakedownContext (Parameters)
open NativeBrakedownParameters (Geometry)
open NativeGoldPcsWire (Query)
open NativeGoldBatchOpening (Opening)
open NativeGoldBatchBinding (Bound)
open NativeLookupRequestWire (Row)
open NativePrefixCodec (Vector)
open NativeTranscript (Transcript Observation)
open OracleProgram (Program bind run)
open OracleSpec OracleComp
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

structure Context where
  tables : Tables
  parameters : Parameters Stored
  parent : Transcript
  root : Digest
  queries : Vector Query
  values : Vector Row
  opening : Opening
  fieldFuel : ℕ

def encodeAll (parameters : Parameters Stored) (planRoot : NativeGoldSolinas.Word) : List Row → Option (List (List GoldWord))
  | [] => some []
  | row::rest => (NativeGoldRowEncoding.encodeResponses (encoding parameters.code planRoot) parameters.width.val row.val).bind (fun encoded =>
      (encodeAll parameters planRoot rest).map (List.cons encoded))

theorem encodeAll_spec (parameters : Parameters Stored) (planRoot : NativeGoldSolinas.Word) (rows : List Row) (encoded : List (List GoldWord))
    (computed : encodeAll parameters planRoot rows = some encoded) :
    List.Forall₂ (fun row words => NativeGoldRowEncoding.encodeResponses (encoding parameters.code planRoot) parameters.width.val row.val = some words) rows encoded := by
  induction rows generalizing encoded with
  | nil => have same := Option.some.inj computed; subst encoded; exact .nil
  | cons row rest ih =>
    simp only [encodeAll] at computed
    obtain ⟨first,read,tail⟩ := Option.bind_eq_some_iff.mp computed
    obtain ⟨remaining,continued,same⟩ := Option.map_eq_some_iff.mp tail
    rw [← same]
    exact .cons read (ih remaining continued)

structure Prepared where
  geometry : Geometry
  binding : Bound
  state : NativeFieldVector.State
  weights : List (List GoldWord)
  sample : NativeIndexRequest.Result
  planRoot : NativeGoldSolinas.Word
  test : List GoldWord
  evaluations : List (List GoldWord)
  jobs : List NativeGoldColumnWorker.Job
  root : Digest
  width : ℕ

def Prepared.random (work : Prepared) := work.state.values.map NativePrimeRequest.goldWord
def Prepared.groups (work : Prepared) := work.weights.zip work.evaluations

inductive PrefixOutcome where
  | prior (status : NativeGoldBatchColumns.Outcome)
  | encodingUnavailable
  | pairingUnavailable
  | prepared (work : Prepared)

def advance (ctx : Context) : NativeGoldBatchColumns.Outcome → PrefixOutcome
  | .columns geometry binding state weights sample =>
    match ctx.tables.load (logSize ctx.parameters.code) with
    | none => .encodingUnavailable
    | some planRoot => match NativeGoldRowEncoding.encodeResponses (encoding ctx.parameters.code planRoot) ctx.parameters.width.val ctx.opening.test.val with
      | none => .encodingUnavailable
      | some test => match encodeAll ctx.parameters planRoot ctx.opening.evaluations.val with
        | none => .encodingUnavailable
        | some evaluations => match NativeGoldPcsWorkers.attach sample.indices ctx.opening.columns.val with
          | none => .pairingUnavailable
          | some jobs => .prepared ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,ctx.root,ctx.parameters.width.val⟩
  | prior => .prior prior

def prepareProgram (ctx : Context) : Program PrefixOutcome :=
  bind (NativeGoldBatchColumns.protocol description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel)
    (fun prior => .pure (advance ctx prior))

theorem run_prepareProgram (ctx : Context) (world : World) :
    (run (prepareProgram ctx) world).run =
      let prior := (run (NativeGoldBatchColumns.protocol description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel) world).run
      (advance ctx prior.1,prior.2) := by
  rw [prepareProgram,OracleProgram.run_bind,ObservationReplay.run_bind]
  simp only [OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]

theorem prepared_origin (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (prepareProgram ctx) world).run.1 = .prepared work) :
    ∃ geometry binding state weights sample planRoot test evaluations jobs,
      (run (NativeGoldBatchColumns.protocol description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel) world).run.1 =
        .columns geometry binding state weights sample ∧
      ctx.tables.load (logSize ctx.parameters.code) = some planRoot ∧
      NativeGoldRowEncoding.encodeResponses (encoding ctx.parameters.code planRoot) ctx.parameters.width.val ctx.opening.test.val = some test ∧
      encodeAll ctx.parameters planRoot ctx.opening.evaluations.val = some evaluations ∧
      NativeGoldPcsWorkers.attach sample.indices ctx.opening.columns.val = some jobs ∧
      work = ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,ctx.root,ctx.parameters.width.val⟩ := by
  rw [run_prepareProgram] at executed
  cases prior : (run (NativeGoldBatchColumns.protocol description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel) world).run.1 <;>
    simp only [prior,advance] at executed
  all_goals try contradiction
  split at executed
  next => contradiction
  next planRoot loaded =>
    split at executed
    next => contradiction
    next test encodedTest =>
      split at executed
      next => contradiction
      next evaluations encodedValues =>
        split at executed
        next => contradiction
        next jobs attached =>
          exact ⟨_,_,_,_,_,planRoot,test,evaluations,jobs,rfl,loaded,encodedTest,encodedValues,attached,(PrefixOutcome.prepared.inj executed).symm⟩

/-- Prepared root, width and original ordered queries/values come from the same checked binding. -/
theorem prepared_binding (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (prepareProgram ctx) world).run.1 = .prepared work) :
    work.root = ctx.root ∧ work.width = ctx.parameters.width.val ∧ work.binding.queries = ctx.queries ∧ work.binding.values = ctx.values := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ := prepared_origin ctx world work executed
  obtain ⟨next,prelude,_,_,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  have bound := (NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude).2.1
  obtain ⟨_,_,_,same,_⟩ := NativeGoldBatchBinding.bound_origin description.row ctx.parameters ctx.parent ctx.root ctx.queries ctx.values world binding bound
  exact ⟨rfl,rfl,congrArg Bound.queries same,congrArg Bound.values same⟩

/-- All computed structured/encoded groups and all claimed values have their original checked counts. -/
theorem prepared_counts (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (prepareProgram ctx) world).run.1 = .prepared work) :
    work.weights.length = NativeGoldQueryGroups.groupCount ctx.parameters.leftVariables.val work.binding.queries ∧
      work.evaluations.length = work.weights.length ∧ ctx.opening.evaluations.val.length = work.weights.length ∧
      work.binding.values.val.length = work.binding.queries.val.length := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,encoded,_,rfl⟩ := prepared_origin ctx world work executed
  obtain ⟨next,prelude,computed,_,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  obtain ⟨_,bound,shape,_⟩ := NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude
  have spec := (NativeGoldBatchOpening.check_iff _ _ _ _).mp shape
  have weightCount := (NativeGoldBatchColumns.structured_spec ctx.parameters binding.queries weights computed).1
  have encodedCount := (encodeAll_spec ctx.parameters planRoot ctx.opening.evaluations.val evaluations encoded).length_eq
  have checked := NativeGoldBatchBinding.bound_origin description.row ctx.parameters ctx.parent ctx.root ctx.queries ctx.values world binding bound
  have count := (NativeGoldBatchBinding.check_iff _ _ _).mp checked.1 |>.2.1
  obtain ⟨_,_,same,_⟩ := checked.2
  refine ⟨weightCount,encodedCount.symm.trans (spec.groups.trans weightCount.symm),spec.groups.trans weightCount.symm,?_⟩
  rw [same]
  exact count.symm

theorem prepared_jobs (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (prepareProgram ctx) world).run.1 = .prepared work) :
    work.jobs.map NativeGoldColumnWorker.Job.index = work.sample.indices ∧
      work.jobs.map NativeGoldColumnWorker.Job.column = ctx.opening.columns.val ∧ work.jobs ≠ [] := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,attached,rfl⟩ := prepared_origin ctx world work executed
  have paired := NativeGoldPcsWorkers.attach_spec _ _ _ attached
  obtain ⟨next,prelude,_,_,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  have shape := (NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude).2.2.1
  have nonempty := (NativeGoldBatchOpening.check_iff _ _ _ _).mp shape |>.nonempty
  refine ⟨paired.1,paired.2,?_⟩
  intro empty
  change jobs = [] at empty
  apply nonempty
  rw [← paired.2,empty,List.map_nil]

/-- The native zip covers every computed group; none can be silently truncated. -/
theorem prepared_groups (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (prepareProgram ctx) world).run.1 = .prepared work) (index : Fin work.weights.length) :
    ∃ bounded : index.val < work.evaluations.length,
      (work.weights[index.val],work.evaluations[index.val]) ∈ work.groups := by
  have counts := prepared_counts ctx world work executed
  have bounded : index.val < work.evaluations.length := by rw [counts.2.1]; exact index.isLt
  refine ⟨bounded,?_⟩
  have inside : index.val < work.groups.length := by
    simp only [Prepared.groups,List.length_zip,counts.2.1,Nat.min_self]
    exact index.isLt
  simpa only [Prepared.groups,List.getElem_zip] using List.getElem_mem inside

/-- Each original query passed its native matrix validators in the actual batch binding. -/
theorem prepared_query_valid (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (prepareProgram ctx) world).run.1 = .prepared work) (index : Fin work.binding.queries.val.length) :
    NativeGoldMatrixWeights.QueryValid ctx.parameters.width.val (work.binding.queries.val.get index).models := by
  obtain ⟨geometry,binding,state,weights,sample,planRoot,test,evaluations,jobs,prior,_,_,_,_,rfl⟩ := prepared_origin ctx world work executed
  obtain ⟨next,prelude,_,_,_⟩ := NativeGoldBatchColumns.columns_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding state weights sample prior
  have bound := (NativeGoldBatchPrelude.sampling_origin description ctx.parameters ctx.parent ctx.root ctx.queries ctx.values ctx.opening ctx.fieldFuel world geometry binding (.finished state next) prelude).2.1
  obtain ⟨valid,_,_,same,_⟩ := NativeGoldBatchBinding.bound_origin description.row ctx.parameters ctx.parent ctx.root ctx.queries ctx.values world binding bound
  cases same
  have checks := (NativeGoldBatchBinding.check_iff _ _ _).mp valid
  have valueBound : index.val < ctx.values.val.length := by rw [← checks.2.1]; exact index.isLt
  exact (NativeGoldPcsColumnsShape.binding_models ctx.parameters (ctx.queries.val.get index) ctx.values.val[index.val] (checks.2.2.get index.isLt valueBound)).2

inductive ClaimError where
  | indexingUnavailable
  | claim (reason : NativeGoldPcsClaim.Error)
  deriving DecidableEq

def claim (parameters : Parameters Stored) (binding : Bound) (opening : Opening) (index : Fin binding.queries.val.length) : Except ClaimError Unit :=
  let group := NativeGoldQueryGroups.group parameters.leftVariables.val binding.queries index
  match opening.evaluations.val[group.val]?,binding.values.val[index.val]? with
  | some response,some claimed => (NativeGoldPcsClaim.verify parameters (binding.queries.val.get index) response.val claimed).mapError ClaimError.claim
  | _,_ => .error .indexingUnavailable

def claims (parameters : Parameters Stored) (binding : Bound) (opening : Opening) : List (Fin binding.queries.val.length) → Except ClaimError Unit
  | [] => .ok ()
  | index::rest => match claim parameters binding opening index with
    | .error reason => .error reason
    | .ok () => claims parameters binding opening rest

def finish (parameters : Parameters Stored) (binding : Bound) (opening : Opening) : Except ClaimError Unit :=
  claims parameters binding opening (List.finRange binding.queries.val.length)

theorem claims_each (parameters : Parameters Stored) (binding : Bound) (opening : Opening)
    (indices : List (Fin binding.queries.val.length)) (accepted : claims parameters binding opening indices = .ok ()) :
    ∀ index ∈ indices, claim parameters binding opening index = .ok () := by
  induction indices with
  | nil => intro index member; cases member
  | cons first rest ih =>
    simp only [claims] at accepted
    cases checked : claim parameters binding opening first with
    | error reason => simp only [checked] at accepted; contradiction
    | ok value =>
      cases value
      simp only [checked] at accepted
      intro index member
      rcases List.mem_cons.mp member with same | later
      · subst index; exact checked
      · exact ih accepted index later

theorem finish_each (parameters : Parameters Stored) (binding : Bound) (opening : Opening)
    (accepted : finish parameters binding opening = .ok ()) (index : Fin binding.queries.val.length) :
    claim parameters binding opening index = .ok () :=
  claims_each parameters binding opening _ accepted index (List.mem_finRange index)

theorem claim_origin (parameters : Parameters Stored) (binding : Bound) (opening : Opening) (index : Fin binding.queries.val.length)
    (accepted : claim parameters binding opening index = .ok ()) :
    ∃ response claimed,
      opening.evaluations.val[(NativeGoldQueryGroups.group parameters.leftVariables.val binding.queries index).val]? = some response ∧
      binding.values.val[index.val]? = some claimed ∧
      NativeGoldPcsClaim.verify parameters (binding.queries.val.get index) response.val claimed = .ok () := by
  unfold claim at accepted
  dsimp only at accepted
  split at accepted
  next response claimed responseRead valueRead =>
    refine ⟨response,claimed,responseRead,valueRead,?_⟩
    cases checked : NativeGoldPcsClaim.verify parameters (binding.queries.val.get index) response.val claimed with
    | error reason => simp only [checked,Except.mapError] at accepted; contradiction
    | ok value => cases value; rfl
  next => contradiction

/-- The totalized indexing branch is unreachable for actual prepared native batches. -/
theorem claim_indexing (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (prepareProgram ctx) world).run.1 = .prepared work) (index : Fin work.binding.queries.val.length) :
    claim ctx.parameters work.binding ctx.opening index ≠ .error .indexingUnavailable := by
  have counts := prepared_counts ctx world work executed
  have responseBound : (NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index).val < ctx.opening.evaluations.val.length := by
    rw [counts.2.2.1,counts.1]
    exact (NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index).isLt
  have valueBound : index.val < work.binding.values.val.length := by rw [counts.2.2.2]; exact index.isLt
  unfold claim
  dsimp only
  rw [List.getElem?_eq_getElem responseBound,List.getElem?_eq_getElem valueBound]
  have safe (result : Except NativeGoldPcsClaim.Error Unit) :
      result.mapError ClaimError.claim ≠ (.error .indexingUnavailable : Except ClaimError Unit) := by
    cases result <;> simp [Except.mapError]
  exact safe _

abbrev Scheduler (Memory : Type) := (work : Prepared) → HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
  Program (Option (Fin work.jobs.length) × Memory)
def workers (work : Prepared) := NativeGoldBatchColumnWorker.workers work.geometry work.width work.random work.test work.groups work.root work.jobs

inductive Status where
  | accepted (parent : Transcript)
  | columns
  | claim (reason : ClaimError)
  | suspended

def status {Memory : Type} (ctx : Context) (work : Prepared) (pool : HashWorkerPool.Outcome Input Digest Memory work.jobs.length) : Status :=
  if HashWorkerPool.allAccepted pool.workers then match finish ctx.parameters work.binding ctx.opening with
    | .ok () => .accepted work.sample.transcript
    | .error reason => .claim reason
  else if NativeGoldPcsAcceptance.anyRejected pool.workers then .columns else .suspended

theorem status_accepted {Memory : Type} (ctx : Context) (work : Prepared) (pool : HashWorkerPool.Outcome Input Digest Memory work.jobs.length)
    (parent : Transcript) : status ctx work pool = .accepted parent ↔
      HashWorkerPool.allAccepted pool.workers = true ∧ finish ctx.parameters work.binding ctx.opening = .ok () ∧ parent = work.sample.transcript := by
  unfold status
  by_cases ready : HashWorkerPool.allAccepted pool.workers = true
  · rw [ite_eq_left ready]
    cases checked : finish ctx.parameters work.binding ctx.opening with
    | error reason => simp only [reduceCtorEq,ready,true_and,false_and]
    | ok value => cases value; simp only [Status.accepted.injEq,ready,true_and]; exact eq_comm
  · rw [ite_eq_right ready]
    split <;> simp only [reduceCtorEq,ready,Bool.false_eq_true,false_and]

structure Completion (Memory : Type) (count : ℕ) where
  pool : HashWorkerPool.Outcome Input Digest Memory count
  status : Status
inductive Outcome (Memory : Type) where
  | prior (result : PrefixOutcome)
  | completed (work : Prepared) (completion : Completion Memory work.jobs.length)

def program {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) : Program (Outcome Memory) :=
  bind (prepareProgram ctx) (fun prepared => match prepared with
    | .prepared work => bind (CausalHashWorkerPool.program (choose work) fuel (workers work) memory) (fun pool =>
        .pure (.completed work ⟨pool,status ctx work pool⟩))
    | prior => .pure (.prior prior))

structure Origin {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World)
    (work : Prepared) (completion : Completion Memory work.jobs.length) : Prop where
  prepared : (run (prepareProgram ctx) world).run.1 = .prepared work
  pool : completion.pool = (run (CausalHashWorkerPool.program (choose work) fuel (workers work) memory) world).run.1
  status : completion.status = status ctx work completion.pool
  log : (run (program ctx choose fuel memory) world).run.2 = (run (prepareProgram ctx) world).run.2 ++
    (run (CausalHashWorkerPool.program (choose work) fuel (workers work) memory) world).run.2

theorem completed_origin {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World)
    (work : Prepared) (completion : Completion Memory work.jobs.length)
    (executed : (run (program ctx choose fuel memory) world).run.1 = .completed work completion) :
    Origin ctx choose fuel memory world work completion := by
  simp only [program,OracleProgram.run_bind,ObservationReplay.run_bind] at executed
  cases prior : (run (prepareProgram ctx) world).run.1 with
  | prior previous => simp only [prior,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | encodingUnavailable => simp only [prior,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | pairingUnavailable => simp only [prior,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed; contradiction
  | prepared actual =>
    simp only [prior,OracleProgram.run_bind,ObservationReplay.run_bind,OracleProgram.run,CanonicalTranscriptSampler.run_pure] at executed
    cases executed
    exact ⟨prior,rfl,rfl,by simp only [program,OracleProgram.run_bind,ObservationReplay.run_bind,prior,OracleProgram.run,CanonicalTranscriptSampler.run_pure,List.append_nil]⟩

theorem accepted_flags {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World)
    (work : Prepared) (completion : Completion Memory work.jobs.length)
    (executed : (run (program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : Transcript) (accepted : completion.status = .accepted parent) :
    HashWorkerPool.allAccepted completion.pool.workers = true ∧ finish ctx.parameters work.binding ctx.opening = .ok () ∧ parent = work.sample.transcript := by
  have origin := completed_origin ctx choose fuel memory world work completion executed
  rw [origin.status] at accepted
  exact (status_accepted ctx work completion.pool parent).mp accepted

/-- Every original claim, including repeated prefix aliases, is finished against its computed response group. -/
theorem accepted_claims {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World)
    (work : Prepared) (completion : Completion Memory work.jobs.length)
    (executed : (run (program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : Transcript) (accepted : completion.status = .accepted parent) (index : Fin work.binding.queries.val.length) :
    ∃ response claimed,
      ctx.opening.evaluations.val[(NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index).val]? = some response ∧
      work.binding.values.val[index.val]? = some claimed ∧
      NativeGoldPcsClaim.verify ctx.parameters (work.binding.queries.val.get index) response.val claimed = .ok () :=
  claim_origin ctx.parameters work.binding ctx.opening index
    (finish_each ctx.parameters work.binding ctx.opening (accepted_flags ctx choose fuel memory world work completion executed parent accepted).2.1 index)

/-- Every accepted original claim equals the semantic native suffix fold of its shared response. -/
theorem accepted_values {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World)
    (work : Prepared) (completion : Completion Memory work.jobs.length)
    (executed : (run (program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : Transcript) (accepted : completion.status = .accepted parent) (index : Fin work.binding.queries.val.length) :
    ∃ response claimed,
      ctx.opening.evaluations.val[(NativeGoldQueryGroups.group ctx.parameters.leftVariables.val work.binding.queries index).val]? = some response ∧
      work.binding.values.val[index.val]? = some claimed ∧
      claimed.val.map NativeFieldRepresentation.goldValue = List.ofFn (FlatMatrixFold.foldAll
        (((work.binding.queries.val.get index).models.drop ctx.parameters.leftVariables.val).map (NativeGoldPackedMeaning.pairValue ctx.parameters.width.val))
        (fun cell lane => NativeFieldRepresentation.goldValue
          (response.val[lane.val*2^(ctx.parameters.numVariables.val-ctx.parameters.leftVariables.val)+cell.val]?.getD 0))) := by
  obtain ⟨response,claimed,responseRead,valueRead,verified⟩ := accepted_claims ctx choose fuel memory world work completion executed parent accepted index
  have valid := prepared_query_valid ctx world work (completed_origin ctx choose fuel memory world work completion executed).prepared index
  exact ⟨response,claimed,responseRead,valueRead,NativeGoldPcsClaim.accepted_value ctx.parameters _ _ _ valid verified⟩

/-- All raw column workers replay in the final shared cache, also after later enclosing work. -/
theorem accepted_workers {Memory : Type} (ctx : Context) (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World)
    (work : Prepared) (completion : Completion Memory work.jobs.length)
    (executed : (run (program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : Transcript) (accepted : completion.status = .accepted parent)
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (run (program ctx choose fuel memory) world).run.2.Sublist history) :
    ∀ job ∈ work.jobs, ∃ leaf siblings,
      NativeGoldColumnAuthentication.decodePath work.geometry.height job.column.path.val = some (leaf,siblings) ∧
      job.column.path.val = leaf :: siblings.toList ∧
      simulateQ (JointHashCache.project history).cache.toPartialImpl
        (NativeMerkleVerifier.verifyPayload NativeGoldColumnAuthentication.encoding work.geometry.height job.index job.column.values leaf work.root siblings) = some true ∧
      NativeGoldBatchColumnWorker.check work.geometry work.width work.random work.test job.column.values.val work.groups job.index = true ∧
      ∀ response ∈ work.groups, NativeGoldColumnChecks.check work.geometry work.width work.random response.1 work.test response.2 job.column.values.val job.index = true := by
  have origin := completed_origin ctx choose fuel memory world work completion executed
  have ready := (accepted_flags ctx choose fuel memory world work completion executed parent accepted).1
  rw [origin.pool] at ready
  have known : CausalHashWorkerPool.Known (JointHashCache.project history).cache
      (run (CausalHashWorkerPool.program (choose work) fuel (workers work) memory) world).run.2 := by
    intro input digest member
    have contained : Observation.hash input (List.ofFn digest) ∈ (run (program ctx choose fuel memory) world).run.2 := by
      rw [origin.log]
      exact List.mem_append_right _ member
    exact NativeHashOracleBridge.cache_known world _ truthful input digest (observed.subset contained)
  intro job member
  obtain ⟨index,same⟩ := List.mem_iff_get.mp member
  subst job
  exact NativeGoldBatchColumnWorker.worker_raw_replay _ _ _ _ _ _ _ _ _
    (CausalHashWorkerPool.accepted_replays (choose work) fuel (workers work) memory world _ known ready index)
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchPcsProgram
