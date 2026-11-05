module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsPaths
public import FormalProof4FHE.HasteBoots.NativeGoldPcsWorkerSoundness
public import FormalProof4FHE.HasteBoots.ParallelColumnAvailability

@[expose] public section

/-! Lossless typed availability requests computed from original raw workers.
No path, Merkle acceptance or replay certificate is an adapter input. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldRawRequests

open NativeGoldColumnWorker (Job)
open NativeGoldColumnAuthentication (decodePath encoding)
open NativeRootMessage (Digest)
open NativeLookupRequestWire (Row)
open InputIndexedOracle (Input)
open OracleSpec OracleComp

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

abbrev Request {Cfg : Type} (height : Cfg → ℕ) :=
  NativeOpeningAvailability.Request (Digest := Digest) (Payload := Row) height

def fromJob {Cfg : Type} (height : Cfg → ℕ) (tag : Cfg) (root : Digest) (job : Job) : Option (Request height) :=
  if bound : job.index < 2^(height tag) then
    match decodePath (height tag) job.column.path.val with
    | none => none
    | some (leaf,siblings) => some ⟨tag,root,⟨job.index,bound⟩,job.column.values,leaf,siblings⟩
  else none

theorem fromJob_spec {Cfg : Type} (height : Cfg → ℕ) (tag : Cfg) (root : Digest) (job : Job) (request : Request height)
    (success : fromJob height tag root job = some request) :
    ∃ bound leaf siblings, decodePath (height tag) job.column.path.val = some (leaf,siblings) ∧
      request = ⟨tag,root,⟨job.index,bound⟩,job.column.values,leaf,siblings⟩ := by
  unfold fromJob at success
  split at success
  next bound =>
    split at success
    next => contradiction
    next leaf siblings parsed =>
      cases success
      exact ⟨bound,leaf,siblings,parsed,rfl⟩
  next => contradiction

theorem decode_complete (height : ℕ) (path : List Digest) (size : path.length = height+1) :
    ∃ leaf siblings, decodePath height path = some (leaf,siblings) := by
  cases path with
  | nil => simp only [List.length_nil] at size; omega
  | cons leaf tail =>
    have length : tail.length = height := by simp only [List.length_cons] at size; omega
    exact ⟨leaf,⟨tail,length⟩,by simp only [decodePath,dite_eq_left length]⟩

theorem fromJob_complete {Cfg : Type} (height : Cfg → ℕ) (tag : Cfg) (root : Digest) (job : Job)
    (bound : job.index < 2^(height tag)) (size : job.column.path.val.length = height tag+1) :
    ∃ request, fromJob height tag root job = some request := by
  obtain ⟨leaf,siblings,parsed⟩ := decode_complete (height tag) job.column.path.val size
  exact ⟨⟨tag,root,⟨job.index,bound⟩,job.column.values,leaf,siblings⟩,
    by simp only [fromJob,dite_eq_left bound,parsed]⟩

/-- Every successful result retains the job alongside its computed request. -/
def entries {Cfg : Type} (height : Cfg → ℕ) (tag : Cfg) (root : Digest) : List Job → Option (List (Job × Request height))
  | [] => some []
  | job :: jobs => (fromJob height tag root job).bind (fun request =>
    (entries height tag root jobs).map (fun rest => (job,request) :: rest))

theorem entries_spec {Cfg : Type} (height : Cfg → ℕ) (tag : Cfg) (root : Digest)
    (jobs : List Job) (result : List (Job × Request height))
    (success : entries height tag root jobs = some result) :
    result.map Prod.fst = jobs ∧ ∀ entry ∈ result, fromJob height tag root entry.1 = some entry.2 := by
  induction jobs generalizing result with
  | nil => cases success; exact ⟨rfl,by simp⟩
  | cons job jobs ih =>
    obtain ⟨request,read,remaining⟩ := Option.bind_eq_some_iff.mp success
    obtain ⟨rest,restRead,same⟩ := Option.map_eq_some_iff.mp remaining
    subst result
    have previous := ih rest restRead
    refine ⟨congrArg (List.cons job) previous.1,?_⟩
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact read
    · exact previous.2 entry member

theorem entries_complete {Cfg : Type} (height : Cfg → ℕ) (tag : Cfg) (root : Digest) (jobs : List Job)
    (valid : ∀ job ∈ jobs, job.index < 2^(height tag) ∧ job.column.path.val.length = height tag+1) :
    ∃ result, entries height tag root jobs = some result := by
  induction jobs with
  | nil => exact ⟨[],rfl⟩
  | cons job jobs ih =>
    have first := valid job List.mem_cons_self
    obtain ⟨request,read⟩ := fromJob_complete height tag root job first.1 first.2
    obtain ⟨rest,restRead⟩ := ih (fun item member => valid item (List.mem_cons_of_mem job member))
    exact ⟨(job,request)::rest,by simp only [entries,read,Option.bind_some,restRead,Option.map_some]⟩

noncomputable section

/-- The replay predicate is obtained from the actual raw worker computation,
without projecting its payload to field values. -/
theorem replay_of_worker {Cfg : Type} (height : Cfg → ℕ) (tag : Cfg) (root : Digest)
    (geometry : NativeBrakedownParameters.Geometry) (width : ℕ)
    (random structured test evaluation : List NativeFieldRepresentation.GoldWord) (job : Job)
    (request : Request height) (prepared : fromJob height tag root job = some request)
    (matchesHeight : geometry.height = height tag) (cache : (Input →ₒ Digest).QueryCache)
    (accepted : simulateQ cache.toPartialImpl
      (NativeGoldColumnWorker.worker geometry width random structured test evaluation root job.index job.column) = some true) :
    ParallelColumnAvailability.Replays encoding height request cache := by
  obtain ⟨bound,leaf,siblings,parsed,rfl⟩ := fromJob_spec height tag root job request prepared
  have authenticated := (NativeGoldColumnWorker.worker_accepts geometry width random structured test evaluation root job.index job.column cache accepted).1
  rw [matchesHeight] at authenticated
  simpa only [ParallelColumnAvailability.Replays,NativeGoldColumnWorker.authentication,parsed] using authenticated

end
end FormalProof4FHE.HasteBoots.NativeGoldRawRequests
