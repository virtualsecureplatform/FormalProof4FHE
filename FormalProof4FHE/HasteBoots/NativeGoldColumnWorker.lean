module

public import FormalProof4FHE.HasteBoots.NativeGoldColumnChecks
public import FormalProof4FHE.HasteBoots.NativeGoldColumnAuthentication
public import FormalProof4FHE.HasteBoots.HashWorkerPool

@[expose] public section

/-! Raw Goldilocks column workers for the shared hash pool. The authenticated
payload is the original Row, not its non-injective field-value projection.
The worker computes its coordinate flag only after authentication succeeds.
Native Rayon/Rust refinement remains separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldColumnWorker

open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeFieldRepresentation (GoldWord)
open NativeGoldColumnAuthentication (Column encoding decodePath)
open NativeBrakedownParameters (Geometry)
open OracleSpec OracleComp

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def authentication (height index : ℕ) (root : Digest) (column : Column) : OracleComp (Input →ₒ Digest) Bool :=
  match decodePath height column.path.val with
  | none => pure false
  | some (leaf,siblings) => NativeMerkleVerifier.verifyPayload encoding height index column.values leaf root siblings

theorem authentication_compile (height index : ℕ) (root : Digest) (column : Column) :
    NativeHashOracleBridge.compile (authentication height index root column) =
      NativeGoldColumnAuthentication.verify height index root column := by
  cases parsed : decodePath height column.path.val with
  | none => simp only [authentication,NativeGoldColumnAuthentication.verify,parsed,NativeHashOracleBridge.compile_pure]
  | some pair =>
    obtain ⟨leaf,siblings⟩ := pair
    simp only [authentication,NativeGoldColumnAuthentication.verify,parsed]
    exact (NativeGoldColumnAuthentication.verifyDecoded_compile height index root leaf column.values siblings).symm

def worker (geometry : Geometry) (width : ℕ) (random structured test evaluation : List GoldWord)
    (root : Digest) (index : ℕ) (column : Column) : OracleComp (Input →ₒ Digest) Bool := do
  let accepted ← authentication geometry.height index root column
  if accepted then pure (NativeGoldColumnChecks.check geometry width random structured test evaluation column.values.val index)
  else pure false

theorem worker_compile (geometry : Geometry) (width : ℕ) (random structured test evaluation : List GoldWord)
    (root : Digest) (index : ℕ) (column : Column) :
    NativeHashOracleBridge.compile (worker geometry width random structured test evaluation root index column) =
      OracleProgram.bind (NativeGoldColumnAuthentication.verify geometry.height index root column)
        (fun accepted => .pure (if accepted then NativeGoldColumnChecks.check geometry width random structured test evaluation column.values.val index else false)) := by
  rw [worker,NativeHashOracleBridge.compile_bind,authentication_compile]
  congr 1
  funext accepted
  cases accepted <;> rfl

theorem worker_accepts (geometry : Geometry) (width : ℕ) (random structured test evaluation : List GoldWord)
    (root : Digest) (index : ℕ) (column : Column) (cache : (Input →ₒ Digest).QueryCache)
    (accepted : simulateQ cache.toPartialImpl (worker geometry width random structured test evaluation root index column) = some true) :
    simulateQ cache.toPartialImpl (authentication geometry.height index root column) = some true ∧
      NativeGoldColumnChecks.check geometry width random structured test evaluation column.values.val index = true := by
  rw [worker,simulateQ_bind] at accepted
  obtain ⟨flag,read,rest⟩ := Option.bind_eq_some_iff.mp accepted
  cases flag with
  | false => simp only [Bool.false_eq_true,reduceIte,simulateQ_pure] at rest; contradiction
  | true => exact ⟨read,Option.some.inj rest⟩

/-- Replay authenticates the exact received raw Row and parsed native path. -/
theorem worker_raw_replay (geometry : Geometry) (width : ℕ) (random structured test evaluation : List GoldWord)
    (root : Digest) (index : ℕ) (column : Column) (cache : (Input →ₒ Digest).QueryCache)
    (accepted : simulateQ cache.toPartialImpl (worker geometry width random structured test evaluation root index column) = some true) :
    ∃ leaf siblings, decodePath geometry.height column.path.val = some (leaf,siblings) ∧
      column.path.val = leaf :: siblings.toList ∧
      simulateQ cache.toPartialImpl (NativeMerkleVerifier.verifyPayload encoding geometry.height index column.values leaf root siblings) = some true ∧
      NativeGoldColumnChecks.check geometry width random structured test evaluation column.values.val index = true := by
  have facts := worker_accepts geometry width random structured test evaluation root index column cache accepted
  cases parsed : decodePath geometry.height column.path.val with
  | none =>
    have impossible : (some false : Option Bool) = some true := by
      simpa only [authentication,parsed,simulateQ_pure,Option.pure_def] using facts.1
    cases impossible
  | some pair =>
    obtain ⟨leaf,siblings⟩ := pair
    exact ⟨leaf,siblings,rfl,NativeGoldColumnAuthentication.decodePath_spec _ _ _ _ parsed,
      by simpa only [authentication,parsed] using facts.1,facts.2⟩

structure Job where
  index : ℕ
  column : Column

noncomputable section

def workers (geometry : Geometry) (width : ℕ) (random structured test evaluation : List GoldWord)
    (root : Digest) (jobs : List Job) : HashWorkerPool.Workers Input Digest jobs.length :=
  fun index => worker geometry width random structured test evaluation root (jobs.get index).index (jobs.get index).column

/-- Scheduling controls individual hash advances and cancellation; its output
does not contain an acceptance certificate. -/
def program {Cfg Memory : Type} (geometry : Geometry) (width : ℕ) (random structured test evaluation : List GoldWord)
    (root : Digest) (jobs : List Job)
    (choose : HashWorkerPool.Workers Input Digest jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory) :=
  HashWorkerPool.program choose fuel (workers geometry width random structured test evaluation root jobs) memory

variable {Cfg Memory : Type} [SampleableType Digest]

/-- Actual pool acceptance establishes each original raw worker's replay and
computed coordinates in the final shared cache, under arbitrary interleaving. -/
theorem accepted_jobs (geometry : Geometry) (width : ℕ) (random structured test evaluation : List GoldWord)
    (dummy root : Digest) (jobs : List Job) (shape : Cfg → BinaryTree.Skeleton)
    (choose : HashWorkerPool.Workers Input Digest jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : HashWorkerPool.Outcome Input Digest Memory jobs.length × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy shape)
      (program geometry width random structured test evaluation root jobs choose fuel memory)).run before))
    (accepted : HashWorkerPool.allAccepted outcome.1.workers = true) :
    ∀ job ∈ jobs, ∃ leaf siblings, decodePath geometry.height job.column.path.val = some (leaf,siblings) ∧
      job.column.path.val = leaf :: siblings.toList ∧
      simulateQ outcome.2.hash.cache.toPartialImpl (NativeMerkleVerifier.verifyPayload encoding geometry.height job.index job.column.values leaf root siblings) = some true ∧
      NativeGoldColumnChecks.check geometry width random structured test evaluation job.column.values.val job.index = true := by
  intro job member
  obtain ⟨index,same⟩ := List.mem_iff_get.mp member
  subst job
  exact worker_raw_replay geometry width random structured test evaluation root _ _ _
    (HashWorkerPool.accepted_replays encoding dummy shape choose fuel
      (workers geometry width random structured test evaluation root jobs) memory before outcome supported accepted index)

end
end FormalProof4FHE.HasteBoots.NativeGoldColumnWorker
