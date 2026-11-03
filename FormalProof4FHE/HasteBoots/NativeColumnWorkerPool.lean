module

public import FormalProof4FHE.HasteBoots.HashWorkerPool
public import FormalProof4FHE.HasteBoots.AuthenticatedColumnChecks

@[expose] public section

/-!
# Native column acceptance from an actual interleaved worker pool

Each worker hashes the whole column, verifies its bottom-up sibling path and
then checks both coordinate families. Workers interleave at individual hash
calls. The pool's computed flag, rather than a caller-supplied flag, establishes
native replay and every coordinate check on the actual final shared cache.
Cancellation retains every issued call. Native Rayon refinement and a concrete
honest scheduling/completion bound remain open.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.NativeColumnWorkerPool

noncomputable section

variable {F Input Digest Cfg Memory : Type} [Field F] [DecidableEq F]
  [DecidableEq Input] [DecidableEq Digest] {width leftCount block height : ℕ}

/-- A native worker checks coordinates only after its authentication succeeds. -/
def worker (enc : MerkleOracle.Encoding Input Digest (List F)) (root : Digest)
    (testWeights structuredWeights : Fin (width * (leftCount * width)) → F)
    (testResponse structuredResponse : Fin (width * ((2 ^ height) * block)) → F)
    (column : NativeColumnLayout.Column F Digest height (leftCount * width) block) :
    OracleComp (Input →ₒ Digest) Bool := do
  let authenticated ← NativeMerkleVerifier.verifyPayload enc height column.position.val
    (NativeColumnLayout.packPayload column.values) column.leaf root column.siblings
  if authenticated then
    pure (NativeColumnLayout.allCoordinates [column] testWeights structuredWeights testResponse structuredResponse)
  else pure false

omit [DecidableEq Input] in
/-- Successful replay of the literal worker entails both native authentication
and the coordinate loop; no commitment-security premise is used. -/
theorem worker_accepts (enc : MerkleOracle.Encoding Input Digest (List F)) (root : Digest)
    (testWeights structuredWeights : Fin (width * (leftCount * width)) → F)
    (testResponse structuredResponse : Fin (width * ((2 ^ height) * block)) → F)
    (column : NativeColumnLayout.Column F Digest height (leftCount * width) block)
    (cache : (Input →ₒ Digest).QueryCache)
    (accepted : simulateQ cache.toPartialImpl
      (worker enc root testWeights structuredWeights testResponse structuredResponse column) = some true) :
    simulateQ cache.toPartialImpl (NativeMerkleVerifier.verifyPayload enc height column.position.val
      (NativeColumnLayout.packPayload column.values) column.leaf root column.siblings) = some true ∧
    NativeColumnLayout.allCoordinates [column] testWeights structuredWeights testResponse structuredResponse = true := by
  rw [worker, simulateQ_bind] at accepted
  obtain ⟨authenticated, read, remaining⟩ := Option.bind_eq_some_iff.mp accepted
  cases authenticated with
  | false =>
    simp only [Bool.false_eq_true, reduceIte, simulateQ_pure] at remaining
    exact (Bool.false_ne_true (Option.some.inj remaining)).elim
  | true =>
    exact ⟨read, Option.some.inj remaining⟩

/-- Native per-column acceptance programs, indexed by their received positions
in the typed proof list. Equal column indices do not merge distinct workers. -/
def workers (enc : MerkleOracle.Encoding Input Digest (List F)) (root : Digest)
    (testWeights structuredWeights : Fin (width * (leftCount * width)) → F)
    (testResponse structuredResponse : Fin (width * ((2 ^ height) * block)) → F)
    (columns : List (NativeColumnLayout.Column F Digest height (leftCount * width) block)) :
    HashWorkerPool.Workers Input Digest columns.length :=
  fun index => worker enc root testWeights structuredWeights testResponse structuredResponse (columns.get index)

/-- Return the column phase's computed flag and retained scheduler memory in
the exact shape expected by the short-circuit factor-opening step. -/
def program (enc : MerkleOracle.Encoding Input Digest (List F)) (root : Digest)
    (testWeights structuredWeights : Fin (width * (leftCount * width)) → F)
    (testResponse structuredResponse : Fin (width * ((2 ^ height) * block)) → F)
    (columns : List (NativeColumnLayout.Column F Digest height (leftCount * width) block))
    (choose : HashWorkerPool.Workers Input Digest columns.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin columns.length) × Memory))
    (fuel : ℕ) (memory : Memory) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest)
      ((List (NativeColumnLayout.Column F Digest height (leftCount * width) block) × Memory) × Bool) :=
  (fun outcome => ((columns, outcome.memory), HashWorkerPool.allAccepted outcome.workers)) <$>
    HashWorkerPool.program choose fuel (workers enc root testWeights structuredWeights testResponse structuredResponse columns) memory

variable [SampleableType Digest]

/-- The actual pool flag discharges the replay interface for every returned
column, and both response families pass their native coordinate checks. -/
theorem accepted_columns (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy root : Digest)
    (shape : Cfg → Skeleton)
    (testWeights structuredWeights : Fin (width * (leftCount * width)) → F)
    (testResponse structuredResponse : Fin (width * ((2 ^ height) * block)) → F)
    (columns : List (NativeColumnLayout.Column F Digest height (leftCount * width) block))
    (choose : HashWorkerPool.Workers Input Digest columns.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin columns.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ((List (NativeColumnLayout.Column F Digest height (leftCount * width) block) × Memory) × Bool) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program enc root testWeights structuredWeights testResponse structuredResponse columns choose fuel memory)).run before))
    (accepted : outcome.1.2 = true) :
    outcome.1.1.1 = columns ∧
    (∀ column ∈ outcome.1.1.1,
      simulateQ outcome.2.hash.cache.toPartialImpl (NativeMerkleVerifier.verifyPayload enc height column.position.val
        (NativeColumnLayout.packPayload column.values) column.leaf root column.siblings) = some true) ∧
    NativeColumnLayout.allCoordinates outcome.1.1.1 testWeights structuredWeights testResponse structuredResponse = true := by
  rw [program, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨finished, finishedSupported, equal⟩ := supported
  subst outcome
  have each : ∀ column ∈ columns,
      simulateQ finished.2.hash.cache.toPartialImpl (NativeMerkleVerifier.verifyPayload enc height column.position.val
        (NativeColumnLayout.packPayload column.values) column.leaf root column.siblings) = some true ∧
      NativeColumnLayout.allCoordinates [column] testWeights structuredWeights testResponse structuredResponse = true := by
    intro column member
    obtain ⟨index, equal⟩ := List.mem_iff_get.mp member
    subst column
    exact worker_accepts enc root testWeights structuredWeights testResponse structuredResponse _ _
      (HashWorkerPool.accepted_replays enc dummy shape choose fuel
        (workers enc root testWeights structuredWeights testResponse structuredResponse columns) memory before
        finished finishedSupported accepted index)
  refine ⟨rfl, fun column member => (each column member).1, ?_⟩
  unfold NativeColumnLayout.allCoordinates
  apply List.all_eq_true.mpr
  intro column member
  simpa only [NativeColumnLayout.allCoordinates, List.all_cons, List.all_nil, Bool.and_true] using (each column member).2

/-- Completed native workers remain authenticated through every later shared
cache extension, including subsequent factors or terminal callbacks. -/
theorem accepted_columns_later (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy root : Digest)
    (shape : Cfg → Skeleton)
    (testWeights structuredWeights : Fin (width * (leftCount * width)) → F)
    (testResponse structuredResponse : Fin (width * ((2 ^ height) * block)) → F)
    (columns : List (NativeColumnLayout.Column F Digest height (leftCount * width) block))
    (choose : HashWorkerPool.Workers Input Digest columns.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin columns.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ((List (NativeColumnLayout.Column F Digest height (leftCount * width) block) × Memory) × Bool) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program enc root testWeights structuredWeights testResponse structuredResponse columns choose fuel memory)).run before))
    (accepted : outcome.1.2 = true) (later : (Input →ₒ Digest).QueryCache) (extension : outcome.2.hash.cache ≤ later) :
    ∀ column ∈ outcome.1.1.1,
      simulateQ later.toPartialImpl (NativeMerkleVerifier.verifyPayload enc height column.position.val
        (NativeColumnLayout.packPayload column.values) column.leaf root column.siblings) = some true := by
  have authenticated := (accepted_columns enc dummy root shape testWeights structuredWeights testResponse
    structuredResponse columns choose fuel memory before outcome supported accepted).2.1
  intro column member
  exact QueryCache.simulateQ_toPartialImpl_mono extension _ (authenticated column member)

end

end FormalProof4FHE.HasteBoots.NativeColumnWorkerPool
