module

public import FormalProof4FHE.HasteBoots.NativeBatchChecks
public import FormalProof4FHE.HasteBoots.NativeBatchColumnWorkerPool
public import FormalProof4FHE.HasteBoots.StoppingJointMatrixOpening

@[expose] public section

/-!
# Concrete native batch step with computed grouping and worker flags

A fixed query/value family uses one random test and one shared column draw.
The verifier computes prefix groups, representative weights, coverage and every
query's finish check. The provider supplies no trusted acceptance flag. Bad
coverage rejects before starting any authentication worker, retaining earlier
provider work. Successful steps replay in later caches and imply the batch
arithmetic event or one availability disagreement. Transcript, raw decoding,
native NTT/Rust and honest scheduling-completion refinement remain open.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.NativeBatchVerifier

noncomputable section

structure Protocol (F Input Digest Cfg Response Memory : Type)
    (b front suffix claims m queries height : ℕ) where
  encoding : MerkleOracle.Encoding Input Digest (List F)
  domain : Fin (2 ^ height) ↪ F
  root : Digest
  query : NativeBatchChecks.QueryFamily F b front suffix claims
  values : Fin claims → Fin b → F
  testResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F
  groupResponse : ℕ → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F
  prepare : Memory → OracleComp (SharedSequence.Shared Cfg Input Digest) Memory
  respond : Memory → TestMatrix F (2 ^ front) b → OracleComp (SharedSequence.Shared Cfg Input Digest) Response
  receiveColumns : Memory → SampleData F Response (2 ^ front) b height queries →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (Columns F Digest (2 ^ front) b height × Memory)
  choose : Memory → (sample : SampleData F Response (2 ^ front) b height queries) →
    (columns : Columns F Digest (2 ^ front) b height) → HashWorkerPool.Workers Input Digest columns.length → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Option (Fin columns.length) × Memory)
  fuel : Memory → SampleData F Response (2 ^ front) b height queries → Columns F Digest (2 ^ front) b height → ℕ

variable {F Input Digest Cfg Response Memory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b front suffix claims m queries height : ℕ}

def next (p : Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (incoming : Memory) (sample : SampleData F Response (2 ^ front) b height queries) := do
  let received ← p.receiveColumns incoming sample
  if NativeBatchChecks.columnsCheck received.1 sample.2 then
    NativeBatchColumnWorkerPool.program p.encoding p.root
      (NativeColumnLayout.flattenWeights sample.1.1)
      (fun group => NativeColumnLayout.flattenWeights (MatrixResponse.weights
        (NativeBatchChecks.groupLeft (front := front) (suffix := suffix) p.query group)))
      (NativeColumnLayout.flattenResponse (MatrixOpeningSecurity.encodeMessages (m := m) p.domain
        (p.testResponse sample.1.1 sample.1.2)))
      (fun group => NativeColumnLayout.flattenResponse (MatrixOpeningSecurity.encodeMessages (m := m) p.domain
        (p.groupResponse group.val sample.1.1 sample.1.2)))
      received.1 (p.choose incoming sample received.1) (p.fuel incoming sample received.1) received.2
  else pure ((received.1, received.2), false)

def checks (p : Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height) :
    JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries → Bool :=
  NativeBatchChecks.check (m := m) p.domain p.query p.values p.testResponse p.groupResponse

section Step

variable [SampleableType (TestMatrix F (2 ^ front) b)] [SampleableType (Fin queries → Fin (2 ^ height))]

def sampledStep (p : Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height) (memory : Memory) :=
  StoppingJointMatrixOpening.step (fun _ : Unit => p.respond)
    (StoppingJointMatrixOpening.checkedNext (fun _ : Unit => checks p) (fun _ : Unit => next p)) () memory

/-- Each root's context/query/value binding precedes its own fresh test, and
is skipped with that root if an earlier batch has already rejected. -/
def step (p : Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height) (memory : Memory) := do
  let prepared ← p.prepare memory
  sampledStep p prepared

end Step

variable [SampleableType Digest]

/-- Coverage failure cannot start a worker or schedule any worker hash. A true
flag instead entails the actual batch worker pool's final-cache authentication. -/
theorem next_accepts_later
    (p : Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (dummy : Digest) (shape : Cfg → Skeleton) (tag : Cfg) (incoming : Memory)
    (sample : SampleData F Response (2 ^ front) b height queries)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ((Columns F Digest (2 ^ front) b height × Memory) × Bool) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) p.encoding dummy shape)
      (next p incoming sample)).run before)) (accepted : outcome.1.2 = true)
    (later : (Input →ₒ Digest).QueryCache) (extension : outcome.2.hash.cache ≤ later) :
    ∀ column ∈ outcome.1.1.1, ParallelColumnAvailability.Replays p.encoding (fun _ : Cfg => height)
      (AuthenticatedColumnChecks.request (fun _ : Cfg => height) tag p.root column) later := by
  rw [next, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨received, _, poolSupported⟩ := supported
  cases covered : NativeBatchChecks.columnsCheck received.1.1 sample.2 with
  | false =>
    simp only [covered, Bool.false_eq_true, reduceIte, simulateQ_pure, StateT.run_pure] at poolSupported
    have equal := eq_of_mem_support_pure _ poolSupported
    subst outcome
    exact (Bool.false_ne_true accepted).elim
  | true =>
    simp only [covered, reduceIte] at poolSupported
    exact NativeBatchColumnWorkerPool.accepted_columns_later p.encoding dummy p.root shape _ _ _ _
      received.1.1 (p.choose incoming sample received.1.1) (p.fuel incoming sample received.1.1)
      received.1.2 received.2 outcome poolSupported accepted later extension

section Runtime

variable [SampleableType (TestMatrix F (2 ^ front) b)] [SampleableType (Fin queries → Fin (2 ^ height))]

/-- The actual step flag implies coverage, all grouped coordinates, every
original finish value and authentication in any later cache. -/
theorem sampled_accepts_later
    (p : Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (dummy : Digest) (shape : Cfg → Skeleton) (tag : Cfg) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ShortCircuitSequence.StepResult (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) p.encoding dummy shape)
      (sampledStep p memory)).run before)) (accepted : outcome.1.accepted = true)
    (later : (Input →ₒ Digest).QueryCache) (extension : outcome.2.hash.cache ≤ later) :
    checks p outcome.1.result = true ∧
    ∀ column ∈ outcome.1.result.2, ParallelColumnAvailability.Replays p.encoding (fun _ : Cfg => height)
      (AuthenticatedColumnChecks.request (fun _ : Cfg => height) tag p.root column) later := by
  rw [sampledStep, StoppingJointMatrixOpening.checked_step_eq, ShortCircuitSequence.enforce,
    simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨raw, rawSupported, equal⟩ := supported
  subst outcome
  obtain ⟨workerAccepted, checked⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨earlier, _, finished, finishedSupported, rawEqual⟩ :=
    StoppingJointMatrixOpening.step_supported p.encoding dummy shape (fun _ : Unit => p.respond)
      (fun _ : Unit => next p) () memory before raw rawSupported
  subst raw
  exact ⟨checked, next_accepts_later p dummy shape tag memory earlier.1 earlier.2 finished finishedSupported
    workerAccepted later extension⟩

/-- The actual step flag implies coverage, all grouped coordinates, every
original finish value and authentication in any later cache. -/
theorem step_accepts_later
    (p : Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (dummy : Digest) (shape : Cfg → Skeleton) (tag : Cfg) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ShortCircuitSequence.StepResult (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) p.encoding dummy shape)
      (step p memory)).run before)) (accepted : outcome.1.accepted = true)
    (later : (Input →ₒ Digest).QueryCache) (extension : outcome.2.hash.cache ≤ later) :
    checks p outcome.1.result = true ∧
    ∀ column ∈ outcome.1.result.2, ParallelColumnAvailability.Replays p.encoding (fun _ : Cfg => height)
      (AuthenticatedColumnChecks.request (fun _ : Cfg => height) tag p.root column) later := by
  rw [step, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨prepared, _, sampled⟩ := supported
  exact sampled_accepts_later p dummy shape tag prepared.1 prepared.2 outcome sampled accepted later extension

/-- Incorrect supplied values on a successful native step imply arithmetic
failure or the common availability event, with no replay certificate input. -/
theorem wrong_implies_arithmetic_or_disagreement
    (p : Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (dummy : Digest) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun _ : Cfg => Skeleton.perfect height)) tag)
    (root : checkpoint.root = p.root) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (outcome : ShortCircuitSequence.StepResult (JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) p.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
      (step p memory)).run before)) (accepted : outcome.1.accepted = true)
    (recorded : ⟨tag, checkpoint⟩ ∈ outcome.2.checkpoints.checkpoints)
    (different : ∃ claim, p.values claim ≠ matrixEvaluation (NativeBatchChecks.left (front := front) (suffix := suffix) p.query claim)
      (NativeBatchChecks.right (front := front) (suffix := suffix) p.query claim)
      (MatrixOpeningSecurity.extract p.domain capacity radius (word p.encoding dummy (fun _ : Cfg => height) tag checkpoint))) :
    BatchMatrixSampling.ArithmeticBad p.domain capacity radius (word p.encoding dummy (fun _ : Cfg => height) tag checkpoint)
      (NativeBatchChecks.left (front := front) (suffix := suffix) p.query)
      (NativeBatchChecks.right (front := front) (suffix := suffix) p.query) p.values p.testResponse
      (NativeBatchChecks.structured p.query p.groupResponse) outcome.1.result.1 ∨
      CheckpointAvailability.Disagreement p.encoding dummy (fun _ : Cfg => Skeleton.perfect height) outcome.2 := by
  have verified := step_accepts_later p dummy (fun _ : Cfg => Skeleton.perfect height) tag memory before outcome
    supported accepted outcome.2.hash.cache le_rfl
  exact NativeBatchChecks.wrong_implies_arithmetic_or_disagreement p.encoding dummy tag checkpoint p.domain p.query p.values
    capacity radius p.testResponse p.groupResponse outcome.1.result outcome.2 recorded
    (by simpa only [root] using verified.2) verified.1 different

variable {K : Type} [Field K] [Algebra F K] [Fintype F] [Fintype K] [DecidableEq K]
  [SampleableType ((Fin (2 ^ front) × Fin b) → K)]

/-- One PCS arithmetic loss for this actual complete native batch step, despite
multiple queries, response groups, shared columns and interleaved worker calls. -/
theorem sampled_arithmetic_bound [NeZero m] [NeZero b]
    (p : Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest) (shape : Cfg → Skeleton)
    (enough : m ≤ Fintype.card (Fin (2 ^ height))) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (source : Fin (2 ^ height) → (Fin (2 ^ front) × Fin b) → Fin b → F)
    (memory : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) p.domain) m : Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) p.encoding dummy shape)
      (sampledStep p memory)).run state}[
        BatchMatrixSampling.ArithmeticBad p.domain capacity radius source
          (NativeBatchChecks.left (front := front) (suffix := suffix) p.query)
          (NativeBatchChecks.right (front := front) (suffix := suffix) p.query) p.values p.testResponse
          (NativeBatchChecks.structured p.query p.groupResponse) outcome.1.result.1] ≤
      JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) p.domain radius := by
  rw [sampledStep, StoppingJointMatrixOpening.step, simulateQ_map, StateT.run_map, prEvent_map]
  exact BatchMatrixSampling.arithmetic_after_bound basis p.domain enough capacity radius source
    (NativeBatchChecks.left (front := front) (suffix := suffix) p.query)
    (NativeBatchChecks.right (front := front) (suffix := suffix) p.query) p.values p.encoding dummy shape
    (p.respond memory) p.testResponse (NativeBatchChecks.structured p.query p.groupResponse)
    (StoppingJointMatrixOpening.checkedNext (fun _ : Unit => checks p) (fun _ : Unit => next p) () memory) state small

/-- One PCS arithmetic loss for this actual complete native batch step, despite
multiple queries, response groups, shared columns and interleaved worker calls. -/
theorem arithmetic_bound [NeZero m] [NeZero b]
    (p : Protocol F Input Digest Cfg Response Memory b front suffix claims m queries height)
    (basis : Module.Basis (Fin b) F K) (dummy : Digest) (shape : Cfg → Skeleton)
    (enough : m ≤ Fintype.card (Fin (2 ^ height))) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (source : Fin (2 ^ height) → (Fin (2 ^ front) × Fin b) → Fin b → F)
    (memory : Memory) (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (small : (radius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) p.domain) m : Set (Fin (2 ^ height) → K)) : ℚ≥0) / 3) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) p.encoding dummy shape)
      (step p memory)).run state}[
        BatchMatrixSampling.ArithmeticBad p.domain capacity radius source
          (NativeBatchChecks.left (front := front) (suffix := suffix) p.query)
          (NativeBatchChecks.right (front := front) (suffix := suffix) p.query) p.values p.testResponse
          (NativeBatchChecks.structured p.query p.groupResponse) outcome.1.result.1] ≤
      JointMatrixOpening.error (K := K) (m := m) (b := b) (queries := queries) p.domain radius := by
  rw [step, simulateQ_bind, StateT.run_bind]
  apply prEvent_bind_le_of_forall_le
  intro prepared
  exact sampled_arithmetic_bound p basis dummy shape enough capacity radius source prepared.1 prepared.2 small

end Runtime

end

end FormalProof4FHE.HasteBoots.NativeBatchVerifier
