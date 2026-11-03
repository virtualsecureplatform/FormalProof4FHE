module

public import FormalProof4FHE.HasteBoots.NativeColumnWorkerPool
public import FormalProof4FHE.HasteBoots.NativeFactorChecks
public import FormalProof4FHE.HasteBoots.StoppingJointMatrixOpening

@[expose] public section

/-!
# Native matrix-opening steps with computed worker acceptance

The prover supplies responses and columns; it does not supply a trusted
verification flag. An actual interleaved native worker pool computes that flag,
then literal coverage/coordinate/claimed-value checks gate the next factor.
All callbacks, private coins and worker hashes use the same shared execution.
Acceptance establishes replay in every later cache. Production transcript,
Rayon/Rust refinement and a concrete honest completion bound remain open.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.NativeMatrixVerifier

noncomputable section

/-- Public opening data and arbitrary prover/scheduler programs. Verification
flags are computed by the verifier and are deliberately absent from this input. -/
structure Protocol (F Factor Input Digest Cfg Response Memory : Type)
    (leftCount b m size queries height : ℕ) where
  encoding : MerkleOracle.Encoding Input Digest (List F)
  domain : Fin (2 ^ height) ↪ F
  root : Factor → Digest
  left : Factor → Fin leftCount → Matrix (Fin b) (Fin b) F
  right : Factor → Fin size → Matrix (Fin b) (Fin b) F
  value : Factor → Fin b → F
  testResponse : Factor → TestMatrix F leftCount b → Response → Fin b → Fin size → F
  structuredResponse : Factor → TestMatrix F leftCount b → Response → Fin b → Fin size → F
  respond : Factor → Memory → TestMatrix F leftCount b → OracleComp (SharedSequence.Shared Cfg Input Digest) Response
  receiveColumns : Factor → Memory → SampleData F Response leftCount b height queries →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (Columns F Digest leftCount b height × Memory)
  choose : Factor → Memory → (sample : SampleData F Response leftCount b height queries) →
    (columns : Columns F Digest leftCount b height) → HashWorkerPool.Workers Input Digest columns.length → Memory →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (Option (Fin columns.length) × Memory)
  fuel : Factor → Memory → SampleData F Response leftCount b height queries → Columns F Digest leftCount b height → ℕ

variable {F Factor Input Digest Cfg Response Memory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {leftCount b m size queries height : ℕ}

/-- The column provider returns columns and private memory only. The native
pool supplies its computed flag after actual whole-column and path hashing. -/
def next (p : Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height)
    (factor : Factor) (incoming : Memory) (sample : SampleData F Response leftCount b height queries) := do
  let received ← p.receiveColumns factor incoming sample
  NativeColumnWorkerPool.program p.encoding (p.root factor)
    (NativeColumnLayout.flattenWeights sample.1.1)
    (NativeColumnLayout.flattenWeights (MatrixResponse.weights (p.left factor)))
    (NativeColumnLayout.flattenResponse
      (MatrixOpeningSecurity.encodeMessages (m := m) p.domain (p.testResponse factor sample.1.1 sample.1.2)))
    (NativeColumnLayout.flattenResponse
      (MatrixOpeningSecurity.encodeMessages (m := m) p.domain (p.structuredResponse factor sample.1.1 sample.1.2)))
    received.1 (p.choose factor incoming sample received.1) (p.fuel factor incoming sample received.1) received.2

def checks (p : Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height)
    (factor : Factor) : JointMatrixOpening.Data F Digest Response leftCount b height queries → Bool :=
  NativeFactorChecks.check (m := m) p.domain (p.left factor) (p.right factor) (p.value factor)
    (p.testResponse factor) (p.structuredResponse factor)

section Step

variable [SampleableType (TestMatrix F leftCount b)] [SampleableType (Fin queries → Fin (2 ^ height))]

/-- Private test, response, private draw, actual interleaved workers, then the
literal final response/value checks. The enclosing loop may stop here. -/
def step (p : Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height)
    (factor : Factor) (memory : Memory) :=
  StoppingJointMatrixOpening.step p.respond (StoppingJointMatrixOpening.checkedNext (checks p) (next p)) factor memory

end Step

variable [SampleableType Digest]

/-- A true column-phase flag yields native replay for every returned column
in every later cache. This is derived from the actual pool computation. -/
theorem next_accepts_later
    (p : Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height)
    (dummy : Digest) (shape : Cfg → Skeleton) (tag : Cfg) (factor : Factor) (incoming : Memory)
    (sample : SampleData F Response leftCount b height queries)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ((Columns F Digest leftCount b height × Memory) × Bool) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) p.encoding dummy shape)
      (next p factor incoming sample)).run before))
    (accepted : outcome.1.2 = true) (later : (Input →ₒ Digest).QueryCache) (extension : outcome.2.hash.cache ≤ later) :
    ∀ column ∈ outcome.1.1.1,
      ParallelColumnAvailability.Replays p.encoding (fun _ : Cfg => height)
        (AuthenticatedColumnChecks.request (fun _ : Cfg => height) tag (p.root factor) column) later := by
  rw [next, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨received, _, poolSupported⟩ := supported
  exact NativeColumnWorkerPool.accepted_columns_later p.encoding dummy (p.root factor) shape _ _ _ _
    received.1.1 (p.choose factor incoming sample received.1.1) (p.fuel factor incoming sample received.1.1)
    received.1.2 received.2 outcome poolSupported accepted later extension

section StepRuntime

variable [SampleableType (TestMatrix F leftCount b)] [SampleableType (Fin queries → Fin (2 ^ height))]

/-- Actual step acceptance supplies the literal factor checks AND native
worker replay. There is no caller-supplied authentication/replay premise. -/
theorem step_accepts_later
    (p : Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height)
    (dummy : Digest) (shape : Cfg → Skeleton) (tag : Cfg) (factor : Factor) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ShortCircuitSequence.StepResult (JointMatrixOpening.Data F Digest Response leftCount b height queries) Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) p.encoding dummy shape)
      (step p factor memory)).run before)) (accepted : outcome.1.accepted = true)
    (laterCache : (Input →ₒ Digest).QueryCache) (extension : outcome.2.hash.cache ≤ laterCache) :
    checks p factor outcome.1.result = true ∧
    ∀ column ∈ outcome.1.result.2,
      ParallelColumnAvailability.Replays p.encoding (fun _ : Cfg => height)
        (AuthenticatedColumnChecks.request (fun _ : Cfg => height) tag (p.root factor) column) laterCache := by
  rw [step, StoppingJointMatrixOpening.checked_step_eq, ShortCircuitSequence.enforce,
    simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨raw, rawSupported, equal⟩ := supported
  subst outcome
  obtain ⟨workerAccepted, checked⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨earlier, _, later, laterSupported, rawEqual⟩ :=
    StoppingJointMatrixOpening.step_supported p.encoding dummy shape p.respond (next p) factor memory before raw rawSupported
  subst raw
  exact ⟨checked, next_accepts_later p dummy shape tag factor memory earlier.1 earlier.2 later
    laterSupported workerAccepted laterCache extension⟩

/-- Successful factor loops carry every earlier worker's authentication and
literal checks to the final cache, despite all subsequent shared work. -/
theorem successful_results
    (p : Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height)
    (dummy : Digest) (shape : Cfg → Skeleton) (tag : Factor → Cfg) (factors : List Factor) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ShortCircuitSequence.Outcome Factor (JointMatrixOpening.Data F Digest Response leftCount b height queries) Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) p.encoding dummy shape)
      (ShortCircuitSequence.program (step p) factors memory)).run before)) (accepted : outcome.1.accepted = true) :
    ∀ entry ∈ outcome.1.results, checks p entry.1 entry.2 = true ∧
      ∀ column ∈ entry.2.2,
        ParallelColumnAvailability.Replays p.encoding (fun _ : Cfg => height)
          (AuthenticatedColumnChecks.request (fun _ : Cfg => height) (tag entry.1) (p.root entry.1) column)
          outcome.2.hash.cache :=
  ShortCircuitSequence.accepted_cache_results p.encoding dummy shape (step p) factors
    (fun factor data cache => checks p factor data = true ∧ ∀ column ∈ data.2,
      ParallelColumnAvailability.Replays p.encoding (fun _ : Cfg => height)
        (AuthenticatedColumnChecks.request (fun _ : Cfg => height) (tag factor) (p.root factor) column) cache)
    (fun factor _ incoming initial result present passed cache extension =>
      step_accepts_later p dummy shape (tag factor) factor incoming initial result present passed cache extension)
    memory before outcome supported accepted

/-- A successful concrete native loop that supplies an incorrect value is in
the joint PCS bad-opening event. Native replay and coordinate checks are
consequences of execution, not hypotheses of this reduction. -/
theorem successful_wrong_evaluation
    (p : Protocol F Factor Input Digest Cfg Response Memory leftCount b m size queries height)
    (dummy : Digest) (tag : Factor → Cfg)
    (checkpoint : ∀ factor, Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun _ : Cfg => Skeleton.perfect height)) (tag factor))
    (roots : ∀ factor, (checkpoint factor).root = p.root factor)
    (capacity : size ≤ m * b) (radius : ℕ) (factors : List Factor) (complete : ∀ factor, factor ∈ factors)
    (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (outcome : ShortCircuitSequence.Outcome Factor (JointMatrixOpening.Data F Digest Response leftCount b height queries) Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) p.encoding dummy (fun _ : Cfg => Skeleton.perfect height))
      (ShortCircuitSequence.program (step p) factors memory)).run before)) (accepted : outcome.1.accepted = true)
    (different : ∃ factor, p.value factor ≠ matrixEvaluation (p.left factor) (p.right factor)
      (MatrixOpeningSecurity.extract p.domain capacity radius (JointMatrixOpening.frozen p.encoding dummy tag checkpoint factor))) :
    JointMatrixOpening.AnyAcceptedWrong p.encoding dummy tag checkpoint p.domain capacity radius p.left p.right
      p.testResponse p.structuredResponse ((outcome.1.results, outcome.1.memory), outcome.2) := by
  have checked := successful_results p dummy (fun _ : Cfg => Skeleton.perfect height) tag factors memory before
    outcome supported accepted
  have coverage := ShortCircuitSequence.accepted_indices p.encoding dummy (fun _ : Cfg => Skeleton.perfect height)
    (step p) factors memory before outcome supported accepted
  obtain ⟨factor, wrong⟩ := different
  have occurs : factor ∈ outcome.1.results.map Prod.fst := by rw [coverage]; exact complete factor
  obtain ⟨entry, member, equal⟩ := List.mem_map.mp occurs
  subst factor
  obtain ⟨covered, coordinates, finished⟩ :=
    (NativeFactorChecks.check_iff p.domain (p.left entry.1) (p.right entry.1) (p.value entry.1)
      (p.testResponse entry.1) (p.structuredResponse entry.1) entry.2).mp (checked entry member).1
  refine ⟨entry, member, ?_, covered, ?_, coordinates⟩
  · rw [finished]
    exact wrong
  · simpa only [roots entry.1] using (checked entry member).2

end StepRuntime

end

end FormalProof4FHE.HasteBoots.NativeMatrixVerifier
