module

public import FormalProof4FHE.HasteBoots.RectangularBatchChecks
public import FormalProof4FHE.HasteBoots.ShortCircuitSequence
public import FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

@[expose] public section

/-!
# Arithmetic for factor openings with actual early rejection

The native column phase returns its result, retained private memory and
verification flag. The factor loop uses that flag to stop before any later
factor's coins or hash calls. The arithmetic bound applies to attempted
openings, including a rejected attempt, on this same actual execution.
Authentication and native worker-flag linkage remain separate interfaces.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.RectangularStoppingOpening

noncomputable section

variable {F Factor Cfg Input Digest Response Memory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {front b block queries height : ℕ}

/-- Private memory returned by the column phase is carried into the next
factor. Projecting it out does not delete any actual oracle calls. -/
def step [SampleableType (TestMatrix F (2^front) b)]
    [SampleableType (Fin queries → Fin (2 ^ height))]
    (respond : Factor → Memory → TestMatrix F (2^front) b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : Factor → Memory → SampleData F Response (2^front) b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) ((RectangularBatchChecks.Columns F Digest front b block height × Memory) × Bool))
    (factor : Factor) (memory : Memory) :
    OracleComp (SharedSequence.Shared Cfg Input Digest)
      (ShortCircuitSequence.StepResult (RectangularBatchChecks.Data F Digest Response front b block height queries) Memory) :=
  (fun outcome => (⟨(outcome.1, outcome.2.1.1), outcome.2.1.2, outcome.2.2⟩ :
    ShortCircuitSequence.StepResult (RectangularBatchChecks.Data F Digest Response front b block height queries) Memory)) <$>
    InteractiveSampling.complete ($ᵗ (TestMatrix F (2^front) b)) (respond factor memory)
      ($ᵗ (Fin queries → Fin (2 ^ height))) (next factor memory)

/-- Enforce the deterministic native response/value checks after the worker
phase, without issuing any additional oracle queries. -/
def checkedNext
    (check : Factor → RectangularBatchChecks.Data F Digest Response front b block height queries → Bool)
    (next : Factor → Memory → SampleData F Response (2^front) b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) ((RectangularBatchChecks.Columns F Digest front b block height × Memory) × Bool))
    (factor : Factor) (memory : Memory) (sample : SampleData F Response (2^front) b height queries) :=
  (fun result => (result.1, result.2 && check factor (sample, result.1.1))) <$> next factor memory sample

omit [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] in
/-- Checking native response data is exactly enforcement at the step boundary;
the equality preserves the oracle program, including all worker calls. -/
theorem checked_step_eq [SampleableType (TestMatrix F (2^front) b)]
    [SampleableType (Fin queries → Fin (2 ^ height))]
    (check : Factor → RectangularBatchChecks.Data F Digest Response front b block height queries → Bool)
    (respond : Factor → Memory → TestMatrix F (2^front) b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : Factor → Memory → SampleData F Response (2^front) b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) ((RectangularBatchChecks.Columns F Digest front b block height × Memory) × Bool))
    (factor : Factor) (memory : Memory) :
    step respond (checkedNext check next) factor memory =
      ShortCircuitSequence.enforce check (step respond next) factor memory := by
  simp only [step, checkedNext, ShortCircuitSequence.enforce, InteractiveSampling.complete,
    map_bind, map_pure, bind_map_left]

omit [Field F] [DecidableEq F] in
/-- Expose the real sampled prefix and native column-phase execution of a
supported step. The returned flag is the actual column-phase flag. -/
theorem step_supported [SampleableType (TestMatrix F (2^front) b)]
    [SampleableType (Fin queries → Fin (2 ^ height))]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (shape : Cfg → Skeleton)
    (respond : Factor → Memory → TestMatrix F (2^front) b →
      OracleComp (SharedSequence.Shared Cfg Input Digest) Response)
    (next : Factor → Memory → SampleData F Response (2^front) b height queries →
      OracleComp (SharedSequence.Shared Cfg Input Digest) ((RectangularBatchChecks.Columns F Digest front b block height × Memory) × Bool))
    (factor : Factor) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ShortCircuitSequence.StepResult (RectangularBatchChecks.Data F Digest Response front b block height queries) Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (step respond next factor memory)).run before)) :
    ∃ earlier ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (InteractiveSampling.program ($ᵗ (TestMatrix F (2^front) b)) (respond factor memory)
          ($ᵗ (Fin queries → Fin (2 ^ height))))).run before),
      ∃ later ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (next factor memory earlier.1)).run earlier.2),
        outcome = (⟨(earlier.1, later.1.1.1), later.1.1.2, later.1.2⟩, later.2) := by
  rw [step, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨packet, packetSupported, equal⟩ := supported
  have parts := (SharedContinuation.support_program enc dummy shape
    (InteractiveSampling.program ($ᵗ (TestMatrix F (2^front) b)) (respond factor memory)
      ($ᵗ (Fin queries → Fin (2 ^ height)))) (next factor memory) before packet).mp packetSupported
  obtain ⟨earlier, earlierSupported, later, laterSupported, packetEqual⟩ := parts
  subst packet
  exact ⟨earlier, earlierSupported, later, laterSupported, equal.symm⟩

end
end FormalProof4FHE.HasteBoots.RectangularStoppingOpening
