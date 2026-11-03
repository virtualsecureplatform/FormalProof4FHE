module

public import FormalProof4FHE.HasteBoots.InteractiveSampling

@[expose] public section

/-!
# Retaining an earlier outcome through arbitrary shared-oracle work

The later program runs on the exact state left by the earlier one. Its hashes,
private draws and checkpoints stay in the complete execution and charge, while
an event already fixed by the earlier outcome cannot gain probability.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.SharedContinuation

noncomputable section

variable {Cfg Input Digest Payload Earlier Later : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

def program (before : OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Earlier)
    (next : Earlier → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Earlier × Later) := do
  let earlier ← before
  let later ← next earlier
  pure (earlier, later)

theorem earlier_event_le (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (before : OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Earlier)
    (next : Earlier → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (event : Earlier → Prop) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program before next)).run state}[event outcome.1.1] ≤
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      before).run state}[event outcome.1] := by
  have bound := AdaptiveResponse.event_le
    ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) before).run state)
    (fun earlier => (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (next earlier.1)).run earlier.2)
    (fun earlier => event earlier.1)
  simpa only [program, AdaptiveResponse.choose, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, simulateQ_map, StateT.run_map, prEvent_norm] using bound

/-- A uniform conditional bound averages over arbitrary earlier shared work,
with the actual state passed to the continuation. No independence is needed. -/
theorem later_event_le (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (before : OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Earlier)
    (next : Earlier → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (event : Earlier → Later × CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop)
    (epsilon : ENNReal)
    (bound : ∀ earlier initial,
      Pr{let outcome ← (simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (next earlier)).run initial}[event earlier outcome] ≤ epsilon) :
    Pr{let outcome ← (simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program before next)).run state}[event outcome.1.1 (outcome.1.2, outcome.2)] ≤ epsilon := by
  simp only [program, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
  apply prEvent_bind_le_of_forall_le
  intro earlier
  simpa only [prEvent_norm] using bound earlier.1 earlier.2

/-- Supported executions expose the real intermediate state, including all
earlier hash calls, for checkpoint-preservation arguments. -/
theorem support_program (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (before : OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Earlier)
    (next : Earlier → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : (Earlier × Later) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program before next)).run state) ↔
    ∃ earlier ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) before).run state),
      ∃ later ∈ support ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (next earlier.1)).run earlier.2), outcome = ((earlier.1, later.1), later.2) := by
  simp only [program, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
  constructor
  · rintro ⟨earlier, reached, later, supported, equal⟩
    exact ⟨earlier, reached, later, supported, equal⟩
  · rintro ⟨earlier, reached, later, supported, equal⟩
    exact ⟨earlier, reached, later, supported, equal⟩

end

end FormalProof4FHE.HasteBoots.SharedContinuation
