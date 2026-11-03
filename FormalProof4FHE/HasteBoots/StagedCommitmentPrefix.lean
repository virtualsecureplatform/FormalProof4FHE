module

public import FormalProof4FHE.HasteBoots.SharedSequence
public import FormalProof4FHE.HasteBoots.MultiCommitmentPrefix
public import FormalProof4FHE.HasteBoots.CheckpointHistory

@[expose] public section

/-!
# Two real recording times and one complete-run availability charge

Source roots are recorded before the adaptive middle program; helper roots
are recorded after it. The middle program may include pair challenges,
rejection sampling and helper commitment work. Analysis retains both actual
states without moving either snapshot. Erasure recovers the real program.
-/

open OracleSpec OracleComp BinaryTree

namespace FormalProof4FHE.HasteBoots.StagedCommitmentPrefix

noncomputable section

variable {Cfg Input Digest Payload First Second Result : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

def program (sourceRequests : First → List (Cfg × Digest)) (helperRequests : First → Second → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (helperCommit : First → OracleComp (SharedSequence.Shared Cfg Input Digest) Second)
    (next : First → Second → OracleComp (SharedSequence.Shared Cfg Input Digest) Result) := do
  let first ← sourceCommit
  let _ ← RecordRoots.program (sourceRequests first)
  let second ← helperCommit first
  let _ ← RecordRoots.program (helperRequests first second)
  let result ← next first second
  pure (first, second, result)

def witness (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sourceRequests : First → List (Cfg × Digest)) (helperRequests : First → Second → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (helperCommit : First → OracleComp (SharedSequence.Shared Cfg Input Digest) Second)
    (next : First → Second → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) := do
  let first ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) sourceCommit).run initial
  let second ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (helperCommit first.1)).run
    (RecordRoots.state shape (sourceRequests first.1) first.2)
  let last ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (next first.1 second.1)).run
    (RecordRoots.state shape (helperRequests first.1 second.1) second.2)
  pure (first, second, last)

/-- Both proof-only states erase, retaining the exact actual final shared state. -/
theorem project_witness (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sourceRequests : First → List (Cfg × Digest)) (helperRequests : First → Second → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (helperCommit : First → OracleComp (SharedSequence.Shared Cfg Input Digest) Second)
    (next : First → Second → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (fun outcome => ((outcome.1.1, outcome.2.1.1, outcome.2.2.1), outcome.2.2.2)) <$>
      witness enc dummy shape sourceRequests helperRequests sourceCommit helperCommit next initial =
      (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (program sourceRequests helperRequests sourceCommit helperCommit next)).run initial := by
  simp only [witness, program, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, RecordRoots.run_program, map_bind, map_pure, pure_bind]

variable [Fintype Digest]

/-- The arithmetic bound is averaged over the actual two adaptive prefixes.
Every availability failure is charged once on their whole real execution. -/
theorem event_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sourceRequests : First → List (Cfg × Digest)) (helperRequests : First → Second → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (helperCommit : First → OracleComp (SharedSequence.Shared Cfg Input Digest) Second)
    (next : First → Second → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (accepted arithmetic :
      (First × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) →
      (Second × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) →
      (Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) → Prop)
    (epsilon : ENNReal)
    (arithmetic_bound : ∀ first second,
      Pr{let last ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (next first.1 second.1)).run (RecordRoots.state shape (helperRequests first.1 second.1) second.2)}[
          arithmetic first second last] ≤ epsilon)
    (reduction : ∀ first,
      first ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        sourceCommit).run (CheckpointExecution.empty shape)) → ∀ second,
      second ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (helperCommit first.1)).run (RecordRoots.state shape (sourceRequests first.1) first.2)) → ∀ last,
      last ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (next first.1 second.1)).run (RecordRoots.state shape (helperRequests first.1 second.1) second.2)) →
      accepted first second last → arithmetic first second last ∨ CheckpointAvailability.Disagreement enc dummy shape last.2) :
    Pr{let outcome ← (witness enc dummy shape sourceRequests helperRequests sourceCommit helperCommit next
      (CheckpointExecution.empty shape))}[accepted outcome.1 outcome.2.1 outcome.2.2] ≤ epsilon +
      ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (CheckpointCollision.loss unifSpec shape)
        (program sourceRequests helperRequests sourceCommit helperCommit next) (CheckpointExecution.empty shape) := by
  have averaged : Pr{let outcome ← (witness enc dummy shape sourceRequests helperRequests sourceCommit helperCommit next
      (CheckpointExecution.empty shape))}[arithmetic outcome.1 outcome.2.1 outcome.2.2] ≤ epsilon := by
    unfold witness
    apply prEvent_bind_le_of_forall_le
    intro first
    apply prEvent_bind_le_of_forall_le
    intro second
    simpa only [prEvent_norm] using arithmetic_bound first second
  have authentication := CheckpointAvailability.disagreement_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp)
    enc dummy shape (program sourceRequests helperRequests sourceCommit helperCommit next)
  rw [← project_witness enc dummy shape sourceRequests helperRequests sourceCommit helperCommit next (CheckpointExecution.empty shape),
    prEvent_map] at authentication
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    arithmetic outcome.1 outcome.2.1 outcome.2.2 ∨ CheckpointAvailability.Disagreement enc dummy shape outcome.2.2.2) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add averaged authentication)
  · intro outcome supported acceptedOutcome
    simp only [witness, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at supported
    obtain ⟨first, firstSupported, second, secondSupported, last, lastSupported, equal⟩ := supported
    subst outcome
    exact reduction first firstSupported second secondSupported last lastSupported acceptedOutcome

end

end FormalProof4FHE.HasteBoots.StagedCommitmentPrefix
