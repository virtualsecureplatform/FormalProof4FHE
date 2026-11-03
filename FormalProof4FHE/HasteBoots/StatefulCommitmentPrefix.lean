module

public import FormalProof4FHE.HasteBoots.CommitmentPrefix

@[expose] public section

/-!
# Commitment prefixes retaining private prover state

The commitment emits a root together with arbitrary private memory. Only the
root enters the checkpoint query. The continuation receives that same memory,
including its correlation with private commitment coins and the shared cache.
Analysis retains the real prefix state and erases exactly to the operational
program. Arithmetic averaging and a single whole-run availability charge need
no safety certificate or finite private-memory space.
-/

open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.StatefulCommitmentPrefix

noncomputable section

variable {Cfg Input Digest Payload Result Memory : Type} [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

abbrev Shared (base : OracleSpec ι) (Cfg Input Digest : Type) :=
  CheckpointExecution.Spec base Cfg Input Digest

/-- The commitment may make arbitrary shared calls. Recording is a passive
annotation between the emitted root and the following verifier coins. -/
def program (tag : Cfg) (commit : OracleComp (Shared base Cfg Input Digest) (Digest × Memory))
    (next : (Digest × Memory) → OracleComp (Shared base Cfg Input Digest) Result) :
    OracleComp (Shared base Cfg Input Digest) ((Digest × Memory) × Result) := do
  let emission ← commit
  let _ ← (Shared base Cfg Input Digest).query (.inr (.inr (tag, emission.1)))
  let result ← next emission
  pure (emission, result)

def snapshot (shape : Cfg → Skeleton) (tag : Cfg)
    (first : (Digest × Memory) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) tag :=
  ⟨first.1.1, first.2.hash.log⟩

omit [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest] in
/-- The newly frozen source is recorded even if the prefix already failed. -/
theorem snapshot_recorded (shape : Cfg → Skeleton) (tag : Cfg)
    (first : (Digest × Memory) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    ⟨tag, snapshot shape tag first⟩ ∈
      (CheckpointExecution.record shape first.2 tag first.1.1).checkpoints.checkpoints := by
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Analysis-only retention of the commitment's actual final hash state. -/
def witness (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (tag : Cfg) (commit : OracleComp (Shared base Cfg Input Digest) (Digest × Memory))
    (next : (Digest × Memory) → OracleComp (Shared base Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) := do
  let first ← (simulateQ (CheckpointExecution.handler implBase enc dummy shape) commit).run initial
  let last ← (simulateQ (CheckpointExecution.handler implBase enc dummy shape) (next first.1)).run
    (CheckpointExecution.record shape first.2 tag first.1.1)
  pure (first, last)

/-- Erasing the analysis snapshot recovers the exact actual execution. -/
theorem project_witness (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (tag : Cfg) (commit : OracleComp (Shared base Cfg Input Digest) (Digest × Memory))
    (next : (Digest × Memory) → OracleComp (Shared base Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (fun outcome => ((outcome.1.1, outcome.2.1), outcome.2.2)) <$>
      witness implBase enc dummy shape tag commit next initial =
    (simulateQ (CheckpointExecution.handler implBase enc dummy shape) (program tag commit next)).run initial := by
  simp only [witness, program, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, simulateQ_spec_query, map_bind, map_pure]
  rfl

variable [Fintype Digest]

/-- A uniform conditional arithmetic bound is averaged over all adaptive
prefixes; authentication is charged once on the whole actual execution.
The two local hypotheses are the interfaces instantiated by the matrix theorem,
not security assumptions about the hash or a commitment primitive. -/
theorem event_bound (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (tag : Cfg) (commit : OracleComp (Shared base Cfg Input Digest) (Digest × Memory))
    (next : (Digest × Memory) → OracleComp (Shared base Cfg Input Digest) Result)
    (accepted arithmetic :
      ((Digest × Memory) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) →
      (Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) → Prop)
    (epsilon : ENNReal)
    (arithmetic_bound : ∀ first,
      Pr{let last ← ((simulateQ (CheckpointExecution.handler implBase enc dummy shape) (next first.1)).run
        (CheckpointExecution.record shape first.2 tag first.1.1))}[arithmetic first last] ≤ epsilon)
    (reduction : ∀ first last,
      last ∈ support ((simulateQ (CheckpointExecution.handler implBase enc dummy shape) (next first.1)).run
        (CheckpointExecution.record shape first.2 tag first.1.1)) →
      accepted first last → arithmetic first last ∨ CheckpointAvailability.Disagreement enc dummy shape last.2) :
    Pr{let outcome ← witness implBase enc dummy shape tag commit next (CheckpointExecution.empty shape)}[
      accepted outcome.1 outcome.2] ≤ epsilon +
      ExpectedHazard.charge (CheckpointExecution.handler implBase enc dummy shape)
        (CheckpointCollision.loss base shape) (program tag commit next) (CheckpointExecution.empty shape) := by
  have arithmetic_average :
      Pr{let outcome ← witness implBase enc dummy shape tag commit next (CheckpointExecution.empty shape)}[
        arithmetic outcome.1 outcome.2] ≤ epsilon := by
    unfold witness
    apply prEvent_bind_le_of_forall_le
    intro first
    simpa only [prEvent_norm] using arithmetic_bound first
  have authentication := CheckpointAvailability.disagreement_from_empty_le_charge implBase enc dummy shape
    (program tag commit next)
  rw [← project_witness implBase enc dummy shape tag commit next (CheckpointExecution.empty shape),
    prEvent_map] at authentication
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    arithmetic outcome.1 outcome.2 ∨ CheckpointAvailability.Disagreement enc dummy shape outcome.2.2) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add arithmetic_average authentication)
  · intro outcome supported acceptedOutcome
    simp only [witness, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at supported
    obtain ⟨first, _, last, reached, equal⟩ := supported
    subst outcome
    exact reduction first last reached acceptedOutcome

end

end FormalProof4FHE.HasteBoots.StatefulCommitmentPrefix
