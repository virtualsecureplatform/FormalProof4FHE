module

public import FormalProof4FHE.HasteBoots.RecordRoots
public import FormalProof4FHE.HasteBoots.CheckpointAvailability

@[expose] public section

/-!
# Joint commitment prefixes for a family of roots

One arbitrary commitment computation emits public roots and retained private
memory. A deterministic request function selects the trusted root/configuration
pairs to annotate before query selection. Root recording preserves the actual
hash log. Analysis retains that prefix log but projects exactly to the original
annotated program. One whole-run availability charge suffices for the family.
-/

open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.MultiCommitmentPrefix

noncomputable section

variable {Cfg Input Digest Payload Result Emission : Type} [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest]

abbrev Shared (Cfg Input Digest : Type) :=
  CheckpointExecution.Spec unifSpec Cfg Input Digest

/-- The commitment may make arbitrary shared calls. Recording is a passive
annotation between the emitted root and the following verifier coins. -/
def program (requests : Emission → List (Cfg × Digest)) (commit : OracleComp (Shared Cfg Input Digest) Emission)
    (next : Emission → OracleComp (Shared Cfg Input Digest) Result) :
    OracleComp (Shared Cfg Input Digest) (Emission × Result) := do
  let emission ← commit
  let _ ← RecordRoots.program (requests emission)
  let result ← next emission
  pure (emission, result)

/-- Analysis-only retention of the commitment's actual final hash state. -/
def witness
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (requests : Emission → List (Cfg × Digest)) (commit : OracleComp (Shared Cfg Input Digest) Emission)
    (next : Emission → OracleComp (Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) := do
  let first ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) commit).run initial
  let last ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (next first.1)).run
    (RecordRoots.state shape (requests first.1) first.2)
  pure (first, last)

/-- Erasing the analysis snapshot recovers the exact actual execution. -/
theorem project_witness
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (requests : Emission → List (Cfg × Digest)) (commit : OracleComp (Shared Cfg Input Digest) Emission)
    (next : Emission → OracleComp (Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (fun outcome => ((outcome.1.1, outcome.2.1), outcome.2.2)) <$>
      witness enc dummy shape requests commit next initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (program requests commit next)).run initial := by
  simp only [witness, program, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, RecordRoots.run_program, map_bind, map_pure, pure_bind]

variable [Fintype Digest]

/-- A uniform conditional arithmetic bound is averaged over all adaptive
prefixes; authentication is charged once on the whole actual execution.
The two local hypotheses are the interfaces instantiated by the matrix theorem,
not security assumptions about the hash or a commitment primitive. -/
theorem event_bound
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (requests : Emission → List (Cfg × Digest)) (commit : OracleComp (Shared Cfg Input Digest) Emission)
    (next : Emission → OracleComp (Shared Cfg Input Digest) Result)
    (accepted arithmetic :
      (Emission × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) →
      (Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) → Prop)
    (epsilon : ENNReal)
    (arithmetic_bound : ∀ first,
      Pr{let last ← ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (next first.1)).run
        (RecordRoots.state shape (requests first.1) first.2))}[arithmetic first last] ≤ epsilon)
    (reduction : ∀ first last,
      last ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) (next first.1)).run
        (RecordRoots.state shape (requests first.1) first.2)) →
      accepted first last → arithmetic first last ∨ CheckpointAvailability.Disagreement enc dummy shape last.2) :
    Pr{let outcome ← witness enc dummy shape requests commit next (CheckpointExecution.empty shape)}[
      accepted outcome.1 outcome.2] ≤ epsilon +
      ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (CheckpointCollision.loss unifSpec shape) (program requests commit next) (CheckpointExecution.empty shape) := by
  have arithmetic_average :
      Pr{let outcome ← witness enc dummy shape requests commit next (CheckpointExecution.empty shape)}[
        arithmetic outcome.1 outcome.2] ≤ epsilon := by
    unfold witness
    apply prEvent_bind_le_of_forall_le
    intro first
    simpa only [prEvent_norm] using arithmetic_bound first
  have authentication := CheckpointAvailability.disagreement_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape
    (program requests commit next)
  rw [← project_witness enc dummy shape requests commit next (CheckpointExecution.empty shape),
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

end FormalProof4FHE.HasteBoots.MultiCommitmentPrefix
