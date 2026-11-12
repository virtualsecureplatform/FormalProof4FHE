module
public import FormalProof4FHE.HasteBoots.SequentialStageHistory
public import FormalProof4FHE.HasteBoots.CheckpointAvailability
@[expose] public section

/-! Conditional committed-stage bounds from arbitrary audited incoming states.
The terminal shared collision event is excluded here and charged once by the
whole caller. No child-from-empty restart or second hash charge is introduced. -/
namespace FormalProof4FHE.HasteBoots.CommittedPrefixSafeBound
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {Cfg Input Digest Payload Emission Result : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

theorem event_bound
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (requests : Emission → List (Cfg × Digest))
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (next : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (audited : CheckpointExecution.Audited enc dummy shape initial)
    (accepted arithmetic :
      (Emission × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) →
      (Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) → Prop)
    (epsilon : ENNReal)
    (arithmetic_bound : ∀ first,
      Pr{let last ← ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (next first.1)).run (RecordRoots.state shape (requests first.1) first.2))}[arithmetic first last] ≤ epsilon)
    (reduction : ∀ first last,
      last ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (next first.1)).run (RecordRoots.state shape (requests first.1) first.2)) →
      accepted first last → arithmetic first last ∨ CheckpointAvailability.Disagreement enc dummy shape last.2) :
    Pr{let outcome ← (MultiCommitmentPrefix.witness enc dummy shape requests commit next initial)}[
      accepted outcome.1 outcome.2 ∧ ¬CheckpointCollision.Bad shape outcome.2.2] ≤ epsilon := by
  have average : Pr{let outcome ← (MultiCommitmentPrefix.witness enc dummy shape requests commit next initial)}[
      arithmetic outcome.1 outcome.2] ≤ epsilon := by
    unfold MultiCommitmentPrefix.witness
    apply prEvent_bind_le_of_forall_le
    intro first
    simpa only [prEvent_norm] using arithmetic_bound first
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome => arithmetic outcome.1 outcome.2) ?_) average
  intro outcome supported event
  have projected : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (MultiCommitmentPrefix.program requests commit next)).run initial) := by
    rw [←MultiCommitmentPrefix.project_witness enc dummy shape requests commit next initial,support_map]
    exact Set.mem_image_of_mem _ supported
  have finalAudit := CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape
    (MultiCommitmentPrefix.program requests commit next) initial audited _ projected
  simp only [MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,_,last,reached,equal⟩ := supported
  subst outcome
  rcases reduction first last reached event.1 with badArithmetic | disagreement
  · exact badArithmetic
  · exact False.elim (event.2 (CheckpointAvailability.disagreement_implies_bad enc dummy shape last.2 finalAudit disagreement))

end
end FormalProof4FHE.HasteBoots.CommittedPrefixSafeBound
