module
public import FormalProof4FHE.HasteBoots.MultiCommitmentPrefix
@[expose] public section

/-! Joint arithmetic and common hash/source exceptions. Including the terminal
bad event in the acceptance event pays the whole-run charge only once. -/
namespace FormalProof4FHE.HasteBoots.CommitmentExceptionUnion
open OracleSpec OracleComp BinaryTree
open MultiCommitmentPrefix
noncomputable section
variable {Cfg Input Digest Payload Result Emission : Type} [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest]

theorem audited_witness (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (requests : Emission → List (Cfg × Digest)) (commit : OracleComp (Shared Cfg Input Digest) Emission)
    (next : Emission → OracleComp (Shared Cfg Input Digest) Result)
    (outcome : (Emission × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
      (Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape))
    (supported : outcome ∈ support (witness enc dummy shape requests commit next (CheckpointExecution.empty shape))) :
    CheckpointExecution.Audited enc dummy shape outcome.2.2 := by
  have projected : ((outcome.1.1,outcome.2.1),outcome.2.2) ∈ support
      ((fun item => ((item.1.1,item.2.1),item.2.2)) <$> witness enc dummy shape requests commit next (CheckpointExecution.empty shape)) := by
    rw [support_map]
    exact Set.mem_image_of_mem _ supported
  rw [project_witness] at projected
  have initial := CheckpointExecution.good_empty enc dummy shape
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape (program requests commit next) _
    ⟨initial.1,fun _ => initial.2.2⟩ _ projected

variable [Fintype Digest]

theorem event_bound_or_bad
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
      accepted outcome.1 outcome.2 ∨ CheckpointCollision.Bad shape outcome.2.2] ≤ epsilon +
      ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (CheckpointCollision.loss unifSpec shape) (program requests commit next) (CheckpointExecution.empty shape) := by
  have arithmetic_average :
      Pr{let outcome ← witness enc dummy shape requests commit next (CheckpointExecution.empty shape)}[
        arithmetic outcome.1 outcome.2] ≤ epsilon := by
    unfold witness
    apply prEvent_bind_le_of_forall_le
    intro first
    simpa only [prEvent_norm] using arithmetic_bound first
  have authentication := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape
    (program requests commit next)
  rw [← project_witness enc dummy shape requests commit next (CheckpointExecution.empty shape),
    prEvent_map] at authentication
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    arithmetic outcome.1 outcome.2 ∨ CheckpointCollision.Bad shape outcome.2.2) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add arithmetic_average authentication)
  · intro outcome supported event
    rcases event with acceptedOutcome | bad
    · have audited := audited_witness enc dummy shape requests commit next outcome supported
      simp only [witness, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at supported
      obtain ⟨first, _, last, reached, equal⟩ := supported
      subst outcome
      rcases reduction first last reached acceptedOutcome with arithmetic | disagreement
      · exact Or.inl arithmetic
      · exact Or.inr (CheckpointAvailability.disagreement_implies_bad enc dummy shape last.2 audited disagreement)
    · exact Or.inr bad


end
end FormalProof4FHE.HasteBoots.CommitmentExceptionUnion
