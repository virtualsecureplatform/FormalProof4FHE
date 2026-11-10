module
public import FormalProof4FHE.HasteBoots.StagedCommitmentPrefix
@[expose] public section

/-! Source/helper recording times and terminal history failure share one
whole-program hash charge, including adaptive work between the two prefixes. -/
namespace FormalProof4FHE.HasteBoots.StagedCommitmentException
open OracleSpec OracleComp BinaryTree StagedCommitmentPrefix
noncomputable section
variable {Cfg Input Digest Payload First Second Result : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

theorem audited_witness (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sourceRequests : First → List (Cfg × Digest)) (helperRequests : First → Second → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (helperCommit : First → OracleComp (SharedSequence.Shared Cfg Input Digest) Second)
    (next : First → Second → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (outcome : (First × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
      (Second × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
      (Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape))
    (supported : outcome ∈ support (witness enc dummy shape sourceRequests helperRequests sourceCommit helperCommit next
      (CheckpointExecution.empty shape))) : CheckpointExecution.Audited enc dummy shape outcome.2.2.2 := by
  have projected : ((outcome.1.1,outcome.2.1.1,outcome.2.2.1),outcome.2.2.2) ∈ support
      ((fun item => ((item.1.1,item.2.1.1,item.2.2.1),item.2.2.2)) <$>
        witness enc dummy shape sourceRequests helperRequests sourceCommit helperCommit next (CheckpointExecution.empty shape)) := by
    rw [support_map]
    exact Set.mem_image_of_mem _ supported
  rw [project_witness] at projected
  have initial := CheckpointExecution.good_empty enc dummy shape
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape
    (program sourceRequests helperRequests sourceCommit helperCommit next) _ ⟨initial.1,fun _ => initial.2.2⟩ _ projected

variable [Fintype Digest]

theorem event_bound_or_bad (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
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
      (CheckpointExecution.empty shape))}[accepted outcome.1 outcome.2.1 outcome.2.2 ∨ CheckpointCollision.Bad shape outcome.2.2.2] ≤ epsilon +
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
  have authentication := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp)
    enc dummy shape (program sourceRequests helperRequests sourceCommit helperCommit next)
  rw [← project_witness enc dummy shape sourceRequests helperRequests sourceCommit helperCommit next (CheckpointExecution.empty shape),
    prEvent_map] at authentication
  apply le_trans (prEvent_mono_of_support _ _ (fun outcome =>
    arithmetic outcome.1 outcome.2.1 outcome.2.2 ∨ CheckpointCollision.Bad shape outcome.2.2.2) ?_)
  · exact (prEvent_or_le _ _ _).trans (add_le_add averaged authentication)
  · intro outcome supported event
    rcases event with acceptedOutcome | bad
    · have audited := audited_witness enc dummy shape sourceRequests helperRequests sourceCommit helperCommit next outcome supported
      simp only [witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
      obtain ⟨first,firstSupported,second,secondSupported,last,lastSupported,equal⟩ := supported
      subst outcome
      rcases reduction first firstSupported second secondSupported last lastSupported acceptedOutcome with arithmetic | disagreement
      · exact Or.inl arithmetic
      · exact Or.inr (CheckpointAvailability.disagreement_implies_bad enc dummy shape last.2 audited disagreement)
    · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.StagedCommitmentException
