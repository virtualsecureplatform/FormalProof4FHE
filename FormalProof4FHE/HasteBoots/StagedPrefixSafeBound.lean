module
public import FormalProof4FHE.HasteBoots.StagedCommitmentPrefix
public import FormalProof4FHE.HasteBoots.CheckpointAvailability
@[expose] public section

/-! Two real source/helper recording times from an arbitrary audited incoming
state, with collision charging left to the enclosing program. -/
namespace FormalProof4FHE.HasteBoots.StagedPrefixSafeBound
open OracleSpec OracleComp BinaryTree StagedCommitmentPrefix
noncomputable section
variable {Cfg Input Digest Payload First Second Result : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

theorem audited_witness (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sourceRequests : First → List (Cfg × Digest)) (helperRequests : First → Second → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (helperCommit : First → OracleComp (SharedSequence.Shared Cfg Input Digest) Second)
    (next : First → Second → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (audited : CheckpointExecution.Audited enc dummy shape initial)
    (outcome : (First × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
      (Second × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
      (Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape))
    (supported : outcome ∈ support (witness enc dummy shape sourceRequests helperRequests sourceCommit helperCommit next
      initial)) : CheckpointExecution.Audited enc dummy shape outcome.2.2.2 := by
  have projected : ((outcome.1.1,outcome.2.1.1,outcome.2.2.1),outcome.2.2.2) ∈ support
      ((fun item => ((item.1.1,item.2.1.1,item.2.2.1),item.2.2.2)) <$>
        witness enc dummy shape sourceRequests helperRequests sourceCommit helperCommit next initial) := by
    rw [support_map]
    exact Set.mem_image_of_mem _ supported
  rw [project_witness] at projected
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape
    (program sourceRequests helperRequests sourceCommit helperCommit next) initial audited _ projected

theorem event_bound (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (sourceRequests : First → List (Cfg × Digest)) (helperRequests : First → Second → List (Cfg × Digest))
    (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
    (helperCommit : First → OracleComp (SharedSequence.Shared Cfg Input Digest) Second)
    (next : First → Second → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (audited : CheckpointExecution.Audited enc dummy shape initial)
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
        sourceCommit).run initial) → ∀ second,
      second ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (helperCommit first.1)).run (RecordRoots.state shape (sourceRequests first.1) first.2)) → ∀ last,
      last ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (next first.1 second.1)).run (RecordRoots.state shape (helperRequests first.1 second.1) second.2)) →
      accepted first second last → arithmetic first second last ∨ CheckpointAvailability.Disagreement enc dummy shape last.2) :
    Pr{let outcome ← (witness enc dummy shape sourceRequests helperRequests sourceCommit helperCommit next
      initial)}[accepted outcome.1 outcome.2.1 outcome.2.2 ∧ ¬CheckpointCollision.Bad shape outcome.2.2.2] ≤ epsilon := by
  have averaged : Pr{let outcome ← (witness enc dummy shape sourceRequests helperRequests sourceCommit helperCommit next
      initial)}[arithmetic outcome.1 outcome.2.1 outcome.2.2] ≤ epsilon := by
    unfold witness
    apply prEvent_bind_le_of_forall_le
    intro first
    apply prEvent_bind_le_of_forall_le
    intro second
    simpa only [prEvent_norm] using arithmetic_bound first second
  apply le_trans (prEvent_mono_of_support _ _
    (fun outcome => arithmetic outcome.1 outcome.2.1 outcome.2.2) ?_) averaged
  intro outcome supported event
  have audit := audited_witness enc dummy shape sourceRequests helperRequests sourceCommit helperCommit next
    initial audited outcome supported
  simp only [witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,second,secondSupported,last,lastSupported,equal⟩ := supported
  subst outcome
  rcases reduction first firstSupported second secondSupported last lastSupported event.1 with arithmetic | disagreement
  · exact arithmetic
  · exact False.elim (event.2 (CheckpointAvailability.disagreement_implies_bad enc dummy shape last.2 audit disagreement))

end
end FormalProof4FHE.HasteBoots.StagedPrefixSafeBound
