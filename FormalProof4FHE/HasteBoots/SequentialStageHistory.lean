module
public import FormalProof4FHE.HasteBoots.MultiCommitmentPrefix
public import FormalProof4FHE.HasteBoots.RecordRoots
public import FormalProof4FHE.HasteBoots.SharedSequence
public import FormalProof4FHE.HasteBoots.RecordedSourceCoherence
@[expose] public section

/-! Sequential committed stages share the actual final state of their
predecessor. Retained analysis snapshots erase to the literal composed program;
no child execution restarts from an empty checkpoint history. -/
namespace FormalProof4FHE.HasteBoots.SequentialStageHistory
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability
noncomputable section
variable {Cfg Input Digest Payload Emission Result : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- A committed stage preserves every previously recorded owner snapshot,
including when the common stability monitor has already failed. -/
theorem witness_retains
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (requests : Emission → List (Cfg × Digest))
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (next : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : (Emission × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
      Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support (MultiCommitmentPrefix.witness enc dummy shape requests commit next initial))
    (tag : Cfg) (checkpoint : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) tag)
    (present : ⟨tag,checkpoint⟩ ∈ initial.checkpoints.checkpoints) :
    ⟨tag,checkpoint⟩ ∈ outcome.2.2.checkpoints.checkpoints := by
  simp only [MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,last,lastSupported,equal⟩ := supported
  subst outcome
  have afterCommit := CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp)
    enc dummy shape tag checkpoint commit initial present first firstSupported
  have afterRecording := RecordRoots.retains shape (requests first.1) first.2 tag checkpoint afterCommit
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape tag checkpoint
    (next first.1) _ afterRecording last lastSupported

/-- Every requested root is frozen at the actual post-commit hash log and
retained through the whole stage, for an arbitrary incoming shared state. -/
theorem witness_recorded
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (requests : Emission → List (Cfg × Digest))
    (commit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (next : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : (Emission × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
      Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support (MultiCommitmentPrefix.witness enc dummy shape requests commit next initial))
    (request : Cfg × Digest) (member : request ∈ requests outcome.1.1) :
    ⟨request.1, ⟨request.2,outcome.1.2.hash.log⟩⟩ ∈ outcome.2.2.checkpoints.checkpoints := by
  simp only [MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,_,last,lastSupported,equal⟩ := supported
  subst outcome
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape request.1
    ⟨request.2,first.2.hash.log⟩ (next first.1) _
    (RecordRoots.recorded shape (requests first.1) first.2 request member) last lastSupported

variable {SecondEmission SecondResult : Type}

def program
    (firstRequests : Emission → List (Cfg × Digest))
    (firstCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (firstNext : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (secondRequests : Emission × Result → SecondEmission → List (Cfg × Digest))
    (secondCommit : Emission × Result → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondEmission)
    (secondNext : Emission × Result → SecondEmission → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondResult) := do
  let first ← MultiCommitmentPrefix.program firstRequests firstCommit firstNext
  let second ← MultiCommitmentPrefix.program (secondRequests first) (secondCommit first) (secondNext first)
  pure (first,second)

def witness
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (firstRequests : Emission → List (Cfg × Digest))
    (firstCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (firstNext : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (secondRequests : Emission × Result → SecondEmission → List (Cfg × Digest))
    (secondCommit : Emission × Result → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondEmission)
    (secondNext : Emission × Result → SecondEmission → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondResult)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) := do
  let first ← MultiCommitmentPrefix.witness enc dummy shape firstRequests firstCommit firstNext initial
  let actualFirst := (first.1.1,first.2.1)
  let second ← MultiCommitmentPrefix.witness enc dummy shape (secondRequests actualFirst)
    (secondCommit actualFirst) (secondNext actualFirst) first.2.2
  pure (first,second)

/-- Erasure keeps both stage results and exactly the final shared history. -/
theorem project_witness
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (firstRequests : Emission → List (Cfg × Digest))
    (firstCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (firstNext : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (secondRequests : Emission × Result → SecondEmission → List (Cfg × Digest))
    (secondCommit : Emission × Result → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondEmission)
    (secondNext : Emission × Result → SecondEmission → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondResult)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (fun outcome => (((outcome.1.1.1,outcome.1.2.1),(outcome.2.1.1,outcome.2.2.1)),outcome.2.2.2)) <$>
      witness enc dummy shape firstRequests firstCommit firstNext secondRequests secondCommit secondNext initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program firstRequests firstCommit firstNext secondRequests secondCommit secondNext)).run initial := by
  simp only [witness,program,MultiCommitmentPrefix.witness,MultiCommitmentPrefix.program,
    simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,RecordRoots.run_program,
    map_bind,map_pure,pure_bind,bind_assoc]

/-- Both original recording times occur in the actual final shared history. -/
theorem both_recorded
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (firstRequests : Emission → List (Cfg × Digest))
    (firstCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (firstNext : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (secondRequests : Emission × Result → SecondEmission → List (Cfg × Digest))
    (secondCommit : Emission × Result → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondEmission)
    (secondNext : Emission × Result → SecondEmission → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondResult)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ((Emission × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
        Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
      (SecondEmission × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
        SecondResult × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support (witness enc dummy shape firstRequests firstCommit firstNext
      secondRequests secondCommit secondNext initial))
    (firstRequest secondRequest : Cfg × Digest)
    (firstMember : firstRequest ∈ firstRequests outcome.1.1.1)
    (secondMember : secondRequest ∈ secondRequests (outcome.1.1.1,outcome.1.2.1) outcome.2.1.1) :
    ⟨firstRequest.1, ⟨firstRequest.2,outcome.1.1.2.hash.log⟩⟩ ∈ outcome.2.2.2.checkpoints.checkpoints ∧
    ⟨secondRequest.1, ⟨secondRequest.2,outcome.2.1.2.hash.log⟩⟩ ∈ outcome.2.2.2.checkpoints.checkpoints := by
  simp only [witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨first,firstSupported,second,secondSupported,equal⟩ := supported
  subst outcome
  constructor
  · exact witness_retains enc dummy shape (secondRequests (first.1.1,first.2.1))
      (secondCommit (first.1.1,first.2.1)) (secondNext (first.1.1,first.2.1)) first.2.2 second secondSupported
      firstRequest.1 ⟨firstRequest.2,first.1.2.hash.log⟩
      (witness_recorded enc dummy shape firstRequests firstCommit firstNext initial first firstSupported firstRequest firstMember)
  · exact witness_recorded enc dummy shape (secondRequests (first.1.1,first.2.1))
      (secondCommit (first.1.1,first.2.1)) (secondNext (first.1.1,first.2.1)) first.2.2 second secondSupported
      secondRequest secondMember

/-- Auditing follows from the actual composed execution, not a final-state
certificate supplied by the caller. -/
theorem audited_final
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (firstRequests : Emission → List (Cfg × Digest))
    (firstCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (firstNext : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (secondRequests : Emission × Result → SecondEmission → List (Cfg × Digest))
    (secondCommit : Emission × Result → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondEmission)
    (secondNext : Emission × Result → SecondEmission → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondResult)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : ((Emission × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
        Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
      (SecondEmission × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
        SecondResult × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support (witness enc dummy shape firstRequests firstCommit firstNext
      secondRequests secondCommit secondNext initial))
    (audited : CheckpointExecution.Audited enc dummy shape initial) :
    CheckpointExecution.Audited enc dummy shape outcome.2.2.2 := by
  have projected : (((outcome.1.1.1,outcome.1.2.1),(outcome.2.1.1,outcome.2.2.1)),outcome.2.2.2) ∈
      support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (program firstRequests firstCommit firstNext secondRequests secondCommit secondNext)).run initial) := by
    rw [←project_witness enc dummy shape firstRequests firstCommit firstNext secondRequests secondCommit secondNext initial,
      support_map,Set.mem_image]
    exact ⟨outcome,supported,rfl⟩
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape
    (program firstRequests firstCommit firstNext secondRequests secondCommit secondNext) initial audited _ projected

variable {F : Type} [Field F] [DecidableEq F] {front suffix b m height : ℕ}

/-- Two occurrences of the same requested context/root have equal original
sources or the existing shared collision event. Both recording memberships
and the final audit are derived from the composed execution. -/
theorem same_request_sources_eq_or_bad
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (firstRequests : Emission → List (Cfg × Digest))
    (firstCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (firstNext : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (secondRequests : Emission × Result → SecondEmission → List (Cfg × Digest))
    (secondCommit : Emission × Result → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondEmission)
    (secondNext : Emission × Result → SecondEmission → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondResult)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (outcome : ((Emission × CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) ×
        Result × CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) ×
      (SecondEmission × CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) ×
        SecondResult × CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (supported : outcome ∈ support (witness enc dummy (RecordedSourceCoherence.Shape Cfg height) firstRequests firstCommit firstNext
      secondRequests secondCommit secondNext initial))
    (audited : CheckpointExecution.Audited enc dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (request : Cfg × Digest)
    (firstMember : request ∈ firstRequests outcome.1.1.1)
    (secondMember : request ∈ secondRequests (outcome.1.1.1,outcome.1.2.1) outcome.2.1.1)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ) :
    RecordedSourceCoherence.source (front := front) enc dummy domain capacity radius request.1
        ⟨request.2,outcome.1.1.2.hash.log⟩ =
      RecordedSourceCoherence.source enc dummy domain capacity radius request.1
        ⟨request.2,outcome.2.1.2.hash.log⟩ ∨
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.2.2.2 := by
  have recorded := both_recorded enc dummy (RecordedSourceCoherence.Shape Cfg height) firstRequests firstCommit firstNext
    secondRequests secondCommit secondNext initial outcome supported request request firstMember secondMember
  have finalAudit := audited_final enc dummy (RecordedSourceCoherence.Shape Cfg height) firstRequests firstCommit firstNext
    secondRequests secondCommit secondNext initial outcome supported audited
  exact RecordedSourceCoherence.source_eq_or_bad enc dummy domain capacity radius outcome.2.2.2 finalAudit
    request.1 _ _ recorded.1 recorded.2 rfl

/-- All shared-request source drift is charged once on the actual composed
program. No separate hash charge or union is introduced for either stage. -/
theorem source_drift_bound [Fintype Digest]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (firstRequests : Emission → List (Cfg × Digest))
    (firstCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (firstNext : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (secondRequests : Emission × Result → SecondEmission → List (Cfg × Digest))
    (secondCommit : Emission × Result → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondEmission)
    (secondNext : Emission × Result → SecondEmission → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondResult)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ) :
    Pr{let outcome ← (witness enc dummy (RecordedSourceCoherence.Shape Cfg height)
      firstRequests firstCommit firstNext secondRequests secondCommit secondNext
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      ∃ request : Cfg × Digest,
        request ∈ firstRequests outcome.1.1.1 ∧
        request ∈ secondRequests (outcome.1.1.1,outcome.1.2.1) outcome.2.1.1 ∧
        RecordedSourceCoherence.source (front := front) enc dummy domain capacity radius request.1
            ⟨request.2,outcome.1.1.2.hash.log⟩ ≠
          RecordedSourceCoherence.source enc dummy domain capacity radius request.1
            ⟨request.2,outcome.2.1.2.hash.log⟩] ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (RecordedSourceCoherence.Shape Cfg height))
        (CheckpointCollision.loss unifSpec (RecordedSourceCoherence.Shape Cfg height))
        (program firstRequests firstCommit firstNext secondRequests secondCommit secondNext)
        (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) := by
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp)
    enc dummy (RecordedSourceCoherence.Shape Cfg height)
    (program firstRequests firstCommit firstNext secondRequests secondCommit secondNext)
  rw [←project_witness enc dummy (RecordedSourceCoherence.Shape Cfg height)
    firstRequests firstCommit firstNext secondRequests secondCommit secondNext
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)),prEvent_map] at bound
  apply le_trans (prEvent_mono_of_support _ _
    (fun outcome => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) outcome.2.2.2) ?_) bound
  intro outcome supported drift
  obtain ⟨request,firstMember,secondMember,different⟩ := drift
  have initial := CheckpointExecution.good_empty enc dummy (RecordedSourceCoherence.Shape Cfg height)
  rcases same_request_sources_eq_or_bad enc dummy firstRequests firstCommit firstNext
      secondRequests secondCommit secondNext _ outcome supported ⟨initial.1,fun _ => initial.2.2⟩
      request firstMember secondMember domain capacity radius with equal | bad
  · exact False.elim (different equal)
  · exact bad

end
end FormalProof4FHE.HasteBoots.SequentialStageHistory
