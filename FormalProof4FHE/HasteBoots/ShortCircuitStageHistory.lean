module
public import FormalProof4FHE.HasteBoots.SequentialStageHistory
@[expose] public section

/-! Committed stages with actual caller short-circuiting. A rejected first
stage skips the second commitment, root annotations and continuation. -/
namespace FormalProof4FHE.HasteBoots.ShortCircuitStageHistory
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {Cfg Input Digest Payload Emission Result SecondEmission SecondResult : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

def program
    (firstRequests : Emission → List (Cfg × Digest))
    (firstCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (firstNext : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (continues : Emission × Result → Bool)
    (secondRequests : Emission × Result → SecondEmission → List (Cfg × Digest))
    (secondCommit : Emission × Result → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondEmission)
    (secondNext : Emission × Result → SecondEmission → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondResult) := do
  let first ← MultiCommitmentPrefix.program firstRequests firstCommit firstNext
  if continues first then
    let second ← MultiCommitmentPrefix.program (secondRequests first) (secondCommit first) (secondNext first)
    pure (first,some second)
  else pure (first,none)

def witness
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (firstRequests : Emission → List (Cfg × Digest))
    (firstCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (firstNext : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (continues : Emission × Result → Bool)
    (secondRequests : Emission × Result → SecondEmission → List (Cfg × Digest))
    (secondCommit : Emission × Result → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondEmission)
    (secondNext : Emission × Result → SecondEmission → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondResult)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) := do
  let first ← MultiCommitmentPrefix.witness enc dummy shape firstRequests firstCommit firstNext initial
  let actualFirst := (first.1.1,first.2.1)
  if continues actualFirst then
    let second ← MultiCommitmentPrefix.witness enc dummy shape (secondRequests actualFirst)
      (secondCommit actualFirst) (secondNext actualFirst) first.2.2
    pure (first,some second)
  else pure (first,none)

/-- Erasure keeps both stage results and exactly the final shared history. -/
theorem project_witness
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (firstRequests : Emission → List (Cfg × Digest))
    (firstCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (firstNext : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (continues : Emission × Result → Bool)
    (secondRequests : Emission × Result → SecondEmission → List (Cfg × Digest))
    (secondCommit : Emission × Result → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondEmission)
    (secondNext : Emission × Result → SecondEmission → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondResult)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (fun outcome => match outcome.2 with
      | none => (((outcome.1.1.1,outcome.1.2.1),none),outcome.1.2.2)
      | some second => (((outcome.1.1.1,outcome.1.2.1),some (second.1.1,second.2.1)),second.2.2)) <$>
      witness enc dummy shape firstRequests firstCommit firstNext continues secondRequests secondCommit secondNext initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program firstRequests firstCommit firstNext continues secondRequests secondCommit secondNext)).run initial := by
  simp only [witness,program,MultiCommitmentPrefix.witness,MultiCommitmentPrefix.program,
    simulateQ_bind,StateT.run_bind,RecordRoots.run_program,
    map_bind,pure_bind,bind_assoc]
  congr 1
  funext first
  congr 1
  funext last
  split <;> simp only [map_bind,map_pure,simulateQ_bind,StateT.run_bind,
    simulateQ_pure,StateT.run_pure,RecordRoots.run_program,pure_bind]


/-- A reached second stage has the same supported history as the actual
sequential execution, and the caller continuation test necessarily passed. -/
theorem reached_second
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (firstRequests : Emission → List (Cfg × Digest))
    (firstCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (firstNext : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (continues : Emission × Result → Bool)
    (secondRequests : Emission × Result → SecondEmission → List (Cfg × Digest))
    (secondCommit : Emission × Result → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondEmission)
    (secondNext : Emission × Result → SecondEmission → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondResult)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (first : (Emission × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
      Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (second : (SecondEmission × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) ×
      SecondResult × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : (first,some second) ∈ support (witness enc dummy shape firstRequests firstCommit firstNext
      continues secondRequests secondCommit secondNext initial)) :
    continues (first.1.1,first.2.1) = true ∧
    (first,second) ∈ support (SequentialStageHistory.witness enc dummy shape firstRequests firstCommit firstNext
      secondRequests secondCommit secondNext initial) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨selected,selectedSupported,rest⟩ := supported
  by_cases go : continues (selected.1.1,selected.2.1) = true
  · simp only [go,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at rest
    obtain ⟨other,otherSupported,equal⟩ := rest
    have firstEq : first = selected := congrArg Prod.fst equal
    have secondEq : second = other := Option.some.inj (congrArg Prod.snd equal)
    subst selected
    subst other
    refine ⟨go,?_⟩
    simp only [SequentialStageHistory.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff]
    exact ⟨first,selectedSupported,second,otherSupported,rfl⟩
  · simp [go] at rest

variable {F : Type} [Field F] [DecidableEq F] {front suffix b m height : ℕ}

/-- Reached child stages share original sources using their actual common
history; recording and auditing premises are derived by composition. -/
theorem same_request_sources_eq_or_bad
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (firstRequests : Emission → List (Cfg × Digest))
    (firstCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (firstNext : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (continues : Emission × Result → Bool)
    (secondRequests : Emission × Result → SecondEmission → List (Cfg × Digest))
    (secondCommit : Emission × Result → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondEmission)
    (secondNext : Emission × Result → SecondEmission → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondResult)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (first : (Emission × CheckpointExecution.State (Input := Input) (Digest := Digest)
        (RecordedSourceCoherence.Shape Cfg height)) × Result ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (second : (SecondEmission × CheckpointExecution.State (Input := Input) (Digest := Digest)
        (RecordedSourceCoherence.Shape Cfg height)) × SecondResult ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (supported : (first,some second) ∈ support (witness enc dummy (RecordedSourceCoherence.Shape Cfg height) firstRequests firstCommit firstNext
      continues secondRequests secondCommit secondNext initial))
    (audited : CheckpointExecution.Audited enc dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (request : Cfg × Digest)
    (firstMember : request ∈ firstRequests first.1.1)
    (secondMember : request ∈ secondRequests (first.1.1,first.2.1) second.1.1)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ) :
    RecordedSourceCoherence.source (front := front) enc dummy domain capacity radius request.1
        ⟨request.2,first.1.2.hash.log⟩ =
      RecordedSourceCoherence.source enc dummy domain capacity radius request.1
        ⟨request.2,second.1.2.hash.log⟩ ∨
    CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height) second.2.2 := by
  have reached := reached_second enc dummy (RecordedSourceCoherence.Shape Cfg height)
    firstRequests firstCommit firstNext continues secondRequests secondCommit secondNext initial first second supported
  exact SequentialStageHistory.same_request_sources_eq_or_bad enc dummy firstRequests firstCommit firstNext
    secondRequests secondCommit secondNext initial (first,second) reached.2 audited request firstMember secondMember
    domain capacity radius

/-- Shared-request source drift is charged on the actual short-circuit
program. Skipped children contribute no fictitious continuation work. -/
theorem source_drift_bound [Fintype Digest]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (firstRequests : Emission → List (Cfg × Digest))
    (firstCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) Emission)
    (firstNext : Emission → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
    (continues : Emission × Result → Bool)
    (secondRequests : Emission × Result → SecondEmission → List (Cfg × Digest))
    (secondCommit : Emission × Result → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondEmission)
    (secondNext : Emission × Result → SecondEmission → OracleComp (SharedSequence.Shared Cfg Input Digest) SecondResult)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ) :
    Pr{let outcome ← (witness enc dummy (RecordedSourceCoherence.Shape Cfg height)
      firstRequests firstCommit firstNext continues secondRequests secondCommit secondNext
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      ∃ second, outcome.2 = some second ∧ ∃ request : Cfg × Digest,
        request ∈ firstRequests outcome.1.1.1 ∧
        request ∈ secondRequests (outcome.1.1.1,outcome.1.2.1) second.1.1 ∧
        RecordedSourceCoherence.source (front := front) enc dummy domain capacity radius request.1
            ⟨request.2,outcome.1.1.2.hash.log⟩ ≠
          RecordedSourceCoherence.source enc dummy domain capacity radius request.1
            ⟨request.2,second.1.2.hash.log⟩] ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy (RecordedSourceCoherence.Shape Cfg height))
        (CheckpointCollision.loss unifSpec (RecordedSourceCoherence.Shape Cfg height))
        (program firstRequests firstCommit firstNext continues secondRequests secondCommit secondNext)
        (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) := by
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp)
    enc dummy (RecordedSourceCoherence.Shape Cfg height)
    (program firstRequests firstCommit firstNext continues secondRequests secondCommit secondNext)
  rw [←project_witness enc dummy (RecordedSourceCoherence.Shape Cfg height)
    firstRequests firstCommit firstNext continues secondRequests secondCommit secondNext
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)),prEvent_map] at bound
  refine le_trans (prEvent_mono_of_support _ _
    (fun outcome => CheckpointCollision.Bad (RecordedSourceCoherence.Shape Cfg height)
      (match outcome.2 with
        | none => (((outcome.1.1.1,outcome.1.2.1),none),outcome.1.2.2)
        | some second => (((outcome.1.1.1,outcome.1.2.1),some (second.1.1,second.2.1)),second.2.2)).2) ?_) ?_
  intro outcome supported drift
  rcases outcome with ⟨first,optional⟩
  obtain ⟨second,reached,request,firstMember,secondMember,different⟩ := drift
  change optional = some second at reached
  subst optional
  have initial := CheckpointExecution.good_empty enc dummy (RecordedSourceCoherence.Shape Cfg height)
  rcases same_request_sources_eq_or_bad enc dummy firstRequests firstCommit firstNext continues
      secondRequests secondCommit secondNext _ first second supported ⟨initial.1,fun _ => initial.2.2⟩
      request firstMember secondMember domain capacity radius with equal | bad
  · exact False.elim (different equal)
  · exact bad
  convert bound using 1
  apply prEvent_congr
  intro outcome
  cases outcome.2 <;> rfl

end
end FormalProof4FHE.HasteBoots.ShortCircuitStageHistory
