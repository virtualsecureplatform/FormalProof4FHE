module
public import FormalProof4FHE.HasteBoots.NTTSequenceSoundness
@[expose] public section

/-! Original checkpoints and actual child acceptance throughout the ordered NTT loop. -/
namespace FormalProof4FHE.HasteBoots.NTTSequenceHistory
open OracleSpec OracleComp BinaryTree
open NTTSequence NTTSequenceSoundness
noncomputable section
variable {F Index Input Digest Cfg Response Memory CommitMemory : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b c r k front suffix m queries height : ℕ}
  [SampleableType (Fin k → Fin r → F)] [SampleableType (Fin b → F)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))] [SampleableType Digest]
variable (factory : Index → Memory → AuthenticatedNTT.Scheme F Input Digest Cfg Response Memory CommitMemory
  b c r k front suffix m queries height)

variable (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
  (indices : List Index) (memory : Memory)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (outcome : Trace (F := F) (Index := Index) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (supported : outcome ∈ support (witness factory enc dummy indices memory initial))

include supported in
/-- Previously recorded original sources survive every actual loop branch. -/
theorem retains (tag : Cfg)
    (checkpoint : RecordedSourceCoherence.Snapshot Input Digest Cfg height tag)
    (present : ⟨tag,checkpoint⟩ ∈ initial.checkpoints.checkpoints) :
    ⟨tag,checkpoint⟩ ∈ outcome.2.checkpoints.checkpoints := by
  have projected : (erase outcome.1,outcome.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (RecordedSourceCoherence.Shape Cfg height)) (program factory indices memory)).run initial) := by
    rw [←project_witness factory enc dummy indices memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointHistory.recorded_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (RecordedSourceCoherence.Shape Cfg height) tag checkpoint (program factory indices memory)
    initial present _ projected

include supported in
/-- The final audit follows from the exact erased execution at the inherited state. -/
theorem audited
    (incoming : CheckpointExecution.Audited enc dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    CheckpointExecution.Audited enc dummy (RecordedSourceCoherence.Shape Cfg height) outcome.2 := by
  have projected : (erase outcome.1,outcome.2) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy
        (RecordedSourceCoherence.Shape Cfg height)) (program factory indices memory)).run initial) := by
    rw [←project_witness factory enc dummy indices memory initial,support_map]
    exact Set.mem_image_of_mem _ supported
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) enc dummy
    (RecordedSourceCoherence.Shape Cfg height) (program factory indices memory) initial incoming _ projected

include supported in
/-- Every checkpoint retained by a child remains in the final loop history. -/
theorem child_recorded
    (entry : Index × Memory × Child (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height))
    (member : entry ∈ outcome.1.results)
    (tag : Cfg) (checkpoint : RecordedSourceCoherence.Snapshot Input Digest Cfg height tag)
    (present : ⟨tag,checkpoint⟩ ∈ entry.2.2.2.2.checkpoints.checkpoints) :
    ⟨tag,checkpoint⟩ ∈ outcome.2.checkpoints.checkpoints := by
  induction indices generalizing memory initial outcome with
  | nil =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    cases member
  | cons index rest ih =>
    simp only [witness,support_bind,Set.mem_iUnion] at supported
    obtain ⟨child,childSupported,remainder⟩ := supported
    by_cases passes : AuthenticatedNTT.accepted child.2.1 = true
    · simp only [passes,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨later,laterSupported,equal⟩ := remainder
      subst outcome
      rcases List.mem_cons.mp member with first | tail
      · subst entry
        exact retains factory enc dummy rest child.2.1.2.memory child.2.2 later laterSupported tag checkpoint present
      · exact ih child.2.1.2.memory child.2.2 later laterSupported tail
    · simp [passes] at remainder
      subst outcome
      have first := List.mem_singleton.mp member
      subst entry
      exact present


include supported in
/-- Loop acceptance derives actual acceptance of every retained child. -/
theorem accepted_children
    (entry : Index × Memory × Child (F := F) (Input := Input) (Digest := Digest) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k)
      (front := front) (queries := queries) (height := height))
    (member : entry ∈ outcome.1.results)
    (accepted : outcome.1.accepted = true) : AuthenticatedNTT.accepted entry.2.2.2.1 = true := by
  induction indices generalizing memory initial outcome with
  | nil =>
    have equal := eq_of_mem_support_pure _ supported
    subst outcome
    cases member
  | cons index rest ih =>
    simp only [witness,support_bind,Set.mem_iUnion] at supported
    obtain ⟨child,childSupported,remainder⟩ := supported
    by_cases passes : AuthenticatedNTT.accepted child.2.1 = true
    · simp only [passes,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨later,laterSupported,equal⟩ := remainder
      subst outcome
      rcases List.mem_cons.mp member with first | tail
      · subst entry
        exact passes
      · exact ih child.2.1.2.memory child.2.2 later laterSupported tail accepted
    · simp [passes] at remainder
      subst outcome
      exact (Bool.false_ne_true accepted).elim

end
end FormalProof4FHE.HasteBoots.NTTSequenceHistory
