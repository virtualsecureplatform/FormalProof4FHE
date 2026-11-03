module

public import FormalProof4FHE.HasteBoots.CheckpointHistory

@[expose] public section

/-! # Recording a finite family of roots without changing the hash log -/

open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.RecordRoots

noncomputable section

variable {Cfg Input Digest Payload : Type}

/-- Passive annotations for the roots already emitted by the commitment. -/
def program (roots : List (Cfg × Digest)) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Unit :=
  match roots with
  | [] => pure ()
  | request :: rest => do
    let _ ← (CheckpointExecution.Spec unifSpec Cfg Input Digest).query (.inr (.inr request))
    program rest

def state (shape : Cfg → Skeleton) (roots : List (Cfg × Digest))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape :=
  match roots with
  | [] => initial
  | request :: rest => state shape rest (CheckpointExecution.record shape initial request.1 request.2)

/-- Recording roots never performs a hash call or replaces the cached history. -/
theorem hash_eq (shape : Cfg → Skeleton) (roots : List (Cfg × Digest))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (state shape roots initial).hash = initial.hash := by
  induction roots generalizing initial with
  | nil => rfl
  | cons request rest ih => exact ih _

/-- Every earlier source snapshot is retained, even in an already failed state. -/
theorem retains (shape : Cfg → Skeleton) (roots : List (Cfg × Digest))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (tag : Cfg) (checkpoint : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) tag)
    (present : ⟨tag, checkpoint⟩ ∈ initial.checkpoints.checkpoints) :
    ⟨tag, checkpoint⟩ ∈ (state shape roots initial).checkpoints.checkpoints := by
  induction roots generalizing initial with
  | nil => exact present
  | cons request rest ih => exact ih _ (List.mem_append_left _ present)

/-- All roots are frozen at the same actual pre-recording hash log. -/
theorem recorded (shape : Cfg → Skeleton) (roots : List (Cfg × Digest))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (request : Cfg × Digest) (member : request ∈ roots) :
    ⟨request.1, ⟨request.2, initial.hash.log⟩⟩ ∈ (state shape roots initial).checkpoints.checkpoints := by
  induction roots generalizing initial with
  | nil => simp only [List.not_mem_nil] at member
  | cons head rest ih =>
    obtain equal | later := List.mem_cons.mp member
    · subst request
      exact retains shape rest (CheckpointExecution.record shape initial head.1 head.2) head.1
        ⟨head.2, initial.hash.log⟩ (List.mem_append_right _ (List.mem_singleton_self _))
    · exact ih _ later

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Root annotations have exactly the explicit state effect above. -/
theorem run_program (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (shape : Cfg → Skeleton) (roots : List (Cfg × Digest))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program roots)).run initial = pure ((), state shape roots initial) := by
  induction roots generalizing initial with
  | nil => rfl
  | cons request rest ih =>
    simp only [program, simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    exact ih _

end

end FormalProof4FHE.HasteBoots.RecordRoots
