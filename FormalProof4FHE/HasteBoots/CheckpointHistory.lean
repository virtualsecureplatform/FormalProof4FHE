module

public import FormalProof4FHE.HasteBoots.CheckpointExecution

@[expose] public section

/-!
# Immutable checkpoint membership through shared execution

No private, hash or root-recording action removes an earlier root snapshot.
This is independent of whether the stability monitor is set: a failure cannot
be repaired by replacing the source against which later checks are measured.
-/

open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.CheckpointHistory

noncomputable section

variable {Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

theorem recorded_step (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (tag : Cfg) (checkpoint : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) tag)
    (query : (CheckpointExecution.Spec base Cfg Input Digest).Domain)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (recorded : ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (result : (CheckpointExecution.Spec base Cfg Input Digest).Range query ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((CheckpointExecution.handler implBase enc dummy shape query).run state)) :
    ⟨tag, checkpoint⟩ ∈ result.2.checkpoints.checkpoints := by
  rcases query with privateQuery | (hashQuery | request)
  · change result ∈ support ((fun answer => (answer, state)) <$> implBase privateQuery) at supported
    rw [support_map, Set.mem_image] at supported
    obtain ⟨_, _, equal⟩ := supported
    subst result
    exact recorded
  · change result ∈ support ((fun result =>
        (result.1, CheckpointExecution.afterHash enc dummy shape state result.2)) <$>
          (CachedHashHandler.handler hashQuery).run state.hash) at supported
    rw [support_map, Set.mem_image] at supported
    obtain ⟨_, _, equal⟩ := supported
    subst result
    exact recorded
  · change result ∈ support (pure ((), CheckpointExecution.record shape state request.1 request.2) : ProbComp _) at supported
    have equal := eq_of_mem_support_pure _ supported
    subst result
    exact List.mem_append_left _ recorded

/-- The original root source remains available after an arbitrary adaptive
program, with no stability or collision-freedom premise and no query bound. -/
theorem recorded_run {Result : Type} (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (tag : Cfg) (checkpoint : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) tag)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (recorded : ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler implBase enc dummy shape) program).run state)) :
    ⟨tag, checkpoint⟩ ∈ result.2.checkpoints.checkpoints :=
  simulateQ_run_preserves_inv_of_query _ (fun current => ⟨tag, checkpoint⟩ ∈ current.checkpoints.checkpoints)
    (fun query current present next reached =>
      recorded_step implBase enc dummy shape tag checkpoint query current present next reached)
    program state recorded result supported

end

end FormalProof4FHE.HasteBoots.CheckpointHistory
