module
public import FormalProof4FHE.HasteBoots.CheckpointCollision
@[expose] public section

/-! Every recorded cumulative transcript remains represented in the actual
shared cache. This follows from execution, including repeated queries and
arbitrary interleaving of private calls and checkpoint annotations. -/
namespace FormalProof4FHE.HasteBoots.RecordedCheckpointQueries
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability
noncomputable section
variable {Cfg Input Digest Payload : Type}

/-- Each frozen transcript consists of answers still present in the cache. -/
def Sound (shape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) : Prop :=
  ∀ saved ∈ state.checkpoints.checkpoints, ∀ entry ∈ saved.2.cumulativeLog,
    state.hash.cache entry.1 = some entry.2

theorem empty (shape : Cfg → Skeleton) : Sound (Input := Input) (Digest := Digest) shape
    (CheckpointExecution.empty shape) := by
  simp [Sound, CheckpointExecution.empty, ExtractorState.empty]

variable [DecidableEq Input]

theorem record (shape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (coherent : CachedHashHandler.Coherent state.hash) (sound : Sound shape state)
    (tag : Cfg) (root : Digest) : Sound shape (CheckpointExecution.record shape state tag root) := by
  intro saved member entry logged
  change saved ∈ state.checkpoints.checkpoints ++ [⟨tag, ⟨root, state.hash.log⟩⟩] at member
  rcases List.mem_append.mp member with old | fresh
  · exact sound saved old entry logged
  · have equal := List.mem_singleton.mp fresh
    subst saved
    exact (CachedHashHandler.represents_cache state.hash coherent).1 entry logged

section Runtime
variable [DecidableEq Digest] [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

theorem step (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (query : (CheckpointExecution.Spec base Cfg Input Digest).Domain)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (valid : CachedHashHandler.Coherent state.hash ∧ Sound shape state)
    (result : (CheckpointExecution.Spec base Cfg Input Digest).Range query ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((CheckpointExecution.handler impl enc dummy shape query).run state)) :
    CachedHashHandler.Coherent result.2.hash ∧ Sound shape result.2 := by
  rcases query with privateQuery | (hashQuery | request)
  · change result ∈ support ((fun answer => (answer, state)) <$> impl privateQuery) at supported
    rw [support_map, Set.mem_image] at supported
    obtain ⟨_, _, equal⟩ := supported
    subst result
    exact valid
  · change result ∈ support ((fun next => (next.1, CheckpointExecution.afterHash enc dummy shape state next.2)) <$>
      (CachedHashHandler.handler hashQuery).run state.hash) at supported
    rw [support_map, Set.mem_image] at supported
    obtain ⟨next, supported, equal⟩ := supported
    subst result
    refine ⟨CachedHashHandler.coherent_step hashQuery state.hash valid.1 next supported, ?_⟩
    intro saved member entry logged
    exact CachedHashCollision.cache_monotone_step hashQuery state.hash next supported
      (valid.2 saved member entry logged)
  · change result ∈ support (pure ((), CheckpointExecution.record shape state request.1 request.2) : ProbComp _) at supported
    have equal := eq_of_mem_support_pure _ supported
    subst result
    exact ⟨valid.1, record shape state valid.1 valid.2 request.1 request.2⟩

theorem run {Result : Type} (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (valid : CachedHashHandler.Coherent state.hash ∧ Sound shape state)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape) program).run state)) :
    CachedHashHandler.Coherent result.2.hash ∧ Sound shape result.2 :=
  simulateQ_run_preserves_inv_of_query _ _ (step impl enc dummy shape)
    program state valid result supported

/-- Every supported complete shared execution establishes all frozen-cache receipts. -/
theorem from_empty {Result : Type} (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape) program).run
      (CheckpointExecution.empty shape))) : Sound shape result.2 :=
  (run impl enc dummy shape program (CheckpointExecution.empty shape)
    ⟨CachedHashHandler.coherent_empty, empty shape⟩ result supported).2

end Runtime
end
end FormalProof4FHE.HasteBoots.RecordedCheckpointQueries
