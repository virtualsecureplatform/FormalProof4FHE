module
public import FormalProof4FHE.HasteBoots.ExecutedHonestCommitment
public import FormalProof4FHE.HasteBoots.CheckpointShapeTransport
@[expose] public section

/-! Actual shared hash logs grow by chronological extension. Geometry transport
copies them verbatim, so setup queries survive a change of extraction shape. -/
namespace FormalProof4FHE.HasteBoots.SharedHashLog
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {Cfg Input Digest Payload : Type} [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

theorem step (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (query : (CheckpointExecution.Spec base Cfg Input Digest).Domain)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : (CheckpointExecution.Spec base Cfg Input Digest).Range query ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((CheckpointExecution.handler impl enc dummy shape query).run state)) :
    state.hash.log <+: result.2.hash.log := by
  rcases query with privateQuery | (hashQuery | request)
  · change result ∈ support ((fun answer => (answer,state)) <$> impl privateQuery) at supported
    rw [support_map, Set.mem_image] at supported
    obtain ⟨_, _, equal⟩ := supported
    subst result
    exact List.prefix_refl _
  · change result ∈ support ((fun next => (next.1, CheckpointExecution.afterHash enc dummy shape state next.2)) <$>
      (CachedHashHandler.handler hashQuery).run state.hash) at supported
    rw [support_map, Set.mem_image] at supported
    obtain ⟨next, present, equal⟩ := supported
    subst result
    have trace := ExecutedHonestCommitment.hash_log hashQuery state.hash next present
    change state.hash.log <+: next.2.log
    rw [trace]
    exact List.prefix_append _ _
  · change result ∈ support (pure ((), CheckpointExecution.record shape state request.1 request.2) : ProbComp _) at supported
    have equal := eq_of_mem_support_pure _ supported
    subst result
    exact List.prefix_refl _

/-- Arbitrary private/hash/recording interleavings retain every setup query. -/
theorem run {Result : Type} (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape) program).run state)) :
    state.hash.log <+: result.2.hash.log := by
  apply simulateQ_run_preserves_inv_of_query _ (fun current => state.hash.log <+: current.hash.log)
    ?_ program state (List.prefix_refl _) result supported
  intro query current prior next present
  exact prior.trans (step impl enc dummy shape query current next present)

end
end FormalProof4FHE.HasteBoots.SharedHashLog
