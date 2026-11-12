module
public import FormalProof4FHE.HasteBoots.CheckpointRecordScope
@[expose] public section

/-! A scoped prefix can run under the geometry of its later continuation.
The equality retains the entire history and monitor, not only real answers. -/
namespace FormalProof4FHE.HasteBoots.CheckpointScopedTransport
open OracleSpec OracleComp BinaryTree
open CheckpointRecordScope
noncomputable section
variable {Cfg Input Digest Payload A : Type} [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest] {ι : Type} {base : OracleSpec ι}

theorem step (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (oldShape newShape : Cfg → Skeleton)
    (query : (CheckpointExecution.Spec base Cfg Input Digest).Domain)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape)
    (compatible : CheckpointShapeTransport.Compatible oldShape newShape before.checkpoints) :
    Prod.map id (CheckpointShapeTransport.state oldShape newShape) <$>
      (CheckpointExecution.handler implBase enc dummy oldShape query).run before =
    (CheckpointExecution.handler implBase enc dummy newShape query).run
      (CheckpointShapeTransport.state oldShape newShape before) := by
  rcases query with privateQuery | (hashQuery | request)
  · simp only [CheckpointExecution.handler,StateT.run_mk,Functor.map_map]
    rfl
  · change Prod.map id (CheckpointShapeTransport.state oldShape newShape) <$>
      ((fun result => (result.1,CheckpointExecution.afterHash enc dummy oldShape before result.2)) <$>
        (CachedHashHandler.handler hashQuery).run before.hash) = _
    rw [Functor.map_map]
    change (fun result : Digest × CachedHashHandler.State Input Digest => (result.1,CheckpointShapeTransport.state oldShape newShape
      (CheckpointExecution.afterHash enc dummy oldShape before result.2))) <$> _ =
      (fun result : Digest × CachedHashHandler.State Input Digest => (result.1,CheckpointExecution.afterHash enc dummy newShape
        (CheckpointShapeTransport.state oldShape newShape before) result.2)) <$> _
    congr 1
    funext result
    rw [CheckpointShapeTransport.afterHash enc dummy oldShape newShape before compatible]
  · change pure ((),CheckpointShapeTransport.state oldShape newShape
      (CheckpointExecution.record oldShape before request.1 request.2)) =
      (pure ((),CheckpointExecution.record newShape (CheckpointShapeTransport.state oldShape newShape before) request.1 request.2) : ProbComp _)
    rw [CheckpointShapeTransport.record]

/-- All adaptive answers and snapshots agree with the single mixed-geometry
handler, provided the prefix only records tags whose geometry is unchanged. -/
theorem run (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (oldShape newShape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) A)
    (restricted : Scoped (fun tag => oldShape tag = newShape tag) program)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape)
    (compatible : CheckpointShapeTransport.Compatible oldShape newShape before.checkpoints) :
    Prod.map id (CheckpointShapeTransport.state oldShape newShape) <$>
      (simulateQ (CheckpointExecution.handler implBase enc dummy oldShape) program).run before =
    (simulateQ (CheckpointExecution.handler implBase enc dummy newShape) program).run
      (CheckpointShapeTransport.state oldShape newShape before) := by
  induction program using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure,Prod.map_apply,id_eq]
  | query_bind query next ih =>
    obtain ⟨allowed,children⟩ := (query_bind_scoped _ query next).mp restricted
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
    rw [←step implBase enc dummy oldShape newShape query before compatible]
    simp only [bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro middle present
    exact ih middle.1 (children middle.1) middle.2
      (compatible_step implBase enc dummy oldShape newShape query allowed before compatible middle present)

end
end FormalProof4FHE.HasteBoots.CheckpointScopedTransport
