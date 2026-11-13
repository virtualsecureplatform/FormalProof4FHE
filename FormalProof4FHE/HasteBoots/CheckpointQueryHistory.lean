module
public import FormalProof4FHE.HasteBoots.SharedHashLog
public import FormalProof4FHE.HasteBoots.RecordedCheckpointQueries
@[expose] public section

/-! Query chronology and frozen cache receipts transport across extraction
geometries independently of the semantic shape-compatibility requirement. -/
namespace FormalProof4FHE.HasteBoots.CheckpointQueryHistory
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {Cfg Input Digest Payload : Type}

/-- Geometry transport copies all roots, frozen logs and cached answers. -/
theorem transport_sound (oldShape newShape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape)
    (sound : RecordedCheckpointQueries.Sound oldShape state) :
    RecordedCheckpointQueries.Sound newShape (CheckpointShapeTransport.state oldShape newShape state) := by
  intro saved member entry logged
  change saved ∈ state.checkpoints.checkpoints.map (fun old =>
    ⟨old.1, CheckpointShapeTransport.checkpoint oldShape newShape old.1 old.2⟩) at member
  obtain ⟨old, present, equal⟩ := List.mem_map.mp member
  subst saved
  exact sound old present entry logged

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {ι : Type} {base : OracleSpec ι}

/-- One actual supported shared run supplies chronology and receipt preservation. -/
theorem run {Result : Type} (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (valid : CachedHashHandler.Coherent state.hash ∧ RecordedCheckpointQueries.Sound shape state)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape) program).run state)) :
    state.hash.log <+: result.2.hash.log ∧ CachedHashHandler.Coherent result.2.hash ∧
      RecordedCheckpointQueries.Sound shape result.2 :=
  ⟨SharedHashLog.run impl enc dummy shape program state result supported,
    RecordedCheckpointQueries.run impl enc dummy shape program state valid result supported⟩

end
end FormalProof4FHE.HasteBoots.CheckpointQueryHistory
