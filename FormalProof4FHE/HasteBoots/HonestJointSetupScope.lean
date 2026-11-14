module
public import FormalProof4FHE.HasteBoots.HonestSetupScope
public import FormalProof4FHE.HasteBoots.HonestJointKeySetup
@[expose] public section

/-! Both actual key setups are hash-only. Their complete shared execution
therefore transports to the full verifier geometry without changing roots,
cache, chronological log or failure flag. -/
namespace FormalProof4FHE.HasteBoots.HonestJointSetupScope
open OracleSpec OracleComp BinaryTree CheckpointRecordScope
noncomputable section
variable {q cells lanes rows levels c keyLevels : ℕ} [Fact q.Prime]
  {Cfg Input Digest : Type} {H : Cfg → ℕ} {ι : Type} {base : OracleSpec ι}
variable (controlParameters : Fin (2*levels) → RecordedPaddedSource.Parameters (ZMod q) Cfg H (2^lanes))
  (keyParameters : Fin keyLevels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
  (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
  (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := levels))
  (original : NativeKeySwitch.Key q (2^(c+2)) keyLevels)

/-- Actual control-key commitments satisfy every checkpoint-recording scope. -/
theorem control (scope : Cfg → Prop) :
    Scoped (base := base) scope (HonestControlKeySetup.program controlParameters enc psi controls) :=
  map_scoped scope _ (HonestSetupScope.matrices scope enc controlParameters _) _

/-- Both setups record no checkpoints, including when sharing an existing cache. -/
theorem joint (scope : Cfg → Prop) :
    Scoped (base := base) scope
      (HonestJointKeySetup.program controlParameters keyParameters enc psi controls original) := by
  unfold HonestJointKeySetup.program
  apply bind_scoped scope _ _ (control controlParameters enc psi controls scope)
  intro controlRoots
  apply bind_scoped scope _ _ (HonestSetupScope.key scope keyParameters enc psi original)
  intro keyRoots
  exact pure_scoped scope _

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Changing geometry transports the actual combined setup run from the same
populated incoming cache and log; no independently generated roots are used. -/
theorem transport (impl : QueryImpl base ProbComp) (dummy : Digest)
    (oldShape newShape : Cfg → Skeleton)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape)
    (compatible : CheckpointShapeTransport.Compatible oldShape newShape before.checkpoints) :
    Prod.map id (CheckpointShapeTransport.state oldShape newShape) <$>
      (simulateQ (CheckpointExecution.handler impl enc dummy oldShape)
        (HonestJointKeySetup.program controlParameters keyParameters enc psi controls original)).run before =
    (simulateQ (CheckpointExecution.handler impl enc dummy newShape)
      (HonestJointKeySetup.program controlParameters keyParameters enc psi controls original)).run
      (CheckpointShapeTransport.state oldShape newShape before) :=
  CheckpointScopedTransport.run impl enc dummy oldShape newShape _
    (joint controlParameters keyParameters enc psi controls original _) before compatible

/-- Empty initialization is transported before either setup; both actual
setups and their entire accumulated history remain in the resulting run. -/
theorem from_empty (impl : QueryImpl base ProbComp) (dummy : Digest)
    (oldShape newShape : Cfg → Skeleton) :
    Prod.map id (CheckpointShapeTransport.state oldShape newShape) <$>
      (simulateQ (CheckpointExecution.handler impl enc dummy oldShape)
        (HonestJointKeySetup.program controlParameters keyParameters enc psi controls original)).run
          (CheckpointExecution.empty oldShape) =
    (simulateQ (CheckpointExecution.handler impl enc dummy newShape)
      (HonestJointKeySetup.program controlParameters keyParameters enc psi controls original)).run
        (CheckpointExecution.empty newShape) := by
  apply transport controlParameters keyParameters enc psi controls original impl dummy oldShape newShape
    (CheckpointExecution.empty oldShape)
  intro tag entry member
  cases member

/-- The setup witness used by native arithmetic projects to the exact raw
combined setup at the full verifier geometry, retaining both root maps and
its complete final monitor state. -/
theorem witness_from_empty (impl : QueryImpl base ProbComp) (dummy : Digest)
    (oldShape newShape : Cfg → Skeleton) :
    (fun built => ((built.1.1,built.2.1),CheckpointShapeTransport.state oldShape newShape built.2.2)) <$>
      HonestJointKeySetup.witness controlParameters keyParameters enc psi controls original impl dummy oldShape =
    (simulateQ (CheckpointExecution.handler impl enc dummy newShape)
      (HonestJointKeySetup.program controlParameters keyParameters enc psi controls original)).run
        (CheckpointExecution.empty newShape) := by
  rw [←from_empty controlParameters keyParameters enc psi controls original impl dummy oldShape newShape,
    ←HonestJointKeySetup.project_witness controlParameters keyParameters enc psi controls original impl dummy oldShape,
    Functor.map_map]
  rfl

end
end FormalProof4FHE.HasteBoots.HonestJointSetupScope
