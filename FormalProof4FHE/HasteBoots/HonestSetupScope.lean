module
public import FormalProof4FHE.HasteBoots.HonestKeySetupReceipts
public import FormalProof4FHE.HasteBoots.CheckpointScopedTransport
@[expose] public section

/-! Honest hash-only setup records no checkpoints. Its entire actual execution
can therefore use the later verifier geometry without changing roots or state. -/
namespace FormalProof4FHE.HasteBoots.HonestSetupScope
open OracleSpec OracleComp BinaryTree CheckpointRecordScope
noncomputable section
variable {Cfg Input Digest Payload : Type} {ι : Type} {base : OracleSpec ι}

/-- Every branch of the Merkle builder uses only shared hash queries. -/
theorem commitment (scope : Cfg → Prop) (enc : MerkleOracle.Encoding Input Digest Payload)
    {s : Skeleton} (payloads : LeafData Payload s) :
    Scoped (base := base) scope (ExecutedHonestCommitment.program enc payloads) := by
  induction payloads with
  | leaf payload =>
    change Scoped scope ((fun digest => FullData.leaf digest) <$>
      (liftM ((CheckpointExecution.Spec base Cfg Input Digest).query (.inr (.inl (enc.leaf () payload))))))
    exact map_scoped scope _ (query_scoped scope (.inr (.inl (enc.leaf () payload))) trivial) _
  | internal left right ihLeft ihRight =>
    change Scoped scope (do
      let l ← ExecutedHonestCommitment.program enc left
      let r ← ExecutedHonestCommitment.program enc right
      let root ← liftM ((CheckpointExecution.Spec base Cfg Input Digest).query
        (.inr (.inl (enc.node () (l.getRootValue,r.getRootValue)))))
      pure (FullData.internal root l r))
    apply bind_scoped scope _ _ ihLeft
    intro l
    apply bind_scoped scope _ _ ihRight
    intro r
    apply bind_scoped scope _ _ (query_scoped scope (.inr (.inl (enc.node () (l.getRootValue,r.getRootValue)))) trivial)
    intro root
    exact pure_scoped scope _

/-- All sequential matrix builders satisfy any checkpoint-recording scope. -/
theorem matrices {F : Type} [Field F] {H : Cfg → ℕ} {b levels : ℕ}
    (scope : Cfg → Prop) (enc : MerkleOracle.Encoding Input Digest (List F))
    (parameters : Fin levels → RecordedPaddedSource.Parameters F Cfg H b)
    (tables : (i : Fin levels) → RecordedPaddedSource.PhysicalMatrix (parameters i)) :
    Scoped (base := base) scope (HonestMatrixSetupTrace.program enc parameters tables) := by
  induction levels with
  | zero => exact pure_scoped scope _
  | succ levels ih =>
    simp only [HonestMatrixSetupTrace.program]
    apply bind_scoped scope _ _ (commitment scope enc _)
    intro first
    apply bind_scoped scope _ _ (ih _ _)
    intro rest
    exact pure_scoped scope _

/-- The actual key-root program inherits hash-only scope, for every key. -/
theorem key {q c levels : ℕ} [Fact q.Prime] {H : Cfg → ℕ}
    (scope : Cfg → Prop)
    (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (original : NativeKeySwitch.Key q (2^(c+2)) levels) :
    Scoped (base := base) scope (HonestKeySetupReceipts.program parameters enc psi original) := by
  exact map_scoped scope _ (matrices scope enc parameters _) _

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- Running the real setup under the verifier geometry copies all hash/history
state exactly; no distribution of independently sampled roots is substituted. -/
theorem transport {q c levels : ℕ} [Fact q.Prime] {H : Cfg → ℕ}
    (impl : QueryImpl base ProbComp)
    (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (psi : ZMod q)
    (original : NativeKeySwitch.Key q (2^(c+2)) levels) (oldShape newShape : Cfg → Skeleton)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape)
    (compatible : CheckpointShapeTransport.Compatible oldShape newShape before.checkpoints) :
    Prod.map id (CheckpointShapeTransport.state oldShape newShape) <$>
      (simulateQ (CheckpointExecution.handler impl enc dummy oldShape)
        (HonestKeySetupReceipts.program parameters enc psi original)).run before =
    (simulateQ (CheckpointExecution.handler impl enc dummy newShape)
      (HonestKeySetupReceipts.program parameters enc psi original)).run
      (CheckpointShapeTransport.state oldShape newShape before) :=
  CheckpointScopedTransport.run impl enc dummy oldShape newShape _ (key _ parameters enc psi original) before compatible

/-- Empty initialization is transported before setup, never reintroduced after it. -/
theorem from_empty {q c levels : ℕ} [Fact q.Prime] {H : Cfg → ℕ}
    (impl : QueryImpl base ProbComp)
    (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (psi : ZMod q)
    (original : NativeKeySwitch.Key q (2^(c+2)) levels) (oldShape newShape : Cfg → Skeleton) :
    Prod.map id (CheckpointShapeTransport.state oldShape newShape) <$>
      (simulateQ (CheckpointExecution.handler impl enc dummy oldShape)
        (HonestKeySetupReceipts.program parameters enc psi original)).run (CheckpointExecution.empty oldShape) =
    (simulateQ (CheckpointExecution.handler impl enc dummy newShape)
      (HonestKeySetupReceipts.program parameters enc psi original)).run (CheckpointExecution.empty newShape) := by
  apply transport impl parameters enc dummy psi original oldShape newShape (CheckpointExecution.empty oldShape)
  intro tag entry member
  cases member

end
end FormalProof4FHE.HasteBoots.HonestSetupScope
