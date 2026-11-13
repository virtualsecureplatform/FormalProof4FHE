module
public import FormalProof4FHE.HasteBoots.HonestKeyQueryReceipt
public import FormalProof4FHE.HasteBoots.HonestSetupInitialHistory
@[expose] public section

/-! Hash-only honest key setup returns public roots. Actual supported execution
establishes both factual query receipts and all initial PBS history invariants. -/
namespace FormalProof4FHE.HasteBoots.HonestKeySetupReceipts
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {q c levels : ℕ} [Fact q.Prime]
  {Cfg Input Digest : Type} {H : Cfg → ℕ}

def program {ι : Type} {base : OracleSpec ι}
    (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (original : NativeKeySwitch.Key q (2^(c+2)) levels) :
    OracleComp (CheckpointExecution.Spec base Cfg Input Digest) (Fin levels → Digest) :=
  (fun labels level => (labels level).getRootValue) <$>
    HonestMatrixSetupTrace.program enc parameters (HonestRecordedEvaluationKey.table parameters psi original)

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- No setup root, query receipt, audit or history compatibility certificate is
provided independently of the actual hash-only setup execution. -/
theorem initialized {ι : Type} {base : OracleSpec ι} (impl : QueryImpl base ProbComp)
    (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (psi : ZMod q)
    (original : NativeKeySwitch.Key q (2^(c+2)) levels) (shape : Cfg → Skeleton)
    (result : (Fin levels → Digest) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (program parameters enc psi original)).run (CheckpointExecution.empty shape))) :
    HonestKeyQueryReceipt.Receipt parameters enc psi original result.1 result.2.hash.log ∧
      CachedHashHandler.Coherent result.2.hash ∧ RecordedCheckpointQueries.Sound shape result.2 ∧
      CheckpointExecution.Audited enc dummy shape result.2 ∧
      ∀ nextShape : Cfg → Skeleton, CheckpointShapeTransport.Compatible shape nextShape result.2.checkpoints := by
  rw [program,simulateQ_map,StateT.run_map,support_map,Set.mem_image] at supported
  obtain ⟨built, present, equal⟩ := supported
  subst result
  exact ⟨HonestKeyQueryReceipt.of_setup impl parameters enc dummy psi original shape
    (CheckpointExecution.empty shape) built present,
    HonestSetupInitialHistory.initialized impl enc dummy shape parameters
      (HonestRecordedEvaluationKey.table parameters psi original) built present⟩

end
end FormalProof4FHE.HasteBoots.HonestKeySetupReceipts
