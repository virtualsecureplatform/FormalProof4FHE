module
public import FormalProof4FHE.HasteBoots.PackedPBSOriginalReferences
public import FormalProof4FHE.HasteBoots.HonestControlKeyTable
public import FormalProof4FHE.HasteBoots.HonestMatrixSetupTrace
public import FormalProof4FHE.HasteBoots.HonestSetupInitialHistory
@[expose] public section

/-! Hash-only honest control-key setup returns actual commitment roots and
factual query receipts; native stages record source checkpoints later. -/
namespace FormalProof4FHE.HasteBoots.HonestControlKeySetup
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {q cells lanes rows levels : ℕ} [Fact q.Prime]
  {Cfg Input Digest : Type} {H : Cfg → ℕ}

/-- The actual root/label/query record of every honest control-key matrix. -/
def Receipt (parameters : Fin (2*levels) → RecordedPaddedSource.Parameters (ZMod q) Cfg H (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := levels))
    (roots : Fin (2*levels) → Digest) (log : MerkleTreeExtractor.QueryLog Input Digest) : Prop :=
  ∃ labels : (slot : Fin (2*levels)) → FullData Digest (Skeleton.perfect (H (parameters slot).tag)),
    (∀ slot, roots slot = (labels slot).getRootValue) ∧
    ∀ slot, ∀ entry ∈ HonestMerkleTranscript.queries enc
      (HonestRecordedMatrix.leaves (parameters slot) (HonestControlKeyTable.table parameters psi controls slot))
      (labels slot), entry ∈ log

/-- Setup runs the shared leaf/node hash oracle without source annotations. -/
def program {ι : Type} {base : OracleSpec ι}
    (parameters : Fin (2*levels) → RecordedPaddedSource.Parameters (ZMod q) Cfg H (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := levels)) :
    OracleComp (CheckpointExecution.Spec base Cfg Input Digest) (Fin (2*levels) → Digest) :=
  (fun labels slot => (labels slot).getRootValue) <$>
    HonestMatrixSetupTrace.program enc parameters (HonestControlKeyTable.table parameters psi controls)

/-- Install the computed control-key roots in the actual caller family. -/
def withKeys (family : PackedPBSOriginalReferences.Family (2*levels)) (roots : Fin (2*levels) → NativeRootMessage.Digest) :
    PackedPBSOriginalReferences.Family (2*levels) := {family with keys := roots}

/-- Factual receipts retain chronological setup hashes in later logs. -/
theorem mono (parameters : Fin (2*levels) → RecordedPaddedSource.Parameters (ZMod q) Cfg H (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := levels))
    (roots : Fin (2*levels) → Digest) (before after : MerkleTreeExtractor.QueryLog Input Digest)
    (growing : before <+: after) (receipt : Receipt parameters enc psi controls roots before) :
    Receipt parameters enc psi controls roots after := by
  obtain ⟨labels,root,logged⟩ := receipt
  exact ⟨labels,root,fun slot entry member => growing.sublist.subset (logged slot entry member)⟩

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- An actual supported setup establishes the receipt and all initial history
invariants, including compatibility with every later extraction geometry. -/
theorem initialized {ι : Type} {base : OracleSpec ι} (impl : QueryImpl base ProbComp)
    (parameters : Fin (2*levels) → RecordedPaddedSource.Parameters (ZMod q) Cfg H (2^lanes))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (psi : ZMod q)
    (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := levels))
    (shape : Cfg → Skeleton)
    (result : (Fin (2*levels) → Digest) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (program parameters enc psi controls)).run (CheckpointExecution.empty shape))) :
    Receipt parameters enc psi controls result.1 result.2.hash.log ∧
      CachedHashHandler.Coherent result.2.hash ∧ RecordedCheckpointQueries.Sound shape result.2 ∧
      CheckpointExecution.Audited enc dummy shape result.2 ∧
      ∀ nextShape : Cfg → Skeleton, CheckpointShapeTransport.Compatible shape nextShape result.2.checkpoints := by
  rw [program,simulateQ_map,StateT.run_map,support_map,Set.mem_image] at supported
  obtain ⟨built,present,equal⟩ := supported
  subst result
  exact ⟨⟨built.1,fun _ => rfl,HonestMatrixSetupTrace.queries_logged impl enc dummy shape parameters
      (HonestControlKeyTable.table parameters psi controls) (CheckpointExecution.empty shape) built present⟩,
    HonestSetupInitialHistory.initialized impl enc dummy shape parameters
      (HonestControlKeyTable.table parameters psi controls) built present⟩

end
end FormalProof4FHE.HasteBoots.HonestControlKeySetup
