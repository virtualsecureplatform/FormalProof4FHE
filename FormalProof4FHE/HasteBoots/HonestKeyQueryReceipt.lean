module
public import FormalProof4FHE.HasteBoots.HonestMatrixSetupTrace
public import FormalProof4FHE.HasteBoots.HonestEvaluationKeyTranscript
@[expose] public section

/-! Factual honest setup receipts consist only of actual Merkle query/response
pairs, their returned roots, and public matrix descriptors. -/
namespace FormalProof4FHE.HasteBoots.HonestKeyQueryReceipt
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {q c levels : ℕ} [Fact q.Prime]
  {Cfg Input Digest : Type} {H : Cfg → ℕ}

def Receipt (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (original : NativeKeySwitch.Key q (2^(c+2)) levels) (roots : Fin levels → Digest)
    (log : MerkleTreeExtractor.QueryLog Input Digest) : Prop :=
  ∃ labels : (level : Fin levels) → FullData Digest (Skeleton.perfect (H (parameters level).tag)),
    (∀ level, roots level = (labels level).getRootValue) ∧
    ∀ level, ∀ entry ∈ HonestMerkleTranscript.queries enc (HonestRecordedMatrix.leaves (parameters level)
      (HonestRecordedEvaluationKey.table parameters psi original level)) (labels level), entry ∈ log

/-- Public descriptor equality transports the receipt, including its typed labels. -/
theorem parameters_congr
    (left right : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (same : ∀ level, left level = right level)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (original : NativeKeySwitch.Key q (2^(c+2)) levels) (roots : Fin levels → Digest)
    (log : MerkleTreeExtractor.QueryLog Input Digest)
    (receipt : Receipt left enc psi original roots log) : Receipt right enc psi original roots log := by
  have equal : left = right := funext same
  cases equal
  exact receipt

/-- Existing hash observations survive chronological extension. -/
theorem mono (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (psi : ZMod q)
    (original : NativeKeySwitch.Key q (2^(c+2)) levels) (roots : Fin levels → Digest)
    (before after : MerkleTreeExtractor.QueryLog Input Digest) (growing : before <+: after)
    (receipt : Receipt parameters enc psi original roots before) : Receipt parameters enc psi original roots after := by
  obtain ⟨labels, root, logged⟩ := receipt
  exact ⟨labels, root, fun level entry member => growing.sublist.subset (logged level entry member)⟩

/-- Unique-decoding distance is unchanged by equality of public descriptors,
including the dependent column domain. -/
theorem margin_congr (left right : RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (same : left = right)
    (margin : 2*left.radius < Code.minDist (BlockCode.code left.domain left.degree 4 :
      Set (Fin (2^H left.tag) → Fin 4 → ZMod q))) :
    2*right.radius < Code.minDist (BlockCode.code right.domain right.degree 4 :
      Set (Fin (2^H right.tag) → Fin 4 → ZMod q)) := by
  cases same
  exact margin

variable [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

/-- A supported actual setup execution constructs the receipt; no source-value
or transform equality certificate is supplied. -/
theorem of_setup {ι : Type} {base : OracleSpec ι} (impl : QueryImpl base ProbComp)
    (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (psi : ZMod q)
    (original : NativeKeySwitch.Key q (2^(c+2)) levels) (shape : Cfg → Skeleton)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (result : ((level : Fin levels) → FullData Digest (Skeleton.perfect (H (parameters level).tag))) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (HonestMatrixSetupTrace.program enc parameters (HonestRecordedEvaluationKey.table parameters psi original))).run initial)) :
    Receipt parameters enc psi original (fun level => (result.1 level).getRootValue) result.2.hash.log :=
  ⟨result.1, fun _ => rfl, HonestMatrixSetupTrace.queries_logged impl enc dummy shape parameters
    (HonestRecordedEvaluationKey.table parameters psi original) initial result supported⟩

end
end FormalProof4FHE.HasteBoots.HonestKeyQueryReceipt
