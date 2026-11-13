module
public import FormalProof4FHE.HasteBoots.HonestRecordedMatrix
@[expose] public section

/-! Honest matrix recovery from actual setup queries in a later source snapshot.
The snapshot may be recorded after setup, at the native stage's own geometry. -/
namespace FormalProof4FHE.HasteBoots.HonestMatrixTranscript
open BinaryTree OracleSpec OracleComp
noncomputable section
variable {F Cfg Input Digest : Type} [Field F] [DecidableEq Digest]
  {H : Cfg → ℕ} {b : ℕ}

theorem word (p : RecordedPaddedSource.Parameters F Cfg H b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (table : RecordedPaddedSource.PhysicalMatrix p)
    (labels : FullData Digest (Skeleton.perfect (H p.tag)))
    (saved : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) p)
    (root : saved.root = labels.getRootValue)
    (included : ∀ entry ∈ HonestMerkleTranscript.queries enc (HonestRecordedMatrix.leaves p table) labels,
      entry ∈ saved.cumulativeLog)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn saved.cumulativeLog) :
    AmbientMatrixSource.word (front := p.front) (b := b) (height := H p.tag)
      enc dummy H p.tag saved = HonestRecordedMatrix.encoded p table := by
  funext position row channel
  have recovered := HonestMerkleTranscript.word_recovered enc dummy [] (H p.tag) (HonestRecordedMatrix.leaves p table)
    labels
    saved.cumulativeLog injective
    included position
  rw [← root] at recovered
  have value : MerkleAvailability.word enc dummy [] (H p.tag)
      saved.cumulativeLog saved.root position =
      HonestRecordedMatrix.column p table position := by
    simpa only [HonestRecordedMatrix.leaves,LeafData.get_ofFun,Equiv.symm_apply_apply] using recovered
  change NativeColumnLayout.unpackPayload (((2^p.front)*b)*b)
    (MerkleAvailability.word enc dummy [] (H p.tag) saved.cumulativeLog
      saved.root position)
    (NativeColumnLayout.payloadAddress (finProdFinEquiv row) channel) = _
  rw [value]
  simp only [HonestRecordedMatrix.column,NativeColumnLayout.unpack_packPayload,NativeColumnLayout.payloadAddress,
    Equiv.symm_apply_apply]

variable [DecidableEq F] [NeZero b]

/-- The fixed query-independent matrix decoder returns the committed setup
matrix, for any admitted unique radius, not only radius zero. -/
theorem decoded (p : RecordedPaddedSource.Parameters F Cfg H b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (table : RecordedPaddedSource.PhysicalMatrix p)
    (labels : FullData Digest (Skeleton.perfect (H p.tag)))
    (saved : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) p)
    (root : saved.root = labels.getRootValue)
    (included : ∀ entry ∈ HonestMerkleTranscript.queries enc (HonestRecordedMatrix.leaves p table) labels,
      entry ∈ saved.cumulativeLog)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn saved.cumulativeLog)
    (enough : p.degree ≤ 2^H p.tag)
    (margin : 2*p.radius < Code.minDist (BlockCode.code p.domain p.degree b :
      Set (Fin (2^H p.tag) → Fin b → F))) :
    RecordedPaddedSource.decoded p enc dummy saved = table := by
  unfold RecordedPaddedSource.decoded
  rw [word p enc dummy table labels saved root included injective]
  exact MatrixOpeningCompleteness.extract p.domain (by simpa only [Fintype.card_fin] using enough)
    p.capacity p.radius margin table

theorem logical (p : RecordedPaddedSource.Parameters F Cfg H b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (table : RecordedPaddedSource.PhysicalMatrix p)
    (labels : FullData Digest (Skeleton.perfect (H p.tag)))
    (saved : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) p)
    (root : saved.root = labels.getRootValue)
    (included : ∀ entry ∈ HonestMerkleTranscript.queries enc (HonestRecordedMatrix.leaves p table) labels,
      entry ∈ saved.cumulativeLog)
    (injective : MerkleTreeExtractor.ResponseInjectiveOn saved.cumulativeLog)
    (enough : p.degree ≤ 2^H p.tag)
    (margin : 2*p.radius < Code.minDist (BlockCode.code p.domain p.degree b :
      Set (Fin (2^H p.tag) → Fin b → F))) (arity : ℕ) :
    RecordedPaddedSource.logical p enc dummy arity saved =
      PaddedSourceAddress.logical arity table := by
  unfold RecordedPaddedSource.logical
  rw [decoded p enc dummy table labels saved root included injective enough margin]

end
end FormalProof4FHE.HasteBoots.HonestMatrixTranscript
