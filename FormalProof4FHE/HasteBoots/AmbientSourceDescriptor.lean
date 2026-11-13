module
public import FormalProof4FHE.HasteBoots.RecordedPaddedSource
@[expose] public section

/-! Public physical-decoder descriptors for unpadded ambient source uses.
The local hash height is checked against its own ambient tag; unrelated
checkpoint heights remain arbitrary. -/
namespace FormalProof4FHE.HasteBoots.AmbientSourceDescriptor
noncomputable section
variable {F Cfg Input Digest : Type} [Field F] [DecidableEq F] [DecidableEq Digest]
  {front suffix b degree height n : ℕ}

/-- Normalize a local domain to the actual height of its ambient context.
This packages public decoder metadata, never a decoded source-value equality. -/
def parameters (heights : Cfg → ℕ) (tag : Cfg) (geometry : heights tag = height)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ degree*b) (radius : ℕ) :
    RecordedPaddedSource.Parameters F Cfg heights b :=
  ⟨front,suffix,degree,tag,
    (finCongr (congrArg (2^·) geometry)).toEmbedding.trans domain,capacity,radius⟩

/-- The actual ambient source is the canonical native-address view of that
same owner's fixed physical decoder, including its actual decoding radius. -/
theorem original (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Cfg) (geometry : heights tag = height)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ degree*b) (radius : ℕ)
    (dimensions : n = front+suffix)
    (owner : AmbientMatrixSource.Snapshot Input Digest heights tag) :
    QueryReindex.source dimensions
      (AmbientMatrixSource.source (front := front) enc dummy heights domain capacity radius tag owner) =
    RecordedPaddedSource.logical (parameters (front := front) heights tag geometry domain capacity radius) enc dummy n owner := by
  subst height
  funext cell lane
  change SubclaimSourceLayout.lookup
    (MatrixOpeningSecurity.extract domain capacity radius
      (AmbientMatrixSource.word (front := front) enc dummy heights tag owner))
    (FlatMatrixFold.index (front+suffix) (dimensions ▸ cell)).val lane = _
  rw [PaddedSourceAddress.index_transport]
  rfl

variable [DecidableEq Input] {heights : Cfg → ℕ}

/-- Matching complete public descriptors and retained roots identify the two
original decoders outside the existing final exception. No alias loss is added. -/
theorem associated_logical_eq_or_bad
    (firstParameters secondParameters : RecordedPaddedSource.Parameters F Cfg heights b)
    (associated : firstParameters = secondParameters)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (n : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (first : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) firstParameters)
    (second : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) secondParameters)
    (firstRecorded : ⟨firstParameters.tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨secondParameters.tag,second⟩ ∈ state.checkpoints.checkpoints)
    (sameRoot : first.root = second.root) :
    RecordedPaddedSource.logical firstParameters enc dummy n first =
      RecordedPaddedSource.logical secondParameters enc dummy n second ∨
    CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  subst secondParameters
  exact RecordedPaddedSource.logical_eq_or_bad firstParameters enc dummy n state audited
    first second firstRecorded secondRecorded sameRoot

end
end FormalProof4FHE.HasteBoots.AmbientSourceDescriptor
