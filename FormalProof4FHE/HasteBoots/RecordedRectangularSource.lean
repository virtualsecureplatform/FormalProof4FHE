module
public import FormalProof4FHE.HasteBoots.AmbientRectangularSource
public import FormalProof4FHE.HasteBoots.RecordedPaddedSource
@[expose] public section

/-! One query-independent source decoder with independent row-packing and
code-symbol widths. The recorded owner, physical domain and analysis radius
remain fixed across all logical presentations and later queries. -/
namespace FormalProof4FHE.HasteBoots.RecordedRectangularSource
open BinaryTree
noncomputable section

structure Parameters (F Cfg : Type) [Field F] (H : Cfg → ℕ) (packingWidth codeWidth : ℕ) where
  front : ℕ
  suffix : ℕ
  degree : ℕ
  tag : Cfg
  domain : Fin (2^H tag) ↪ F
  capacity : 2^suffix ≤ degree*codeWidth
  radius : ℕ

variable {F Cfg Input Digest : Type} [Field F] [DecidableEq F] [DecidableEq Digest]
  {H : Cfg → ℕ} {packingWidth codeWidth n m : ℕ}

abbrev Owner (p : Parameters F Cfg H packingWidth codeWidth) :=
  AmbientMatrixSource.Snapshot Input Digest H p.tag

/-- The extracted table keeps packed rows and original message columns; only
its physical encoding uses codeWidth. -/
def decoded (p : Parameters F Cfg H packingWidth codeWidth)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (owner : Owner (Input := Input) (Digest := Digest) p) :
    Fin (2^p.front) → Fin (2^p.suffix) → Fin packingWidth → F :=
  RectangularMatrixOpeningKernel.extract p.domain p.capacity p.radius
    (AmbientRectangularSource.word (front := p.front) (packingWidth := packingWidth) (codeWidth := codeWidth)
      (height := H p.tag) enc dummy H p.tag owner)

def logical (p : Parameters F Cfg H packingWidth codeWidth)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (logical : ℕ)
    (owner : Owner (Input := Input) (Digest := Digest) p) : MatrixFold.Cube logical → Fin packingWidth → F :=
  PaddedSourceAddress.logical logical (decoded p enc dummy owner)

theorem padded_eq_logical (p : Parameters F Cfg H packingWidth codeWidth)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (padding : ℕ) (dimensions : padding+n = p.front+p.suffix)
    (owner : Owner (Input := Input) (Digest := Digest) p) :
    QueryHighZeroPadding.source padding (QueryReindex.source dimensions
      (AmbientRectangularSource.source (front := p.front) (packingWidth := packingWidth)
        enc dummy H p.domain p.capacity p.radius p.tag owner)) = logical p enc dummy n owner :=
  RectangularSubclaimSourceLayout.padded_decoded_source padding dimensions p.domain p.capacity p.radius _

theorem logical_same_address (p : Parameters F Cfg H packingWidth codeWidth)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (owner : Owner (Input := Input) (Digest := Digest) p)
    (left : MatrixFold.Cube n) (right : MatrixFold.Cube m)
    (address : (FlatMatrixFold.index n left).val = (FlatMatrixFold.index m right).val) :
    logical p enc dummy n owner left = logical p enc dummy m owner right :=
  PaddedSourceAddress.same_address _ left right address

variable [DecidableEq Input]

theorem decoded_eq_or_bad (p : Parameters F Cfg H packingWidth codeWidth)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) state)
    (first second : Owner (Input := Input) (Digest := Digest) p)
    (firstRecorded : ⟨p.tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨p.tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root) :
    decoded p enc dummy first = decoded p enc dummy second ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  cases clear : state.failed with
  | false =>
    left
    exact congrArg (RectangularMatrixOpeningKernel.extract p.domain p.capacity p.radius)
      (AmbientRectangularSource.word_eq_of_stable enc dummy H p.tag rfl state (audited.2 clear)
        first second firstRecorded secondRecorded sameRoot)
  | true => exact Or.inr (Or.inl clear)

theorem logical_eq_or_bad (p : Parameters F Cfg H packingWidth codeWidth)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (logical : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) state)
    (first second : Owner (Input := Input) (Digest := Digest) p)
    (firstRecorded : ⟨p.tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨p.tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root) :
    RecordedRectangularSource.logical p enc dummy logical first = RecordedRectangularSource.logical p enc dummy logical second ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  rcases decoded_eq_or_bad p enc dummy state audited first second firstRecorded secondRecorded sameRoot with equal | bad
  · exact Or.inl (congrArg (PaddedSourceAddress.logical logical) equal)
  · exact Or.inr bad

omit [DecidableEq Input] in
/-- Embed existing square source descriptors without changing their decoder. -/
def ofSquare (p : RecordedPaddedSource.Parameters F Cfg H packingWidth) : Parameters F Cfg H packingWidth packingWidth :=
  ⟨p.front,p.suffix,p.degree,p.tag,p.domain,p.capacity,p.radius⟩

omit [DecidableEq Input] in
theorem decoded_ofSquare (p : RecordedPaddedSource.Parameters F Cfg H packingWidth)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (owner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) p) :
    decoded (ofSquare p) enc dummy owner = RecordedPaddedSource.decoded p enc dummy owner := rfl

omit [DecidableEq Input] in
theorem logical_ofSquare (p : RecordedPaddedSource.Parameters F Cfg H packingWidth)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (logical : ℕ)
    (owner : RecordedPaddedSource.Owner (Input := Input) (Digest := Digest) p) :
    RecordedRectangularSource.logical (ofSquare p) enc dummy logical owner = RecordedPaddedSource.logical p enc dummy logical owner := rfl

end
end FormalProof4FHE.HasteBoots.RecordedRectangularSource
