module
public import FormalProof4FHE.HasteBoots.PaddedSourceAddress
public import FormalProof4FHE.HasteBoots.AmbientMatrixSource
@[expose] public section

/-! One decoded matrix and native-address interpretation per retained root.
The descriptor fixes context, dimensions, domain, degree and decoder radius.
Recorded aliases share this interpretation outside the existing final Bad;
digest equality alone, or independent decoder choices, is insufficient. -/
namespace FormalProof4FHE.HasteBoots.RecordedPaddedSource
open BinaryTree
noncomputable section

structure Parameters (F Cfg : Type) [Field F] (heights : Cfg → ℕ) (b : ℕ) where
  front : ℕ
  suffix : ℕ
  degree : ℕ
  tag : Cfg
  domain : Fin (2^heights tag) ↪ F
  capacity : 2^suffix ≤ degree*b
  radius : ℕ

variable {F Cfg Input Digest : Type} [Field F] [DecidableEq F] [DecidableEq Digest]
  {heights : Cfg → ℕ} {b n m : ℕ}

abbrev Owner (p : Parameters F Cfg heights b) :=
  AmbientMatrixSource.Snapshot Input Digest heights p.tag

abbrev PhysicalMatrix (p : Parameters F Cfg heights b) :=
  Fin (2^p.front) → Fin (2^p.suffix) → Fin b → F

/-- Decode once from this immutable owner's available word, using fixed public
parameters; no query, sumcheck claim or logical padding is an input. -/
def decoded (p : Parameters F Cfg heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (owner : Owner (Input := Input) (Digest := Digest) p) : PhysicalMatrix p :=
  MatrixOpeningSecurity.extract p.domain p.capacity p.radius
    (AmbientMatrixSource.word (front := p.front) (b := b) (height := heights p.tag) enc dummy heights p.tag owner)

def logical (p : Parameters F Cfg heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (n : ℕ)
    (owner : Owner (Input := Input) (Digest := Digest) p) : MatrixFold.Cube n → Fin b → F :=
  PaddedSourceAddress.logical n (decoded p enc dummy owner)

/-- The logical source in each padded verifier is this canonical address view. -/
theorem padded_eq_logical (p : Parameters F Cfg heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (padding : ℕ) (dimensions : padding+n = p.front+p.suffix)
    (owner : Owner (Input := Input) (Digest := Digest) p) :
    QueryHighZeroPadding.source padding (QueryReindex.source dimensions
      (AmbientMatrixSource.source (front := p.front) enc dummy heights p.domain p.capacity p.radius p.tag owner)) =
    logical p enc dummy n owner :=
  PaddedSourceAddress.padded_decoded_source padding dimensions p.domain p.capacity p.radius _

/-- Native address agreement is the only logical-view equality required after
one physical matrix has been fixed. -/
theorem logical_same_address (p : Parameters F Cfg heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (owner : Owner (Input := Input) (Digest := Digest) p)
    (left : MatrixFold.Cube n) (right : MatrixFold.Cube m)
    (address : (FlatMatrixFold.index n left).val = (FlatMatrixFold.index m right).val) :
    logical p enc dummy n owner left = logical p enc dummy m owner right :=
  PaddedSourceAddress.same_address _ left right address

variable [DecidableEq Input]

/-- Retained aliases have one physical decoded matrix outside the same final
exception. Keeping the radius fixed avoids inconsistent decoder fallbacks. -/
theorem decoded_eq_or_bad (p : Parameters F Cfg heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (first second : Owner (Input := Input) (Digest := Digest) p)
    (firstRecorded : ⟨p.tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨p.tag,second⟩ ∈ state.checkpoints.checkpoints)
    (sameRoot : first.root = second.root) :
    decoded p enc dummy first = decoded p enc dummy second ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  cases failed : state.failed with
  | false =>
    left
    exact congrArg (MatrixOpeningSecurity.extract p.domain p.capacity p.radius)
      (AmbientMatrixSource.word_eq_of_stable enc dummy heights p.tag rfl state (audited.2 failed)
        first second firstRecorded secondRecorded sameRoot)
  | true => exact Or.inr (Or.inl failed)

/-- An original owner selected after the run gives the same logical table as
any other recorded alias with this descriptor and root. -/
theorem logical_eq_or_bad (p : Parameters F Cfg heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (n : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (first second : Owner (Input := Input) (Digest := Digest) p)
    (firstRecorded : ⟨p.tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨p.tag,second⟩ ∈ state.checkpoints.checkpoints)
    (sameRoot : first.root = second.root) :
    logical p enc dummy n first = logical p enc dummy n second ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  rcases decoded_eq_or_bad p enc dummy state audited first second firstRecorded secondRecorded sameRoot with same | bad
  · exact Or.inl (congrArg (PaddedSourceAddress.logical n) same)
  · exact Or.inr bad

/-- Different logical presentations of recorded aliases agree at every shared
native address, under the inherited final collision exclusion. -/
theorem padded_same_address_or_bad (p : Parameters F Cfg heights b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (leftPadding rightPadding : ℕ)
    (leftDimensions : leftPadding+n = p.front+p.suffix) (rightDimensions : rightPadding+m = p.front+p.suffix)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (first second : Owner (Input := Input) (Digest := Digest) p)
    (firstRecorded : ⟨p.tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨p.tag,second⟩ ∈ state.checkpoints.checkpoints)
    (sameRoot : first.root = second.root)
    (left : MatrixFold.Cube n) (right : MatrixFold.Cube m)
    (address : (FlatMatrixFold.index n left).val = (FlatMatrixFold.index m right).val) :
    QueryHighZeroPadding.source leftPadding (QueryReindex.source leftDimensions
      (AmbientMatrixSource.source (front := p.front) enc dummy heights p.domain p.capacity p.radius p.tag first)) left =
    QueryHighZeroPadding.source rightPadding (QueryReindex.source rightDimensions
      (AmbientMatrixSource.source (front := p.front) enc dummy heights p.domain p.capacity p.radius p.tag second)) right ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  rw [padded_eq_logical,padded_eq_logical]
  rcases logical_eq_or_bad p enc dummy n state audited first second firstRecorded secondRecorded sameRoot with same | bad
  · left
    rw [same]
    exact logical_same_address p enc dummy second left right address
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.RecordedPaddedSource
