module
public import FormalProof4FHE.HasteBoots.RecordedSourceCoherence
public import FormalProof4FHE.HasteBoots.CheckpointShapeTransport
@[expose] public section

/-! A fixed-height matrix source inside a heterogeneous shared checkpoint state.
Only its own recorded context needs that height; other histories are retained. -/
namespace FormalProof4FHE.HasteBoots.AmbientMatrixSource
open BinaryTree MerkleTreeMultiExtractability
open InteractiveAuthenticatedOpening
noncomputable section
variable {F Cfg Input Digest : Type} [Field F] [DecidableEq Digest]
  {front suffix b m height : ℕ}

abbrev Shape (heights : Cfg → ℕ) := fun cfg => Skeleton.perfect (heights cfg)
abbrev Snapshot (Input Digest : Type) (heights : Cfg → ℕ) (tag : Cfg) :=
  Checkpoint Input Digest (MerklePayloadCheckpoints.configuration (Shape heights)) tag

/-- A source view copies only this immutable checkpoint's root/log. The actual
ambient state and all its other checkpoints remain untouched. -/
def localSnapshot (heights : Cfg → ℕ) (tag : Cfg) (saved : Snapshot Input Digest heights tag) :
    RecordedSourceCoherence.Snapshot Input Digest Cfg height tag :=
  ⟨saved.root,saved.cumulativeLog⟩

def word (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Cfg) (saved : Snapshot Input Digest heights tag) :
    Fin (2^height) → (Fin (2^front) × Fin b) → Fin b → F :=
  InteractiveAuthenticatedOpening.word enc dummy (fun _ : Cfg => height) tag (localSnapshot heights tag saved)

variable [DecidableEq F]

def source (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (tag : Cfg) (saved : Snapshot Input Digest heights tag) : MatrixFold.Cube (front+suffix) → Fin b → F :=
  SubclaimSourceLayout.decodedSource domain capacity radius (word enc dummy heights tag saved)

omit [DecidableEq F] in
/-- Stable ambient extraction compares sources at a matching local height. -/
theorem word_eq_of_stable (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Cfg) (geometry : heights tag = height)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (Shape heights))
    (stable : MerklePayloadCheckpoints.StableAt enc dummy (Shape heights) state.checkpoints state.hash.log)
    (first second : Snapshot Input Digest heights tag)
    (firstRecorded : ⟨tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root) :
    word (front := front) (b := b) (height := height) enc dummy heights tag first = word enc dummy heights tag second := by
  subst height
  funext position row lane
  have payloads := MerklePayloadCheckpoints.same_root_payloads enc dummy (Shape heights)
    state.checkpoints state.hash.log stable tag first second firstRecorded secondRecorded sameRoot
    (SkeletonLeafIndex.perfectEquiv (heights tag) position)
  exact congrArg (fun payload : Option (List F) =>
    NativeColumnLayout.unpackPayload (((2^front)*b)*b) (payload.getD [])
      (NativeColumnLayout.payloadAddress (finProdFinEquiv row) lane)) payloads

theorem source_eq_of_stable (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Cfg) (geometry : heights tag = height)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (Shape heights))
    (stable : MerklePayloadCheckpoints.StableAt enc dummy (Shape heights) state.checkpoints state.hash.log)
    (first second : Snapshot Input Digest heights tag)
    (firstRecorded : ⟨tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root) :
    source (front := front) enc dummy heights domain capacity radius tag first = source enc dummy heights domain capacity radius tag second :=
  congrArg (SubclaimSourceLayout.decodedSource domain capacity radius)
    (word_eq_of_stable enc dummy heights tag geometry state stable first second firstRecorded secondRecorded sameRoot)

variable [DecidableEq Input]

/-- Original owners may be selected after execution; their sources agree
outside the same ambient final exception, regardless of unrelated helper heights. -/
theorem source_eq_or_bad (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Cfg) (geometry : heights tag = height)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (Shape heights) state)
    (first second : Snapshot Input Digest heights tag)
    (firstRecorded : ⟨tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root) :
    source (front := front) enc dummy heights domain capacity radius tag first = source enc dummy heights domain capacity radius tag second ∨
      CheckpointCollision.Bad (Shape heights) state := by
  cases clear : state.failed with
  | false => exact Or.inl (source_eq_of_stable enc dummy heights tag geometry domain capacity radius state
      (audited.2 clear) first second firstRecorded secondRecorded sameRoot)
  | true => exact Or.inr (Or.inl clear)

end
end FormalProof4FHE.HasteBoots.AmbientMatrixSource
