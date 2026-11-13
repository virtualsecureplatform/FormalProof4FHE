module
public import FormalProof4FHE.HasteBoots.AmbientMatrixSource
public import FormalProof4FHE.HasteBoots.RectangularSubclaimSourceLayout
@[expose] public section

/-! Rectangular source words in one heterogeneous recorded history. Packing
and code-symbol widths are independent; immutable owners and the final audited
collision event have the same meaning as in the square source interface. -/
namespace FormalProof4FHE.HasteBoots.AmbientRectangularSource
open BinaryTree MerkleTreeMultiExtractability
noncomputable section
variable {F Cfg Input Digest : Type} [Field F] [DecidableEq Digest]
  {front suffix packingWidth codeWidth degree height : ℕ}

def word (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag) :
    Fin (2^height) → (Fin (2^front) × Fin packingWidth) → Fin codeWidth → F :=
  NativeColumnLayout.expandedWord
    (AuthenticatedColumnChecks.frozenWord (leftCount := 2^front) (width := packingWidth) (block := codeWidth)
      enc dummy (fun _ : Cfg => height) tag (AmbientMatrixSource.localSnapshot heights tag saved))

variable [DecidableEq F]

def source (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ degree*codeWidth) (radius : ℕ)
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag) :
    MatrixFold.Cube (front+suffix) → Fin packingWidth → F :=
  RectangularSubclaimSourceLayout.decodedSource domain capacity radius (word enc dummy heights tag saved)

omit [DecidableEq F] in
/-- Native whole-column addresses retain row packing separately from the
code-symbol coordinate within that row. -/
theorem word_eq_of_stable (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Cfg) (geometry : heights tag = height)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (stable : MerklePayloadCheckpoints.StableAt enc dummy (AmbientMatrixSource.Shape heights) state.checkpoints state.hash.log)
    (first second : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (firstRecorded : ⟨tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root) :
    word (front := front) (packingWidth := packingWidth) (codeWidth := codeWidth) (height := height) enc dummy heights tag first =
      word enc dummy heights tag second := by
  subst height
  funext position row coordinate
  have payloads := MerklePayloadCheckpoints.same_root_payloads enc dummy (AmbientMatrixSource.Shape heights)
    state.checkpoints state.hash.log stable tag first second firstRecorded secondRecorded sameRoot
    (SkeletonLeafIndex.perfectEquiv (heights tag) position)
  exact congrArg (fun payload : Option (List F) =>
    NativeColumnLayout.unpackPayload (((2^front)*packingWidth)*codeWidth) (payload.getD [])
      (NativeColumnLayout.payloadAddress (finProdFinEquiv row) coordinate)) payloads

variable [DecidableEq Input]

/-- Complete rectangular decoded sources agree under the same recorded-root
and audited-history exclusion, with no separate rectangular collision charge. -/
theorem source_eq_or_bad (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Cfg) (geometry : heights tag = height)
    (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ degree*codeWidth) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (first second : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (firstRecorded : ⟨tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root) :
    source (front := front) (packingWidth := packingWidth) enc dummy heights domain capacity radius tag first =
      source enc dummy heights domain capacity radius tag second ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  cases clear : state.failed with
  | false =>
    left
    exact congrArg (RectangularSubclaimSourceLayout.decodedSource domain capacity radius)
      (word_eq_of_stable enc dummy heights tag geometry state (audited.2 clear) first second firstRecorded secondRecorded sameRoot)
  | true => exact Or.inr (Or.inl clear)

omit [DecidableEq Input] [DecidableEq F] in
theorem word_square (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag) :
    word (front := front) (packingWidth := packingWidth) (codeWidth := packingWidth) (height := height) enc dummy heights tag saved =
      AmbientMatrixSource.word (front := front) (b := packingWidth) (height := height) enc dummy heights tag saved := rfl

omit [DecidableEq Input] in
theorem source_square (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (domain : Fin (2^height) ↪ F) (capacity : 2^suffix ≤ degree*packingWidth) (radius : ℕ)
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest heights tag) :
    source (front := front) (packingWidth := packingWidth) enc dummy heights domain capacity radius tag saved =
      AmbientMatrixSource.source (front := front) enc dummy heights domain capacity radius tag saved := rfl

end
end FormalProof4FHE.HasteBoots.AmbientRectangularSource
