module
public import FormalProof4FHE.HasteBoots.RecordedPayloadCoherence
public import FormalProof4FHE.HasteBoots.SubclaimSourceLayout
public import FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
@[expose] public section

/-! Recorded source coherence with different tree heights and PCS layouts in
one shared history. Each interpretation keeps its own fixed parameters. -/
namespace FormalProof4FHE.HasteBoots.HeterogeneousSourceCoherence
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability
open InteractiveAuthenticatedOpening
noncomputable section
variable {F Cfg Input Digest : Type} [Field F] [DecidableEq F] [DecidableEq Digest]
  {front suffix b m : ℕ}

abbrev Snapshot (Input Digest Cfg : Type) (heights : Cfg → ℕ) (tag : Cfg) :=
  Checkpoint Input Digest (MerklePayloadCheckpoints.configuration (fun cfg => Skeleton.perfect (heights cfg))) tag

omit [DecidableEq F] in
theorem word_eq_of_stable (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (stable : MerklePayloadCheckpoints.StableAt enc dummy (fun cfg => Skeleton.perfect (heights cfg)) state.checkpoints state.hash.log)
    (tag : Cfg) (first second : Snapshot Input Digest Cfg heights tag)
    (firstRecorded : ⟨tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root) :
    word (leftCount := 2^front) (b := b) enc dummy heights tag first = word enc dummy heights tag second := by
  funext position row lane
  have payloads := MerklePayloadCheckpoints.same_root_payloads enc dummy (fun cfg => Skeleton.perfect (heights cfg))
    state.checkpoints state.hash.log stable tag first second firstRecorded secondRecorded sameRoot
    (SkeletonLeafIndex.perfectEquiv (heights tag) position)
  exact congrArg (fun payload : Option (List F) => NativeColumnLayout.unpackPayload (((2^front)*b)*b) (payload.getD [])
    (NativeColumnLayout.payloadAddress (finProdFinEquiv row) lane)) payloads

variable [DecidableEq Input]

omit [DecidableEq F] in
theorem word_eq_or_bad (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (heights : Cfg → ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (audited : CheckpointExecution.Audited enc dummy (fun cfg => Skeleton.perfect (heights cfg)) state)
    (tag : Cfg) (first second : Snapshot Input Digest Cfg heights tag)
    (firstRecorded : ⟨tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root) :
    word (leftCount := 2^front) (b := b) enc dummy heights tag first = word enc dummy heights tag second ∨
      CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) state := by
  cases failed : state.failed with
  | false => exact Or.inl (word_eq_of_stable enc dummy heights state (audited.2 failed) tag first second firstRecorded secondRecorded sameRoot)
  | true => exact Or.inr (Or.inl failed)

theorem source_eq_or_bad (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (heights : Cfg → ℕ)
    (tag : Cfg) (domain : Fin (2^heights tag) ↪ F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (audited : CheckpointExecution.Audited enc dummy (fun cfg => Skeleton.perfect (heights cfg)) state)
    (first second : Snapshot Input Digest Cfg heights tag)
    (firstRecorded : ⟨tag,first⟩ ∈ state.checkpoints.checkpoints)
    (secondRecorded : ⟨tag,second⟩ ∈ state.checkpoints.checkpoints) (sameRoot : first.root = second.root) :
    SubclaimSourceLayout.decodedSource (front := front) domain capacity radius (word enc dummy heights tag first) =
      SubclaimSourceLayout.decodedSource (front := front) domain capacity radius (word enc dummy heights tag second) ∨
      CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) state := by
  rcases word_eq_or_bad (front := front) enc dummy heights state audited tag first second firstRecorded secondRecorded sameRoot with same | bad
  · exact Or.inl (congrArg (SubclaimSourceLayout.decodedSource domain capacity radius) same)
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.HeterogeneousSourceCoherence
