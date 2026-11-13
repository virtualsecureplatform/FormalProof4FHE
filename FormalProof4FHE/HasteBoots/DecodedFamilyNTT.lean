module
public import FormalProof4FHE.HasteBoots.DecodedPaddedNTT
@[expose] public section

/-! The executed native padded NTT constrains the common recorded family.
Stage-local owners and the later global family need only share public decoder
metadata and retained roots outside the single global collision event. -/
namespace FormalProof4FHE.HasteBoots.DecodedFamilyNTT
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {q c lanes k : ℕ} [Fact q.Prime]
  {Input Digest Cfg Response Memory CommitMemory Index : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}

/-- Both halves of the actual coefficient/evaluation roots satisfy the native
negacyclic transform, interpreted in the common family. -/
theorem native_transform_of_not_risk
    (s : PaddedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory heights (2^lanes) c 1 k)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (roots : Bool → Digest)
    (nodesEnough : 2*(2^lanes) ≤ q) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))
    (dummy : Digest)
    (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*(2^lanes)) (radius : Bool → ℕ)
    (outcome : PaddedNTT.Prefix (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedNTT.RunResult (PaddedNTT.nativeScheme s enc roots q nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive))
    (owner : ∀ side, AmbientMatrixSource.Snapshot Input Digest heights (s.tag side))
    (recorded : ∀ side, (owner side).root = outcome.1.1.1 side ∧ ⟨s.tag side,owner side⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (passes : PaddedNTT.accepted (PaddedNTT.nativeScheme s enc roots q nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) outcome.2.1 = true)
    (clear : ¬PaddedNTT.OriginalRisk (PaddedNTT.nativeScheme s enc roots q nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive)
      dummy capacity radius outcome)
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (slots : Bool → Index)
    (associated : ∀ side, PaddedStageSourceInterpretation.nttParameters
      (PaddedNTT.nativeScheme s enc roots q nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive)
      capacity radius side = world.parameters (slots side))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (retained : ∀ side, ⟨s.tag side,owner side⟩ ∈ state.checkpoints.checkpoints)
    (ownerRoots : ∀ side, (owner side).root = world.roots (slots side))
    (noBad : ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state)
    (half : Bool) :
    BlindRotationNTT.transform (c+lanes) psi
      (PackedCipherSource.familyCipher (c := c) world enc dummy (slots false) half) =
      PackedCipherSource.familyCipher (c := c) world enc dummy (slots true) half := by
  have same : DecodedPaddedNTT.cipher
      (PaddedNTT.nativeScheme s enc roots q nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive)
      dummy capacity radius owner = fun side => PackedCipherSource.familyCipher (c := c) world enc dummy (slots side) := by
    funext side
    exact (DecodedPaddedNTT.cipher_family_eq_or_bad
      (PaddedNTT.nativeScheme s enc roots q nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive)
      world (slots side) side dummy capacity radius (associated side) state audited worldRecorded owner
      (retained side) (ownerRoots side)).resolve_right noBad
  have transformed := DecodedPaddedNTT.native_transform_of_not_risk s enc roots nodesEnough psi primitive
    dummy capacity radius outcome owner recorded passes clear half
  rw [same] at transformed
  exact transformed

end
end FormalProof4FHE.HasteBoots.DecodedFamilyNTT
