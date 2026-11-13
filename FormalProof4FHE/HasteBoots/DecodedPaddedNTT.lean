module
public import FormalProof4FHE.HasteBoots.PackedCipherSource
public import FormalProof4FHE.HasteBoots.PaddedNTT
public import FormalProof4FHE.HasteBoots.BlindRotationNTT
public import FormalProof4FHE.HasteBoots.PaddedStageSourceInterpretation
@[expose] public section

/-! Accepted native NTT relations act on coefficient-domain ciphertexts
constructed from the actual original source tables. Both polynomial halves
are derived from their complete rows; no coefficient/evaluation source-value
certificate is supplied. -/
namespace FormalProof4FHE.HasteBoots.DecodedPaddedNTT
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {q c lanes k : ℕ} [Fact q.Prime]
  {Input Digest Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}

variable (s : PaddedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory heights (2^lanes) c 1 k)

/-- Each retained coefficient/evaluation source constructs its two polynomial halves. -/
def cipher (dummy : Digest)
    (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*(2^lanes)) (radius : Bool → ℕ)
    (owner : ∀ side, AmbientMatrixSource.Snapshot Input Digest heights (s.tag side)) (side : Bool) :=
  PackedCipherSource.ofRows (PaddedNTT.originalSources s dummy capacity radius owner side)

omit [DecidableEq Input] in
/-- Clearing the actual NTT risk enforces the verifier's transform on complete
original-owner rows, with both decoded halves constructed from those rows. -/
theorem relation_of_not_risk (dummy : Digest)
    (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*(2^lanes)) (radius : Bool → ℕ)
    (outcome : PaddedNTT.Prefix (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights × PaddedNTT.RunResult s)
    (owner : ∀ side, AmbientMatrixSource.Snapshot Input Digest heights (s.tag side))
    (recorded : ∀ side, (owner side).root = outcome.1.1.1 side ∧ ⟨s.tag side,owner side⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (passes : PaddedNTT.accepted s outcome.2.1 = true)
    (clear : ¬PaddedNTT.OriginalRisk s dummy capacity radius outcome) :
    NTTRowCheck.Relation s.transform
      (NTTCompression.sourceRows c 1 (PaddedNTT.originalSources s dummy capacity radius owner false))
      (NTTCompression.sourceRows c 1 (PaddedNTT.originalSources s dummy capacity radius owner true)) := by
  by_contra wrong
  exact clear ⟨owner,recorded,wrong,passes⟩

omit [DecidableEq Input] in
/-- The trusted native butterfly driver enforces the exact negacyclic transform
of the decoded original coefficient source, for each ciphertext half. -/
theorem native_transform_of_not_risk
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
      dummy capacity radius outcome) (half : Bool) :
    BlindRotationNTT.transform (c+lanes) psi
      (cipher (PaddedNTT.nativeScheme s enc roots q nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) dummy capacity radius owner false half) =
    cipher (PaddedNTT.nativeScheme s enc roots q nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) dummy capacity radius owner true half := by
  have relation := relation_of_not_risk (PaddedNTT.nativeScheme s enc roots q nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive)
    dummy capacity radius outcome owner recorded passes clear
  have row := relation (half,())
  have flattened := congrArg (PackedNTT.flatten (Nat.pow_add 2 c lanes).symm) row
  change PackedNTT.flatten (Nat.pow_add 2 c lanes).symm
      (PackedNTT.unflatten (Nat.pow_add 2 c lanes).symm
        (NTTButterfly.flatTransform (c+lanes) psi (psi^2)
          (PackedNTT.flatten (Nat.pow_add 2 c lanes).symm
            (NTTCompression.sourceRows c 1 (PaddedNTT.originalSources
              (PaddedNTT.nativeScheme s enc roots q nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive)
              dummy capacity radius owner false) (half,()))))) = _ at flattened
  rw [PackedNTT.flatten_unflatten,PackedCipherSource.flatten_rows,PackedCipherSource.flatten_rows,
    NTTButterfly.negacyclic_evaluation (c+lanes) psi primitive] at flattened
  exact flattened
variable {Index : Type}

/-- Public descriptor and recorded-root association identify the constructed
NTT source value with the same common coefficient-domain family value. -/
theorem cipher_family_eq_or_bad
    (family : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (index : Index) (side : Bool) (dummy : Digest)
    (capacity : ∀ side, 2^(s.code side).suffix ≤ (s.code side).m*(2^lanes)) (radius : Bool → ℕ)
    (associated : PaddedStageSourceInterpretation.nttParameters s capacity radius side = family.parameters index)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) state)
    (familyRecorded : RecordedPaddedSourceFamily.Recorded family state)
    (owner : ∀ side, AmbientMatrixSource.Snapshot Input Digest heights (s.tag side))
    (ownerRecorded : ⟨s.tag side,owner side⟩ ∈ state.checkpoints.checkpoints)
    (ownerRoot : (owner side).root = family.roots index) :
    cipher s dummy capacity radius owner side = PackedCipherSource.familyCipher (c := c) family s.encoding dummy index ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  have compared := RecordedPaddedSourceFamily.associated_owner_agrees_or_bad family s.encoding dummy (1+c) index
    (PaddedStageSourceInterpretation.nttParameters s capacity radius side) associated state audited
    familyRecorded (owner side) ownerRecorded ownerRoot
  rcases compared with same | bad
  · left
    unfold cipher
    rw [PaddedStageSourceInterpretation.ntt_original,same,PackedCipherSource.ofRows_family]
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.DecodedPaddedNTT
