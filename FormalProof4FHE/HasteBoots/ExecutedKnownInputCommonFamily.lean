module
public import FormalProof4FHE.HasteBoots.DecodedKnownInput
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! The actual known-input check fixes the later common-family input to the
negative accumulator mask, using its literal fresh checkpoint and retention. -/
namespace FormalProof4FHE.HasteBoots.ExecutedKnownInputCommonFamily
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {q c lanes front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Digest Cfg Response Memory CommitMemory Index : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}
variable (s : AmbientKnownInput.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
  (2^lanes) (1+c) front suffix m queries height)
  (small : 2*(2^lanes) ≤ q) (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (root : Digest)
  (accumulator : NativeBlindRotation.Cipher q (2^(c+lanes)))
  [SampleableType Digest] [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) (2^lanes))]
  [SampleableType (Fin queries → Fin (2^height))]
variable (dummy : Digest) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : AmbientKnownInput.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
    AmbientKnownInput.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
      (b := 2^lanes) (n := 1+c) (front := front) (queries := queries) (height := height))
  (supported : outcome ∈ support (AmbientKnownInput.witness heights
    (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s) dummy initial))

include supported in
theorem negative_mask_on_world
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (index : Index) (geometry : heights s.tag = height)
    (parameters : DecodedKnownInput.parameters
      (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s)
      heights geometry capacity radius = world.parameters index)
    (worldRoot : world.roots index = root)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (noBad : ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state)
    (passes : outcome.2.1.2.accepted = true)
    (clear : ¬AmbientKnownInput.OriginalRisk heights
      (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s) dummy capacity radius outcome) :
    ∀ half, PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy index half = -accumulator false := by
  let owner := AmbientCommittedBatchSafeBound.snapshots heights (fun _ : Unit => s.tag) outcome.1 ()
  have recorded := AmbientKnownInput.fresh_recorded heights
    (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s) dummy initial outcome supported
  have rootEq := KeySwitchKnownInput.witness_root small enc root (Nat.pow_add 2 c lanes).symm accumulator s
    heights dummy initial outcome supported
  have ownerRoot : owner.root = world.roots index := rootEq.trans worldRoot.symm
  exact DecodedKnownInput.negative_mask_family_of_not_risk s small enc root accumulator heights dummy capacity radius
    outcome owner rfl recorded passes clear world index geometry parameters state audited worldRecorded
    (retained _ _ recorded) ownerRoot noBad

include supported in
theorem wrong_mask_implies_risk_or_bad
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (index : Index) (geometry : heights s.tag = height)
    (parameters : DecodedKnownInput.parameters
      (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s)
      heights geometry capacity radius = world.parameters index)
    (worldRoot : world.roots index = root)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (passes : outcome.2.1.2.accepted = true)
    (half : Bool)
    (wrong : PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy index half ≠ -accumulator false) :
    AmbientKnownInput.OriginalRisk heights
      (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s) dummy capacity radius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state
  · exact Or.inr bad
  left
  by_contra clear
  exact wrong (negative_mask_on_world s small enc root accumulator dummy capacity radius initial outcome supported
    world index geometry parameters worldRoot state audited retained worldRecorded bad passes clear half)

end
end FormalProof4FHE.HasteBoots.ExecutedKnownInputCommonFamily
