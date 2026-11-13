module
public import FormalProof4FHE.HasteBoots.DecodedKnownInput
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
public import FormalProof4FHE.HasteBoots.ExecutedKnownInputCommonFamily
public import FormalProof4FHE.HasteBoots.RecordedSourceWorld
@[expose] public section

/-! The actual known-input check fixes the later common-family input to the
negative accumulator mask, using its literal fresh checkpoint and retention. -/
namespace FormalProof4FHE.HasteBoots.ExecutedKnownInputWorld
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {q c lanes front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Digest Cfg Response Memory CommitMemory : Type}
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

/-- The literal fresh known-input checkpoint supplies its canonical world slot. -/
def slot (geometry : heights s.tag = height)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state) : RecordedSourceWorld.Index (ZMod q) (2^lanes) state :=
  ⟨⟨DecodedKnownInput.parameters (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s) heights geometry capacity radius,root⟩,
    AmbientCommittedBatchSafeBound.snapshots heights (fun _ : Unit => s.tag) outcome.1 (),
    KeySwitchKnownInput.witness_root small enc root (Nat.pow_add 2 c lanes).symm accumulator s heights dummy initial outcome supported,
    retained _ _ (AmbientKnownInput.fresh_recorded heights (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s) dummy initial outcome supported)⟩

include supported in
/-- The actual accepted known-input check fixes both canonical world halves
or exposes its arithmetic risk or the single final Bad event. -/
theorem negative_mask_or_risk_or_bad
    (geometry : heights s.tag = height)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (passes : outcome.2.1.2.accepted = true) :
    (∀ half, PackedCipherSource.familyCipher (c := c) (lanes := lanes) (RecordedSourceWorld.family state) enc dummy
      (slot s small enc root accumulator dummy capacity radius initial outcome supported geometry state retained) half = -accumulator false) ∨
      AmbientKnownInput.OriginalRisk heights (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s) dummy capacity radius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  classical
  by_cases risky : AmbientKnownInput.OriginalRisk heights (KeySwitchKnownInput.stage small enc root (Nat.pow_add 2 c lanes).symm accumulator s) dummy capacity radius outcome
  · exact Or.inr (Or.inl risky)
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state
  · exact Or.inr (Or.inr bad)
  left
  exact ExecutedKnownInputCommonFamily.negative_mask_on_world s small enc root accumulator dummy capacity radius initial outcome supported
    (RecordedSourceWorld.family state) (slot s small enc root accumulator dummy capacity radius initial outcome supported geometry state retained) geometry rfl rfl
    state audited retained (RecordedSourceWorld.recorded state) bad passes risky

end
end FormalProof4FHE.HasteBoots.ExecutedKnownInputWorld
