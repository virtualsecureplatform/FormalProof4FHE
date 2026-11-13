module
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchProduct
public import FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
public import FormalProof4FHE.HasteBoots.ExecutedProductCommonFamily
public import FormalProof4FHE.HasteBoots.RecordedSourceWorld
@[expose] public section

/-! The final history constructs the common family used by the actual
accepted product. No caller-supplied family or source-value map is needed. -/
namespace FormalProof4FHE.HasteBoots.ExecutedProductWorld
open OracleSpec OracleComp BinaryTree
open scoped BigOperators
open NativeRootMessage (Digest)
noncomputable section
variable {q d c lanes : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}
variable (s : KeySwitchPaddedProduct.Scheme (q := q) (d := d) (b := 2^lanes) (n := c)
  (Input := Input) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (heights := heights))
variable (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
  (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
  (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
  (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : PBSHadamard.Factor d → ℕ)

variable [SampleableType Digest] [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) c (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(s.code factor).front) (2^lanes))]
  [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^heights (s.tag factor)))]
variable (dummy : Digest)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
    PaddedZeroCheck.RunResult (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough))
  (supported : outcome ∈ support (PaddedZeroCheck.witness (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy initial))

include supported in
/-- Acceptance constrains the canonical family constructed from the final
recorded history, or exposes the executed arithmetic risk or final Bad. -/
theorem identity_or_risk_or_bad
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (passes : PaddedZeroCheck.accepted (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) outcome.2.1 = true) :
    let world := RecordedSourceWorld.family (F := ZMod q) (b := 2^lanes) state
    let localRecorded := CheckpointHistoryChain.family_recorded (ExecutedKeySwitchProduct.sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1) outcome.2.2 state retained
      (ExecutedKeySwitchProduct.sourceFamily_recorded s enc family firstSmall roundSmall nodesEnough capacity radius dummy initial outcome supported)
    let slots := RecordedSourceWorld.slot (ExecutedKeySwitchProduct.sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1) state localRecorded
    (PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (.inr ())) =
      ∑ level : Fin d, PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (.inl (level,false))) *
        PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (.inl (level,true)))) ∨
      PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  dsimp only
  classical
  by_cases risky : PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius outcome
  · exact Or.inr (Or.inl risky)
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state
  · exact Or.inr (Or.inr bad)
  left
  exact ExecutedProductCommonFamily.identity_on_world s enc family firstSmall roundSmall nodesEnough capacity radius dummy initial outcome supported (RecordedSourceWorld.family state) (RecordedSourceWorld.slot (ExecutedKeySwitchProduct.sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1) state (CheckpointHistoryChain.family_recorded (ExecutedKeySwitchProduct.sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1) outcome.2.2 state retained
      (ExecutedKeySwitchProduct.sourceFamily_recorded s enc family firstSmall roundSmall nodesEnough capacity radius dummy initial outcome supported))) (fun _ => rfl) (fun _ => rfl) state audited retained
    (RecordedSourceWorld.recorded state) bad passes risky

end
end FormalProof4FHE.HasteBoots.ExecutedProductWorld
