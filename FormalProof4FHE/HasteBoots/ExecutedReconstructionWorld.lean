module
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchReconstruction
public import FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
public import FormalProof4FHE.HasteBoots.ExecutedReconstructionCommonFamily
public import FormalProof4FHE.HasteBoots.RecordedSourceWorld
@[expose] public section

/-! The final history constructs the common family used by the actual
accepted reconstruction. No caller-supplied family or source-value map is needed. -/
namespace FormalProof4FHE.HasteBoots.ExecutedReconstructionWorld
open OracleSpec OracleComp BinaryTree
open scoped BigOperators
open NativeRootMessage (Digest)
noncomputable section
variable {q d c lanes : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}
variable (s : PaddedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory heights (2*d+2) (2^lanes) (1+c))
variable (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
  (input : NativeGoldParameterStore.Reference) (family : PackedPBSOriginalReferences.Family d)
  (nodesEnough : 2*(2^lanes) ≤ q) (radix : ZMod q)
  (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Fin (2*d+2) → ℕ)

variable [SampleableType Digest] [SampleableType (Fin (2^lanes) → ZMod q)]
  [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(s.code factor).front) (2^lanes))]
  [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^heights (s.tag factor)))]
variable (dummy : Digest)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : PaddedLinear.Prefix (count := 2*d+2) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
    PaddedLinear.RunResult (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix))
  (supported : outcome ∈ support (PaddedLinear.witness (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy initial))

include supported in
/-- Acceptance constrains the canonical family constructed from the final
recorded history, or exposes the executed arithmetic risk or final Bad. -/
theorem relation_or_risk_or_bad
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (passes : PaddedLinear.accepted (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) outcome.2.1 = true) :
    let world := RecordedSourceWorld.family (F := ZMod q) (b := 2^lanes) state
    let localRecorded := CheckpointHistoryChain.family_recorded (ExecutedKeySwitchReconstruction.sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) outcome.2.2 state retained
      (ExecutedKeySwitchReconstruction.sourceFamily_recorded s enc input family nodesEnough radix capacity radius dummy initial outcome supported)
    let slots := RecordedSourceWorld.slot (ExecutedKeySwitchReconstruction.sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) state localRecorded
    (DecompositionLinear.Relation radix
      (fun factor => RecordedPaddedSourceFamily.logical world enc dummy (c+1) (slots factor))) ∨
      PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  dsimp only
  classical
  by_cases risky : PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius outcome
  · exact Or.inr (Or.inl risky)
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state
  · exact Or.inr (Or.inr bad)
  left
  exact ExecutedReconstructionCommonFamily.relation_on_world s enc input family nodesEnough radix capacity radius dummy initial outcome supported (RecordedSourceWorld.family state) (RecordedSourceWorld.slot (ExecutedKeySwitchReconstruction.sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) state (CheckpointHistoryChain.family_recorded (ExecutedKeySwitchReconstruction.sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) outcome.2.2 state retained
      (ExecutedKeySwitchReconstruction.sourceFamily_recorded s enc input family nodesEnough radix capacity radius dummy initial outcome supported))) (fun _ => rfl) (fun _ => rfl) state audited retained
    (RecordedSourceWorld.recorded state) bad passes risky

end
end FormalProof4FHE.HasteBoots.ExecutedReconstructionWorld
