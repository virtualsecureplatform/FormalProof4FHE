module
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchReconstruction
public import FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! Accepted native reconstruction constrains a later common recorded family.
Only public descriptor/root associations and actual checkpoint retention are
used; no decoded source equality is supplied and final Bad is shared. -/
namespace FormalProof4FHE.HasteBoots.ExecutedReconstructionCommonFamily
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

variable {Index : Type}
include supported in
theorem relation_on_world
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (slots : Fin (2*d+2) → Index)
    (parameters : ∀ factor, (ExecutedKeySwitchReconstruction.sourceFamily s enc input family nodesEnough radix capacity radius outcome.1).parameters factor = world.parameters (slots factor))
    (roots : ∀ factor, (ExecutedKeySwitchReconstruction.sourceFamily s enc input family nodesEnough radix capacity radius outcome.1).roots factor = world.roots (slots factor))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (noBad : ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state)
    (passes : PaddedLinear.accepted (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) outcome.2.1 = true)
    (clear : ¬PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius outcome) :
    DecompositionLinear.Relation radix
      (fun factor => RecordedPaddedSourceFamily.logical world enc dummy (c+1) (slots factor)) := by
  have localRecorded := CheckpointHistoryChain.family_recorded (ExecutedKeySwitchReconstruction.sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) outcome.2.2 state retained
    (ExecutedKeySwitchReconstruction.sourceFamily_recorded s enc input family nodesEnough radix capacity radius dummy initial outcome supported)
  have same := (RecordedFamilyEmbedding.logical_eq_or_bad (ExecutedKeySwitchReconstruction.sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) world slots parameters roots
    enc dummy (1+c) state audited localRecorded worldRecorded).resolve_right noBad
  have checked := ExecutedKeySwitchReconstruction.sourceFamily_relation s enc input family nodesEnough radix capacity radius dummy initial outcome supported passes clear
  rw [same] at checked
  have reindex (left right : ℕ) (equal : left = right) :
      DecompositionLinear.Relation radix (fun factor => RecordedPaddedSourceFamily.logical world enc dummy left (slots factor)) →
      DecompositionLinear.Relation radix (fun factor => RecordedPaddedSourceFamily.logical world enc dummy right (slots factor)) := by
    cases equal
    exact id
  exact reindex (1+c) (c+1) (Nat.add_comm 1 c) checked

include supported in
theorem wrong_relation_implies_risk_or_bad
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (slots : Fin (2*d+2) → Index)
    (parameters : ∀ factor, (ExecutedKeySwitchReconstruction.sourceFamily s enc input family nodesEnough radix capacity radius outcome.1).parameters factor = world.parameters (slots factor))
    (roots : ∀ factor, (ExecutedKeySwitchReconstruction.sourceFamily s enc input family nodesEnough radix capacity radius outcome.1).roots factor = world.roots (slots factor))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (passes : PaddedLinear.accepted (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) outcome.2.1 = true)
    (wrong : ¬(DecompositionLinear.Relation radix
      (fun factor => RecordedPaddedSourceFamily.logical world enc dummy (c+1) (slots factor)))) :
    PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius outcome ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state
  · exact Or.inr bad
  left
  by_contra clear
  exact wrong (relation_on_world s enc input family nodesEnough radix capacity radius dummy initial outcome supported world slots parameters roots state audited retained worldRecorded bad passes clear)

end
end FormalProof4FHE.HasteBoots.ExecutedReconstructionCommonFamily
