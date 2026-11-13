module
public import FormalProof4FHE.HasteBoots.AcceptedKeySwitchNTT
public import FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
public import FormalProof4FHE.HasteBoots.ExecutedNTTCommonFamily
public import FormalProof4FHE.HasteBoots.RecordedSourceWorld
@[expose] public section

/-! Actual accepted NTT children constrain a later common family. The local
source family uses those literal child owners, so only the global audited
history exclusion is needed for transport. -/
namespace FormalProof4FHE.HasteBoots.ExecutedNTTWorld
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {q c lanes d : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}
variable (base : Fin (d+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory heights (2^lanes) c 1 (2^lanes))
  (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
  (nodesEnough : 2*(2^lanes) ≤ q) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))

variable [SampleableType (Fin (2^lanes) → Fin 1 → ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)] [SampleableType Digest]
  [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((base index memory).code side).front) (2^lanes))]
  [∀ index memory side, SampleableType (Fin ((base index memory).code side).queries → Fin (2^heights ((base index memory).tag side)))]

variable (dummy : Digest) (memory : Memory)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : PaddedNTTSequence.Trace (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (supported : outcome ∈ support (KeySwitchPaddedNTT.witness base enc family nodesEnough
    (Nat.pow_add 2 c lanes).symm psi primitive dummy memory initial))

include supported in
/-- All reached accepted NTT children constrain the canonical final-history
family, or expose the already bounded loop risk or final Bad. -/
theorem transform_or_risk_or_bad
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ) (passes : outcome.1.accepted = true)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (retained : CheckpointHistoryChain.Retains outcome.2 state) :
    let world := RecordedSourceWorld.family (F := ZMod q) (b := 2^lanes) state
    let localRecorded := CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 state retained
      (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)
    let slots := RecordedSourceWorld.slot (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) state localRecorded
    (∀ index half, BlindRotationNTT.transform (c+lanes) psi
      (PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (index,false)) half) =
      PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (index,true)) half) ∨
      PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy capacity radius outcome.1 ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  dsimp only
  classical
  by_cases risky : PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy capacity radius outcome.1
  · exact Or.inr (Or.inl risky)
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state
  · exact Or.inr (Or.inr bad)
  left
  intro index half
  exact ExecutedNTTCommonFamily.transform_on_world base enc family nodesEnough psi primitive dummy memory initial outcome supported
    capacity radius passes (RecordedSourceWorld.family state)
    (RecordedSourceWorld.slot (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) state (CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 state retained
      (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)))
    (fun _ => rfl) (fun _ => rfl) state audited retained (RecordedSourceWorld.recorded state) bad risky index half

end
end FormalProof4FHE.HasteBoots.ExecutedNTTWorld
