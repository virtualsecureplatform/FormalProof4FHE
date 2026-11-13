module
public import FormalProof4FHE.HasteBoots.AcceptedKeySwitchNTT
public import FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! Actual accepted NTT children constrain a later common family. The local
source family uses those literal child owners, so only the global audited
history exclusion is needed for transport. -/
namespace FormalProof4FHE.HasteBoots.ExecutedNTTCommonFamily
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
/-- The selected child's decoded rows are the very owners used to construct
the accepted loop family, without an extra coherence or safety premise. -/
theorem selected_cipher
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ) (passes : outcome.1.accepted = true)
    (index : Fin (d+1)) (side : Bool) :
    let child := AcceptedKeySwitchNTT.selected base enc family nodesEnough psi primitive dummy memory initial outcome supported passes index
    DecodedPaddedNTT.cipher ((KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) child.1.1 child.1.2)
      dummy (capacity child.1.1 child.1.2) (radius child.1.1 child.1.2)
      (AcceptedKeySwitchNTT.owners base enc family nodesEnough psi primitive (index,child)) side =
    PackedCipherSource.familyCipher (c := c) (lanes := lanes) (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) enc dummy (index,side) := by
  dsimp only
  unfold DecodedPaddedNTT.cipher
  rw [PaddedStageSourceInterpretation.ntt_original]
  change PackedCipherSource.ofRows
    (RecordedPaddedSourceFamily.logical (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) enc dummy (1+c) (index,side)) = _
  exact PackedCipherSource.ofRows_family (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) enc dummy (index,side)

variable {Index : Type}
include supported in
theorem transform_on_world
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ) (passes : outcome.1.accepted = true)
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (slots : (Fin (d+1) × Bool) → Index)
    (parameters : ∀ pair, (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes).parameters pair = world.parameters (slots pair))
    (roots : ∀ pair, (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes).roots pair = world.roots (slots pair))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (retained : CheckpointHistoryChain.Retains outcome.2 state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (noBad : ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state)
    (clear : ¬PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy capacity radius outcome.1)
    (index : Fin (d+1)) (half : Bool) :
    BlindRotationNTT.transform (c+lanes) psi
      (PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (index,false)) half) =
      PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (index,true)) half := by
  have localRecorded := CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 state retained
    (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)
  have same := (RecordedFamilyEmbedding.cipher_eq_or_bad (c := c) (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) world slots parameters roots
    enc dummy state audited localRecorded worldRecorded).resolve_right noBad
  have transformed := AcceptedKeySwitchNTT.retained_transform base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes clear
    (index,AcceptedKeySwitchNTT.selected base enc family nodesEnough psi primitive dummy memory initial outcome supported passes index)
    (AcceptedKeySwitchNTT.selected_member base enc family nodesEnough psi primitive dummy memory initial outcome supported passes index) half
  rw [selected_cipher base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes index false,
    selected_cipher base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes index true] at transformed
  have sameAt pair := congrFun same pair
  simpa only [sameAt] using transformed

include supported in
theorem wrong_transform_implies_risk_or_bad
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ) (passes : outcome.1.accepted = true)
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (slots : (Fin (d+1) × Bool) → Index)
    (parameters : ∀ pair, (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes).parameters pair = world.parameters (slots pair))
    (roots : ∀ pair, (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes).roots pair = world.roots (slots pair))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (retained : CheckpointHistoryChain.Retains outcome.2 state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (index : Fin (d+1)) (half : Bool) (wrong : ¬(BlindRotationNTT.transform (c+lanes) psi
      (PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (index,false)) half) =
      PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (index,true)) half)) :
    PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy capacity radius outcome.1 ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state
  · exact Or.inr bad
  left
  by_contra clear
  exact wrong (transform_on_world base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes world slots parameters roots
    state audited retained worldRecorded bad clear index half)

end
end FormalProof4FHE.HasteBoots.ExecutedNTTCommonFamily
