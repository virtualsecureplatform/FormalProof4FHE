module
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchProduct
public import FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! Accepted native product constrains a later common recorded family.
Only public descriptor/root associations and actual checkpoint retention are
used; no decoded source equality is supplied and final Bad is shared. -/
namespace FormalProof4FHE.HasteBoots.ExecutedProductCommonFamily
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

variable {Index : Type}
include supported in
theorem identity_on_world
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (slots : PBSHadamard.Factor d → Index)
    (parameters : ∀ factor, (ExecutedKeySwitchProduct.sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1).parameters factor = world.parameters (slots factor))
    (roots : ∀ factor, (ExecutedKeySwitchProduct.sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1).roots factor = world.roots (slots factor))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (noBad : ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state)
    (passes : PaddedZeroCheck.accepted (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) outcome.2.1 = true)
    (clear : ¬PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius outcome) :
    PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (.inr ())) =
      ∑ level : Fin d, PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (.inl (level,false))) *
        PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (.inl (level,true))) := by
  have localRecorded := CheckpointHistoryChain.family_recorded (ExecutedKeySwitchProduct.sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1) outcome.2.2 state retained
    (ExecutedKeySwitchProduct.sourceFamily_recorded s enc family firstSmall roundSmall nodesEnough capacity radius dummy initial outcome supported)
  have same := (RecordedFamilyEmbedding.cipher_eq_or_bad (c := c) (ExecutedKeySwitchProduct.sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1) world slots parameters roots
    enc dummy state audited localRecorded worldRecorded).resolve_right noBad
  have checked := ExecutedKeySwitchProduct.sourceFamily_identity s enc family firstSmall roundSmall nodesEnough capacity radius dummy initial outcome supported passes clear
  have sameAt factor := congrFun same factor
  simpa only [sameAt] using checked

include supported in
theorem wrong_identity_implies_risk_or_bad
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (slots : PBSHadamard.Factor d → Index)
    (parameters : ∀ factor, (ExecutedKeySwitchProduct.sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1).parameters factor = world.parameters (slots factor))
    (roots : ∀ factor, (ExecutedKeySwitchProduct.sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1).roots factor = world.roots (slots factor))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (passes : PaddedZeroCheck.accepted (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) outcome.2.1 = true)
    (wrong : ¬(PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (.inr ())) =
      ∑ level : Fin d, PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (.inl (level,false))) *
        PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (slots (.inl (level,true))))) :
    PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius outcome ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state
  · exact Or.inr bad
  left
  by_contra clear
  exact wrong (identity_on_world s enc family firstSmall roundSmall nodesEnough capacity radius dummy initial outcome supported world slots parameters roots state audited retained worldRecorded bad passes clear)

end
end FormalProof4FHE.HasteBoots.ExecutedProductCommonFamily
