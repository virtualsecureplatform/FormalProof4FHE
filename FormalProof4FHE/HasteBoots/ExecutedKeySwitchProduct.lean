module
public import FormalProof4FHE.HasteBoots.ExecutedPaddedSourceFamily
public import FormalProof4FHE.HasteBoots.DecodedPaddedProduct
@[expose] public section

/-! The native product's actual original snapshots construct a recorded family
whose decoded evaluation arrays satisfy the checked product equation. -/
namespace FormalProof4FHE.HasteBoots.ExecutedKeySwitchProduct
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

/-- Construct the product family from the literal native prefix. -/
abbrev sourceFamily := ExecutedPaddedSourceFamily.zeroFamily
  (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) capacity radius

omit [DecidableEq Input] in
/-- Unpacking the original source and the constructed family gives one value. -/
theorem cipher_eq (dummy : Digest)
    (first : PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights)
    (factor : PBSHadamard.Factor d) :
    DecodedPaddedProduct.cipher (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough)
      dummy capacity radius (HeterogeneousSingleOpening.snapshots heights s.tag first) factor =
      PackedCipherSource.familyCipher (c := c) (sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius first) enc dummy factor := by
  unfold DecodedPaddedProduct.cipher PackedCipherSource.familyCipher
  rw [ExecutedPaddedSourceFamily.zero_logical]

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
/-- Every digit/key/result anchor is obtained and recorded by actual execution. -/
theorem sourceFamily_recorded :
    RecordedPaddedSourceFamily.Recorded
      (sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1) outcome.2.2 :=
  ExecutedPaddedSourceFamily.zero_recorded_witness
    (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius
    PBSHadamard.factors_complete initial outcome supported

include supported in
/-- Constructed roots are exactly the caller's evaluation/key/result roots. -/
theorem sourceFamily_roots :
    (sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1).roots = KeySwitchPaddedProduct.roots family :=
  KeySwitchPaddedProduct.witness_roots s enc family firstSmall roundSmall nodesEnough dummy initial outcome supported

include supported in
/-- The actual native product constrains the complete constructed tables,
without a separately supplied family or source-value association. -/
theorem sourceFamily_relation
    (passes : PaddedZeroCheck.accepted (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) outcome.2.1 = true)
    (clear : ¬PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius outcome) :
    PBSHadamard.Relation
      (RecordedPaddedSourceFamily.logical (sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1) enc dummy (c+1)) := by
  have recorded := sourceFamily_recorded s enc family firstSmall roundSmall nodesEnough capacity radius dummy initial outcome supported
  have checked := DecodedPaddedProduct.relation_of_not_risk s enc family firstSmall roundSmall nodesEnough dummy capacity radius outcome
    (HeterogeneousSingleOpening.snapshots heights s.tag outcome.1) (fun factor => ⟨rfl,recorded factor⟩) passes clear
  have same : PaddedZeroCheck.originalSources (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough)
      dummy capacity radius (HeterogeneousSingleOpening.snapshots heights s.tag outcome.1) =
      RecordedPaddedSourceFamily.logical (sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1) enc dummy (c+1) := by
    funext factor
    exact ExecutedPaddedSourceFamily.zero_logical (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius outcome.1 factor
  rw [same] at checked
  exact checked

include supported in
/-- The family arrays satisfy the pointwise evaluation-domain product sum. -/
theorem sourceFamily_identity
    (passes : PaddedZeroCheck.accepted (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) outcome.2.1 = true)
    (clear : ¬PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius outcome) :
    PackedCipherSource.familyCipher (c := c) (sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1) enc dummy (.inr ()) =
      ∑ level : Fin d, PackedCipherSource.familyCipher (c := c) (sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1) enc dummy (.inl (level,false)) *
        PackedCipherSource.familyCipher (c := c) (sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1) enc dummy (.inl (level,true)) := by
  have recorded := sourceFamily_recorded s enc family firstSmall roundSmall nodesEnough capacity radius dummy initial outcome supported
  have checked := DecodedPaddedProduct.native_identity_of_not_risk s enc family firstSmall roundSmall nodesEnough dummy capacity radius outcome
    (HeterogeneousSingleOpening.snapshots heights s.tag outcome.1) (fun factor => ⟨rfl,recorded factor⟩) passes clear
  have same := funext (cipher_eq s enc family firstSmall roundSmall nodesEnough capacity radius dummy outcome.1)
  rw [same] at checked
  exact checked

include supported in
/-- A false constructed-family product relation is already in the existing
native original-owner risk event whenever the actual stage accepts. -/
theorem wrong_relation_implies_risk
    (passes : PaddedZeroCheck.accepted (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) outcome.2.1 = true)
    (wrong : ¬PBSHadamard.Relation
      (RecordedPaddedSourceFamily.logical (sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius outcome.1) enc dummy (c+1))) :
    PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius outcome := by
  by_contra clear
  exact wrong (sourceFamily_relation s enc family firstSmall roundSmall nodesEnough capacity radius dummy initial outcome supported passes clear)

/-- Accepted false relations of the execution-built family inherit the native
original-owner risk bound under the same single final collision exclusion. -/
theorem false_relation_safe_le_original :
    Pr{let actual ← (PaddedZeroCheck.witness (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy initial)}[
      PaddedZeroCheck.accepted (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) actual.2.1 = true ∧
      ¬PBSHadamard.Relation (RecordedPaddedSourceFamily.logical (sourceFamily s enc family firstSmall roundSmall nodesEnough capacity radius actual.1) enc dummy (c+1)) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) actual.2.2] ≤
    Pr{let actual ← (PaddedZeroCheck.witness (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy initial)}[
      PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius actual ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) actual.2.2] := by
  apply prEvent_mono_of_support
  intro actual present event
  exact ⟨wrong_relation_implies_risk s enc family firstSmall roundSmall nodesEnough capacity radius dummy initial actual present event.1 event.2.1,event.2.2⟩

end
end FormalProof4FHE.HasteBoots.ExecutedKeySwitchProduct
