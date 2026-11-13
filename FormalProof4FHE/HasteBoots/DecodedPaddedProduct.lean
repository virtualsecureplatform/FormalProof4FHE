module
public import FormalProof4FHE.HasteBoots.PackedCipherSource
public import FormalProof4FHE.HasteBoots.KeySwitchPaddedProduct
public import FormalProof4FHE.HasteBoots.PaddedStageSourceInterpretation
@[expose] public section

/-! The final private product acts on the native-indexed evaluation arrays constructed
from its actual retained evaluation/key/result tables. No independently
supplied interpretation of those private sources is a hypothesis. -/
namespace FormalProof4FHE.HasteBoots.DecodedPaddedProduct
open OracleSpec OracleComp BinaryTree
open scoped BigOperators
open NativeRootMessage (Digest)
noncomputable section
variable {q d c lanes : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}

variable (s : KeySwitchPaddedProduct.Scheme (q := q) (d := d) (b := 2^lanes) (n := c)
  (Input := Input) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (heights := heights))

/-- Construct the value of each original evaluation/key/result factor. -/
def cipher (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : PBSHadamard.Factor d → ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor)) (factor : PBSHadamard.Factor d) :=
  PackedCipherSource.unpack (PaddedZeroCheck.originalSources s dummy capacity radius owner factor)

omit [DecidableEq Input] in
/-- Pointwise decoded multiplication is the literal trusted product identity. -/
theorem identity_of_relation (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : PBSHadamard.Factor d → ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (relation : PBSHadamard.Relation (PaddedZeroCheck.originalSources s dummy capacity radius owner)) :
    cipher s dummy capacity radius owner (.inr ()) =
      ∑ index : Fin d, cipher s dummy capacity radius owner (.inl (index,false)) *
        cipher s dummy capacity radius owner (.inl (index,true)) := by
  funext half coefficient
  simpa only [cipher,PackedCipherSource.unpack,Finset.sum_apply,Pi.mul_apply] using
    relation (PackedCipherSource.point ((PackedAccumulatorTrace.polynomial c lanes).symm coefficient).1 half)
      ((PackedAccumulatorTrace.polynomial c lanes).symm coefficient).2

omit [DecidableEq Input] in
/-- Accepted native product execution outside its actual original-owner risk
enforces the product relation on the complete decoded source tables. -/
theorem relation_of_not_risk
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : PBSHadamard.Factor d → ℕ)
    (outcome : PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedZeroCheck.RunResult (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough))
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧ ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (passes : PaddedZeroCheck.accepted (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) outcome.2.1 = true)
    (clear : ¬PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius outcome) :
    PBSHadamard.Relation (PaddedZeroCheck.originalSources (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough)
      dummy capacity radius owner) := by
  apply (KeySwitchPaddedProduct.relation s enc family firstSmall roundSmall nodesEnough _).mp
  by_contra wrong
  exact clear ⟨owner,recorded,wrong,passes⟩

omit [DecidableEq Input] in
/-- No source-value witness is needed to derive the native pointwise sum of
products from an accepted original-owner-safe stage. -/
theorem native_identity_of_not_risk
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : PBSHadamard.Factor d → ℕ)
    (outcome : PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedZeroCheck.RunResult (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough))
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧ ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (passes : PaddedZeroCheck.accepted (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) outcome.2.1 = true)
    (clear : ¬PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius outcome) :
    cipher (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius owner (.inr ()) =
      ∑ index : Fin d, cipher (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough)
        dummy capacity radius owner (.inl (index,false)) *
        cipher (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough)
          dummy capacity radius owner (.inl (index,true)) :=
  identity_of_relation (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius owner
    (relation_of_not_risk s enc family firstSmall roundSmall nodesEnough dummy capacity radius outcome owner recorded passes clear)

variable {Index : Type}

/-- Public descriptor and recorded-root association give the same common family
value for every original product factor. -/
theorem cipher_family_eq_or_bad
    (family : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (index : Index) (factor : PBSHadamard.Factor d) (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : PBSHadamard.Factor d → ℕ)
    (associated : PaddedStageSourceInterpretation.zeroParameters s capacity radius factor = family.parameters index)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) state)
    (familyRecorded : RecordedPaddedSourceFamily.Recorded family state)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (ownerRecorded : ⟨s.tag factor,owner factor⟩ ∈ state.checkpoints.checkpoints)
    (ownerRoot : (owner factor).root = family.roots index) :
    cipher s dummy capacity radius owner factor = PackedCipherSource.familyCipher (c := c) family s.encoding dummy index ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  have compared := RecordedPaddedSourceFamily.associated_owner_agrees_or_bad family s.encoding dummy (c+1) index
    (PaddedStageSourceInterpretation.zeroParameters s capacity radius factor) associated state audited
    familyRecorded (owner factor) ownerRecorded ownerRoot
  rcases compared with same | bad
  · left
    unfold cipher PackedCipherSource.familyCipher
    rw [PaddedStageSourceInterpretation.zero_original,same]
  · exact Or.inr bad
/-- The actual product enforces its identity on one common family after all
owners have been retained in the final audited history. Public decoder metadata,
not source-value equalities, associates its slots with that family. -/
theorem native_family_identity_of_not_risk
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : PBSHadamard.Factor d → ℕ)
    (outcome : PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedZeroCheck.RunResult (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough))
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧ ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (passes : PaddedZeroCheck.accepted (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) outcome.2.1 = true)
    (clear : ¬PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius outcome)
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (slots : PBSHadamard.Factor d → Index)
    (associated : ∀ factor, PaddedStageSourceInterpretation.zeroParameters
      (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) capacity radius factor = world.parameters (slots factor))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (ownerRetained : ∀ factor, ⟨s.tag factor,owner factor⟩ ∈ state.checkpoints.checkpoints)
    (ownerRoots : ∀ factor, (owner factor).root = world.roots (slots factor))
    (noBad : ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state) :
    PackedCipherSource.familyCipher (c := c) world enc dummy (slots (.inr ())) =
      ∑ index : Fin d, PackedCipherSource.familyCipher (c := c) world enc dummy (slots (.inl (index,false))) *
        PackedCipherSource.familyCipher (c := c) world enc dummy (slots (.inl (index,true))) := by
  have same : cipher (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough) dummy capacity radius owner =
      fun factor => PackedCipherSource.familyCipher (c := c) world enc dummy (slots factor) := by
    funext factor
    exact (cipher_family_eq_or_bad (KeySwitchPaddedProduct.stage s enc family firstSmall roundSmall nodesEnough)
      world (slots factor) factor dummy capacity radius (associated factor) state audited worldRecorded owner
      (ownerRetained factor) (ownerRoots factor)).resolve_right noBad
  have checked := native_identity_of_not_risk s enc family firstSmall roundSmall nodesEnough dummy capacity radius outcome owner recorded passes clear
  rw [same] at checked
  exact checked

end
end FormalProof4FHE.HasteBoots.DecodedPaddedProduct
