module
public import FormalProof4FHE.HasteBoots.PackedCipherSource
public import FormalProof4FHE.HasteBoots.KeySwitchPaddedReconstruction
public import FormalProof4FHE.HasteBoots.PaddedStageSourceInterpretation
@[expose] public section

/-! Radix reconstruction and borrow endpoints of the actual decoded input,
digit and borrow sources. These are coefficient-domain constraints, not an
asserted identification with independently supplied digit polynomials. -/
namespace FormalProof4FHE.HasteBoots.DecodedPaddedReconstruction
open OracleSpec OracleComp BinaryTree
open scoped BigOperators
open NativeRootMessage (Digest)
noncomputable section
variable {q d c lanes : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}

variable (s : PaddedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory heights (2*d+2) (2^lanes) (1+c))

/-- The same complete NTT-row packing constructs every retained linear source. -/
def cipher (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Fin (2*d+2) → ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor)) (factor : Fin (2*d+2)) :=
  PackedCipherSource.ofRows (PaddedLinear.originalSources s dummy capacity radius owner factor)

omit [DecidableEq Input] in
/-- Full logical-table reconstruction implies reconstruction of every decoded
ciphertext coefficient and zero first/last borrows on each half. -/
theorem coefficients_of_relation (radix : ZMod q) (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Fin (2*d+2) → ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (relation : DecompositionLinear.Relation radix (PaddedLinear.originalSources s dummy capacity radius owner)) :
    ∀ half index,
      cipher s dummy capacity radius owner DecompositionLinear.input half index =
        ∑ digit : Fin d, radix^digit.val * cipher s dummy capacity radius owner (DecompositionLinear.digit digit) half index ∧
      cipher s dummy capacity radius owner DecompositionLinear.firstBorrow half index = 0 ∧
      cipher s dummy capacity radius owner DecompositionLinear.lastBorrow half index = 0 := by
  intro half index
  exact relation (Nat.add_comm c 1 ▸ PackedCipherSource.point ((PackedAccumulatorTrace.polynomial c lanes).symm index).1 half)
    ((PackedAccumulatorTrace.polynomial c lanes).symm index).2

omit [DecidableEq Input] in
/-- Absence of the actual original-owner risk forces the native trusted
relation list on the original source tables whenever the stage accepts. -/
theorem relation_of_not_risk
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (input : NativeGoldParameterStore.Reference) (family : PackedPBSOriginalReferences.Family d)
    (nodesEnough : 2*(2^lanes) ≤ q) (radix : ZMod q) (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Fin (2*d+2) → ℕ)
    (outcome : PaddedLinear.Prefix (count := 2*d+2) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedLinear.RunResult (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix))
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧ ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (passes : PaddedLinear.accepted (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) outcome.2.1 = true)
    (clear : ¬PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius outcome) :
    DecompositionLinear.Relation radix (PaddedLinear.originalSources (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix)
      dummy capacity radius owner) := by
  apply (KeySwitchPaddedReconstruction.relation s enc input family nodesEnough radix _).mp
  by_contra wrong
  exact clear ⟨owner,recorded,wrong,passes⟩

omit [DecidableEq Input] in
/-- Accepted native reconstruction enforces its exact decoded coefficient
constraints without a supplied interpretation of inputs, digits or borrows. -/
theorem native_coefficients_of_not_risk
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (input : NativeGoldParameterStore.Reference) (family : PackedPBSOriginalReferences.Family d)
    (nodesEnough : 2*(2^lanes) ≤ q) (radix : ZMod q) (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Fin (2*d+2) → ℕ)
    (outcome : PaddedLinear.Prefix (count := 2*d+2) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedLinear.RunResult (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix))
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧ ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (passes : PaddedLinear.accepted (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) outcome.2.1 = true)
    (clear : ¬PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius outcome) :
    ∀ half index,
      cipher (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius owner DecompositionLinear.input half index =
        ∑ digit : Fin d, radix^digit.val * cipher (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix)
          dummy capacity radius owner (DecompositionLinear.digit digit) half index ∧
      cipher (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius owner DecompositionLinear.firstBorrow half index = 0 ∧
      cipher (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius owner DecompositionLinear.lastBorrow half index = 0 :=
  coefficients_of_relation (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) radix dummy capacity radius owner
    (relation_of_not_risk s enc input family nodesEnough radix dummy capacity radius outcome owner recorded passes clear)

variable {Index : Type}

/-- Retained input/digit/borrow roots use the same common family values as the
other stages when their public decoder descriptors are associated. -/
theorem cipher_family_eq_or_bad
    (family : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (index : Index) (factor : Fin (2*d+2)) (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Fin (2*d+2) → ℕ)
    (associated : PaddedStageSourceInterpretation.linearParameters s capacity radius factor = family.parameters index)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) state)
    (familyRecorded : RecordedPaddedSourceFamily.Recorded family state)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (ownerRecorded : ⟨s.tag factor,owner factor⟩ ∈ state.checkpoints.checkpoints)
    (ownerRoot : (owner factor).root = family.roots index) :
    cipher s dummy capacity radius owner factor = PackedCipherSource.familyCipher (c := c) family s.encoding dummy index ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  have compared := RecordedPaddedSourceFamily.associated_owner_agrees_or_bad family s.encoding dummy (1+c) index
    (PaddedStageSourceInterpretation.linearParameters s capacity radius factor) associated state audited
    familyRecorded (owner factor) ownerRecorded ownerRoot
  rcases compared with same | bad
  · left
    unfold cipher
    rw [PaddedStageSourceInterpretation.linear_original,same,PackedCipherSource.ofRows_family]
  · exact Or.inr bad
/-- The executed reconstruction enforces input/digit reconstruction and both
borrow endpoints on the common family under the inherited final exclusion. -/
theorem native_family_coefficients_of_not_risk
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (input : NativeGoldParameterStore.Reference) (family : PackedPBSOriginalReferences.Family d)
    (nodesEnough : 2*(2^lanes) ≤ q) (radix : ZMod q) (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Fin (2*d+2) → ℕ)
    (outcome : PaddedLinear.Prefix (count := 2*d+2) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedLinear.RunResult (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix))
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧ ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (passes : PaddedLinear.accepted (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) outcome.2.1 = true)
    (clear : ¬PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius outcome)
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (slots : Fin (2*d+2) → Index)
    (associated : ∀ factor, PaddedStageSourceInterpretation.linearParameters
      (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) capacity radius factor = world.parameters (slots factor))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (worldRecorded : RecordedPaddedSourceFamily.Recorded world state)
    (ownerRetained : ∀ factor, ⟨s.tag factor,owner factor⟩ ∈ state.checkpoints.checkpoints)
    (ownerRoots : ∀ factor, (owner factor).root = world.roots (slots factor))
    (noBad : ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state) :
    ∀ half index,
      PackedCipherSource.familyCipher (c := c) world enc dummy (slots DecompositionLinear.input) half index =
        ∑ digit : Fin d, radix^digit.val * PackedCipherSource.familyCipher (c := c) world enc dummy (slots (DecompositionLinear.digit digit)) half index ∧
      PackedCipherSource.familyCipher (c := c) world enc dummy (slots DecompositionLinear.firstBorrow) half index = 0 ∧
      PackedCipherSource.familyCipher (c := c) world enc dummy (slots DecompositionLinear.lastBorrow) half index = 0 := by
  have same : cipher (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius owner =
      fun factor => PackedCipherSource.familyCipher (c := c) world enc dummy (slots factor) := by
    funext factor
    exact (cipher_family_eq_or_bad (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix)
      world (slots factor) factor dummy capacity radius (associated factor) state audited worldRecorded owner
      (ownerRetained factor) (ownerRoots factor)).resolve_right noBad
  have checked := native_coefficients_of_not_risk s enc input family nodesEnough radix dummy capacity radius outcome owner recorded passes clear
  rw [same] at checked
  exact checked

end
end FormalProof4FHE.HasteBoots.DecodedPaddedReconstruction
