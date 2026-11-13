module
public import FormalProof4FHE.HasteBoots.ExecutedPaddedSourceFamily
public import FormalProof4FHE.HasteBoots.DecodedPaddedReconstruction
@[expose] public section

/-! The native reconstruction builds its input/digit/borrow family from actual
recorded snapshots. Its field constraints act on these constructed values. -/
namespace FormalProof4FHE.HasteBoots.ExecutedKeySwitchReconstruction
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

/-- Construct the input/digit/borrow family from the literal native prefix. -/
abbrev sourceFamily := ExecutedPaddedSourceFamily.linearFamily
  (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) capacity radius

omit [DecidableEq Input] in
/-- The original row packing and the constructed family yield one ciphertext. -/
theorem cipher_eq (dummy : Digest)
    (first : PaddedLinear.Prefix (count := 2*d+2) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights)
    (factor : Fin (2*d+2)) :
    DecodedPaddedReconstruction.cipher (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix)
      dummy capacity radius (HeterogeneousBatchOpening.snapshots heights s.tag first) factor =
      PackedCipherSource.familyCipher (c := c) (sourceFamily s enc input family nodesEnough radix capacity radius first) enc dummy factor := by
  unfold DecodedPaddedReconstruction.cipher
  rw [ExecutedPaddedSourceFamily.linear_logical,PackedCipherSource.ofRows_family]

variable [SampleableType Digest] [SampleableType (Fin (2^lanes) → ZMod q)]
  [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(s.code factor).front) (2^lanes))]
  [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^heights (s.tag factor)))]
variable (dummy : Digest)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : PaddedLinear.Prefix (count := 2*d+2) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
    PaddedLinear.RunResult (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix))
  (supported : outcome ∈ support (PaddedLinear.witness (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy initial))

include supported in
/-- Actual reconstruction records every original input/digit/borrow owner. -/
theorem sourceFamily_recorded :
    RecordedPaddedSourceFamily.Recorded
      (sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) outcome.2.2 :=
  ExecutedPaddedSourceFamily.linear_recorded_witness
    (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius initial outcome supported

include supported in
/-- Input and digit anchors retain the caller's roots. Borrow roots remain
the actual newly emitted roots preserved by the family construction. -/
theorem sourceFamily_expected_roots :
    (sourceFamily s enc input family nodesEnough radix capacity radius outcome.1).roots DecompositionLinear.input = input.root ∧
      ∀ digit : Fin d, (sourceFamily s enc input family nodesEnough radix capacity radius outcome.1).roots
        (DecompositionLinear.digit digit) = family.coefficients (Fin.castSucc digit) :=
  KeySwitchPaddedReconstruction.witness_expected_roots s enc input family nodesEnough radix dummy initial outcome supported

include supported in
/-- The actual trusted relation list constrains the entire constructed family. -/
theorem sourceFamily_relation
    (passes : PaddedLinear.accepted (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) outcome.2.1 = true)
    (clear : ¬PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius outcome) :
    DecompositionLinear.Relation radix
      (RecordedPaddedSourceFamily.logical (sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) enc dummy (1+c)) := by
  have recorded := sourceFamily_recorded s enc input family nodesEnough radix capacity radius dummy initial outcome supported
  have checked := DecodedPaddedReconstruction.relation_of_not_risk s enc input family nodesEnough radix dummy capacity radius outcome
    (HeterogeneousBatchOpening.snapshots heights s.tag outcome.1) (fun factor => ⟨rfl,recorded factor⟩) passes clear
  have same : PaddedLinear.originalSources (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix)
      dummy capacity radius (HeterogeneousBatchOpening.snapshots heights s.tag outcome.1) =
      RecordedPaddedSourceFamily.logical (sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) enc dummy (1+c) := by
    funext factor
    exact ExecutedPaddedSourceFamily.linear_logical (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix)
      dummy capacity radius outcome.1 factor
  rw [same] at checked
  exact checked

include supported in
/-- The constructed ciphertexts satisfy radix reconstruction and zero endpoint
borrows at every coefficient of both halves. -/
theorem sourceFamily_coefficients
    (passes : PaddedLinear.accepted (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) outcome.2.1 = true)
    (clear : ¬PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius outcome) :
    ∀ half index,
      PackedCipherSource.familyCipher (c := c) (sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) enc dummy DecompositionLinear.input half index =
        ∑ digit : Fin d, radix^digit.val * PackedCipherSource.familyCipher (c := c)
          (sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) enc dummy (DecompositionLinear.digit digit) half index ∧
      PackedCipherSource.familyCipher (c := c) (sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) enc dummy DecompositionLinear.firstBorrow half index = 0 ∧
      PackedCipherSource.familyCipher (c := c) (sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) enc dummy DecompositionLinear.lastBorrow half index = 0 := by
  have recorded := sourceFamily_recorded s enc input family nodesEnough radix capacity radius dummy initial outcome supported
  have checked := DecodedPaddedReconstruction.native_coefficients_of_not_risk s enc input family nodesEnough radix dummy capacity radius outcome
    (HeterogeneousBatchOpening.snapshots heights s.tag outcome.1) (fun factor => ⟨rfl,recorded factor⟩) passes clear
  have same := funext (cipher_eq s enc input family nodesEnough radix capacity radius dummy outcome.1)
  rw [same] at checked
  exact checked

include supported in
/-- A false constructed-family reconstruction is covered by the native
original-owner risk whenever that actual stage accepts. -/
theorem wrong_relation_implies_risk
    (passes : PaddedLinear.accepted (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) outcome.2.1 = true)
    (wrong : ¬DecompositionLinear.Relation radix
      (RecordedPaddedSourceFamily.logical (sourceFamily s enc input family nodesEnough radix capacity radius outcome.1) enc dummy (1+c))) :
    PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius outcome := by
  by_contra clear
  exact wrong (sourceFamily_relation s enc input family nodesEnough radix capacity radius dummy initial outcome supported passes clear)

/-- Accepted false relations of the execution-built family inherit the native
original-owner risk bound under the same single final collision exclusion. -/
theorem false_relation_safe_le_original :
    Pr{let actual ← (PaddedLinear.witness (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy initial)}[
      PaddedLinear.accepted (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) actual.2.1 = true ∧
      ¬DecompositionLinear.Relation radix (RecordedPaddedSourceFamily.logical (sourceFamily s enc input family nodesEnough radix capacity radius actual.1) enc dummy (1+c)) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) actual.2.2] ≤
    Pr{let actual ← (PaddedLinear.witness (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy initial)}[
      PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy capacity radius actual ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) actual.2.2] := by
  apply prEvent_mono_of_support
  intro actual present event
  exact ⟨wrong_relation_implies_risk s enc input family nodesEnough radix capacity radius dummy initial actual present event.1 event.2.1,event.2.2⟩

end
end FormalProof4FHE.HasteBoots.ExecutedKeySwitchReconstruction
