module
public import FormalProof4FHE.HasteBoots.PackedCipherSource
public import FormalProof4FHE.HasteBoots.KeySwitchPaddedExtraction
public import FormalProof4FHE.HasteBoots.PaddedStageSourceInterpretation
@[expose] public section

/-! Semantic extraction of the coefficient value constructed from the actual
retained private source. No equality to an independently supplied increment
is a security hypothesis. Earlier key-switch constraints must still establish
that this decoded value is the canonical signed key-product increment. -/
namespace FormalProof4FHE.HasteBoots.DecodedPaddedExtraction
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {q d c lanes dimension : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}

variable (s : KeySwitchPaddedExtraction.Scheme (q := q) (c := c) (lanes := lanes) (Input := Input) (Cfg := Cfg)
  (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (heights := heights))

/-- Construct the increment from the complete logical view of its retained owner. -/
def increment (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Unit → ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor)) :=
  PackedCipherSource.unpack (PaddedPublicZeroCheck.originalSources s dummy capacity radius owner ())

omit [DecidableEq Input] in
/-- The private source is the exact packing of the constructed increment. -/
theorem source_eq_pack (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Unit → ℕ)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor)) :
    PaddedPublicZeroCheck.originalSources s dummy capacity radius owner =
      fun _ : Unit => KeySwitchExtraction.pack (increment s dummy capacity radius owner) := by
  funext factor
  cases factor
  exact (PackedCipherSource.pack_unpack _).symm

omit [DecidableEq Input] in
/-- Accepted incorrect extraction of the decoded root value is an actual
original-owner stage risk, without a supplied source interpretation equality. -/
theorem wrong_implies_risk
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (family : PackedPBSOriginalReferences.Family d) (shape : dimension ≤ 2^(c+lanes)) (positive : 0 < dimension)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Unit → ℕ)
    (outcome : PaddedPublicZeroCheck.Prefix (Private := Unit) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedPublicZeroCheck.RunResult (KeySwitchPaddedExtraction.stage s enc family positive acc output firstSmall roundSmall nodesEnough))
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧
      ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (wrong : ¬CanonicalKeySwitch.Extraction shape (NativePBS.bias (acc outcome.1.1))
      (increment (KeySwitchPaddedExtraction.stage s enc family positive acc output firstSmall roundSmall nodesEnough) dummy capacity radius owner)
      (output outcome.1.1))
    (passes : PaddedPublicZeroCheck.accepted (KeySwitchPaddedExtraction.stage s enc family positive acc output firstSmall roundSmall nodesEnough) outcome.2.1 = true) :
    PaddedPublicZeroCheck.OriginalRisk (KeySwitchPaddedExtraction.stage s enc family positive acc output firstSmall roundSmall nodesEnough)
      dummy capacity radius outcome :=
  KeySwitchPaddedExtraction.wrong_extraction_implies_originalRisk s enc family shape positive acc output firstSmall roundSmall nodesEnough
    dummy capacity radius outcome owner recorded _
    (source_eq_pack (KeySwitchPaddedExtraction.stage s enc family positive acc output firstSmall roundSmall nodesEnough) dummy capacity radius owner)
    wrong passes

omit [DecidableEq Input] in
/-- Clearing the actual extraction risk enforces extraction of the decoded
private coefficient root, rather than an asserted increment witness. -/
theorem extraction_of_not_risk
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (family : PackedPBSOriginalReferences.Family d) (shape : dimension ≤ 2^(c+lanes)) (positive : 0 < dimension)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Unit → ℕ)
    (outcome : PaddedPublicZeroCheck.Prefix (Private := Unit) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedPublicZeroCheck.RunResult (KeySwitchPaddedExtraction.stage s enc family positive acc output firstSmall roundSmall nodesEnough))
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (recorded : ∀ factor, (owner factor).root = outcome.1.1.1 factor ∧
      ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints)
    (passes : PaddedPublicZeroCheck.accepted (KeySwitchPaddedExtraction.stage s enc family positive acc output firstSmall roundSmall nodesEnough) outcome.2.1 = true)
    (clear : ¬PaddedPublicZeroCheck.OriginalRisk (KeySwitchPaddedExtraction.stage s enc family positive acc output firstSmall roundSmall nodesEnough)
      dummy capacity radius outcome) :
    CanonicalKeySwitch.Extraction shape (NativePBS.bias (acc outcome.1.1))
      (increment (KeySwitchPaddedExtraction.stage s enc family positive acc output firstSmall roundSmall nodesEnough) dummy capacity radius owner)
      (output outcome.1.1) := by
  by_contra wrong
  exact clear (wrong_implies_risk s enc family shape positive acc output firstSmall roundSmall nodesEnough
    dummy capacity radius outcome owner recorded wrong passes)
variable {Index : Type}

/-- Under public descriptor association the constructed increment agrees with
the family's common coefficient value, outside the same final exception. -/
theorem increment_family_eq_or_bad
    (family : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Index heights (2^lanes))
    (index : Index) (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Unit → ℕ)
    (associated : PaddedStageSourceInterpretation.publicZeroParameters s capacity radius () = family.parameters index)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape heights) state)
    (familyRecorded : RecordedPaddedSourceFamily.Recorded family state)
    (owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor))
    (ownerRecorded : ⟨s.tag (),owner ()⟩ ∈ state.checkpoints.checkpoints)
    (ownerRoot : (owner ()).root = family.roots index) :
    increment s dummy capacity radius owner = PackedCipherSource.familyCipher (c := c) family s.encoding dummy index ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  have compared := RecordedPaddedSourceFamily.associated_owner_agrees_or_bad family s.encoding dummy (c+1) index
    (PaddedStageSourceInterpretation.publicZeroParameters s capacity radius ()) associated state audited
    familyRecorded (owner ()) ownerRecorded ownerRoot
  rcases compared with same | bad
  · left
    unfold increment PackedCipherSource.familyCipher
    rw [PaddedStageSourceInterpretation.publicZero_original,same]
  · exact Or.inr bad

/-- Incorrect extraction is stated for the decoded value of a retained owner;
no supplied increment or source-value equality appears in this event. -/
def OriginalFalse (shape : dimension ≤ 2^(c+lanes)) (dummy : Digest)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Unit → ℕ)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (outcome : PaddedPublicZeroCheck.Prefix (Private := Unit) (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) heights ×
      PaddedPublicZeroCheck.RunResult s) : Prop :=
  ∃ owner : ∀ factor, AmbientMatrixSource.Snapshot Input Digest heights (s.tag factor),
    (∀ factor, (owner factor).root = outcome.1.1.1 factor ∧ ⟨s.tag factor,owner factor⟩ ∈ outcome.2.2.checkpoints.checkpoints) ∧
    ¬CanonicalKeySwitch.Extraction shape (NativePBS.bias (acc outcome.1.1))
      (increment s dummy capacity radius owner) (output outcome.1.1) ∧
    PaddedPublicZeroCheck.accepted s outcome.2.1 = true

variable [SampleableType (Fin (2^lanes) → ZMod q)] [SampleableType (PackedZeroReduction.Points (ZMod q) c (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)] [SampleableType Digest]
  [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(s.code factor).front) (2^lanes))]
  [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^heights (s.tag factor)))]

variable {K : Type} [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [SampleableType (ZMod q)] [SampleableType (Fin c → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]
  [∀ factor, SampleableType ((Fin (2^(s.code factor).front) × Fin (2^lanes)) → K)]

/-- The existing native extraction rate bounds accepted semantic extraction
failure of the actual decoded root value, without any interpretation certificate. -/
theorem semantic_safe_bound [NeZero (2^lanes)] [∀ factor, NeZero (s.code factor).m]
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (shape : dimension ≤ 2^(c+lanes)) (positive : 0 < dimension)
    (acc : ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q) (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (basis : Module.Basis (Fin (2^lanes)) (ZMod q) K) (dummy : Digest)
    (enough : ∀ factor, (s.code factor).m ≤ Fintype.card (Fin (2^heights (s.tag factor))))
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(2^lanes)) (radius : Unit → ℕ)
    (small : ∀ factor, (radius factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) (s.domain factor)) (s.code factor).m :
        Set (Fin (2^heights (s.tag factor)) → K)) : ℚ≥0)/3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) initial) :
    Pr{let outcome ← (PaddedPublicZeroCheck.witness (KeySwitchPaddedExtraction.stage s enc family positive acc output firstSmall roundSmall nodesEnough) dummy initial)}[
      OriginalFalse (KeySwitchPaddedExtraction.stage s enc family positive acc output firstSmall roundSmall nodesEnough) shape dummy capacity radius acc output outcome ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) outcome.2.2] ≤
      (((c : ENNReal)/Fintype.card (ZMod q))^(2^lanes) + ((((((2*(2^lanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes))) +
        (c : ENNReal)*((((((2*(2^lanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (([()]).map (fun factor => JointMatrixOpening.error (K := K) (m := (s.code factor).m) (b := 2^lanes)
        (queries := (s.code factor).queries) (s.domain factor) (radius factor))).sum := by
  have bounded := KeySwitchPaddedExtraction.original_safe_bound s enc family positive acc output firstSmall roundSmall nodesEnough
    basis dummy enough capacity radius small initial audited
  apply le_trans (prEvent_mono _ _ _ ?_) bounded
  intro outcome event
  obtain ⟨⟨owner,recorded,wrong,passes⟩,clear⟩ := event
  exact ⟨wrong_implies_risk s enc family shape positive acc output firstSmall roundSmall nodesEnough
    dummy capacity radius outcome owner recorded wrong passes,clear⟩

end
end FormalProof4FHE.HasteBoots.DecodedPaddedExtraction
