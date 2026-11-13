module
public import FormalProof4FHE.HasteBoots.KeySwitchPaddedNTT
public import FormalProof4FHE.HasteBoots.AcceptedKeySwitchNTT
public import FormalProof4FHE.HasteBoots.DecodedFamilyNTT
public import FormalProof4FHE.HasteBoots.DecodedPaddedExtraction
public import FormalProof4FHE.HasteBoots.RecordedSourceWorldTransport
@[expose] public section

/-! Relate the actual extraction coefficient owner to the accepted key-switch
NTT result and its final canonical source world under public decoder metadata. -/
namespace FormalProof4FHE.HasteBoots.ExecutedExtractionNTTLink
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

variable
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ) (passes : outcome.1.accepted = true)
variable {ExtractionResponse ExtractionCommitMemory : Type} {dimension : ℕ}
    (extraction : KeySwitchPaddedExtraction.Scheme (q := q) (c := c) (lanes := lanes) (Input := Input) (Cfg := Cfg)
      (Response := ExtractionResponse) (Memory := Memory) (CommitMemory := ExtractionCommitMemory) (heights := heights))
    (positive : 0 < dimension)
    (accumulator : ((Unit → Digest) × ExtractionCommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : ((Unit → Digest) × ExtractionCommitMemory) → NativePublic.Ciphertext q dimension)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (extractionNodes : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (extractionCapacity : ∀ factor, 2^(extraction.code factor).suffix ≤ (extraction.code factor).m*(2^lanes))
    (extractionRadius : Unit → ℕ)
    [SampleableType (PackedZeroReduction.Points (ZMod q) c (2^lanes))]
    [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
    [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(extraction.code factor).front) (2^lanes))]
    [∀ factor, SampleableType (Fin (extraction.code factor).queries → Fin (2^heights (extraction.tag factor)))]
    (extractionInitial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (extractionOutcome : PaddedPublicZeroCheck.Prefix (Private := Unit) (Input := Input) (Digest := Digest) (CommitMemory := ExtractionCommitMemory) heights ×
      PaddedPublicZeroCheck.RunResult (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes))
    (extractionSupported : extractionOutcome ∈ support (PaddedPublicZeroCheck.witness (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes) dummy extractionInitial))

include extractionSupported in
omit [SampleableType (Fin (2^lanes) → Fin 1 → ZMod q)] in
/-- The actual fresh extraction owner has the caller's last coefficient root
and remains recorded after every opening, including rejected openings. -/
theorem owner_recorded :
    ((HeterogeneousBatchOpening.snapshots heights (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes).tag extractionOutcome.1) ()).root = family.coefficients (Fin.last d) ∧
      ⟨(KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes).tag (),(HeterogeneousBatchOpening.snapshots heights (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes).tag extractionOutcome.1) ()⟩ ∈ extractionOutcome.2.2.checkpoints.checkpoints := by
  have roots := KeySwitchPaddedExtraction.witness_roots extraction enc family positive accumulator output firstSmall roundSmall extractionNodes dummy extractionInitial extractionOutcome extractionSupported
  have recorded := PaddedPublicZeroCheck.fresh_recorded (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes)
    dummy extractionInitial extractionOutcome extractionSupported
    (fun factor => by cases factor; exact List.mem_singleton_self ()) ()
  exact ⟨congrFun roots (),recorded⟩

variable (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (nttRetained : CheckpointHistoryChain.Retains outcome.2 state)
    (extractionRetained : CheckpointHistoryChain.Retains extractionOutcome.2.2 state)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (associated : PaddedStageSourceInterpretation.publicZeroParameters (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes) extractionCapacity extractionRadius () =
      (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes).parameters (Fin.last d,false))

include supported extractionSupported nttRetained extractionRetained audited associated in
/-- Actual accepted NTT and extraction executions refer to the same coefficient
value under public decoder association, outside the same final collision event. -/
theorem increment_eq_ntt_or_bad :
    DecodedPaddedExtraction.increment (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes) dummy extractionCapacity extractionRadius (HeterogeneousBatchOpening.snapshots heights (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes).tag extractionOutcome.1) =
      PackedCipherSource.familyCipher (c := c) (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) enc dummy (Fin.last d,false) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  have actual := owner_recorded enc family dummy extraction positive accumulator output firstSmall roundSmall extractionNodes extractionInitial extractionOutcome extractionSupported
  exact DecodedPaddedExtraction.increment_family_eq_or_bad (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes) (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) (Fin.last d,false)
    dummy extractionCapacity extractionRadius associated state audited (CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 state nttRetained (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)) (HeterogeneousBatchOpening.snapshots heights (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes).tag extractionOutcome.1)
    (extractionRetained _ _ actual.2) actual.1

include supported extractionSupported nttRetained extractionRetained audited associated in
/-- The extraction increment is the exact result slot of the final canonical
source world used by the executed key-switch increment theorem. -/
theorem increment_eq_world_or_bad :
    DecodedPaddedExtraction.increment (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes) dummy extractionCapacity extractionRadius (HeterogeneousBatchOpening.snapshots heights (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes).tag extractionOutcome.1) =
      PackedCipherSource.familyCipher (c := c) (RecordedSourceWorld.family state) enc dummy (RecordedSourceWorld.slot (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) state (CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 state nttRetained (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)) (Fin.last d,false)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  rcases increment_eq_ntt_or_bad base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes extraction positive accumulator output firstSmall roundSmall extractionNodes extractionCapacity extractionRadius extractionInitial extractionOutcome extractionSupported state nttRetained extractionRetained audited associated with equal | bad
  · rcases RecordedSourceWorld.cipher_eq_or_bad (c := c) (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) enc dummy state audited (CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 state nttRetained (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)) with transferred | bad
    · exact Or.inl (equal.trans (congrFun transferred (Fin.last d,false)))
    · exact Or.inr bad
  · exact Or.inr bad

include supported extractionSupported nttRetained extractionRetained audited associated in
/-- Actual accepted extraction enforces the canonical extraction equation on
the NTT result's final-world value, or its original risk or the same final bad event. -/
theorem extraction_world_or_risks (shape : dimension ≤ 2^(c+lanes))
    (extractionPassed : PaddedPublicZeroCheck.accepted (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes) extractionOutcome.2.1 = true) :
    CanonicalKeySwitch.Extraction shape (NativePBS.bias (accumulator extractionOutcome.1.1))
      (PackedCipherSource.familyCipher (c := c) (RecordedSourceWorld.family state) enc dummy (RecordedSourceWorld.slot (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) state (CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 state nttRetained (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)) (Fin.last d,false)))
      (output extractionOutcome.1.1) ∨
    PaddedPublicZeroCheck.OriginalRisk (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes) dummy extractionCapacity extractionRadius extractionOutcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  classical
  by_cases risk : PaddedPublicZeroCheck.OriginalRisk (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes) dummy extractionCapacity extractionRadius extractionOutcome
  · exact Or.inr (Or.inl risk)
  have recorded : ∀ factor, ((HeterogeneousBatchOpening.snapshots heights (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes).tag extractionOutcome.1) factor).root = extractionOutcome.1.1.1 factor ∧
      ⟨(KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes).tag factor,(HeterogeneousBatchOpening.snapshots heights (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes).tag extractionOutcome.1) factor⟩ ∈ extractionOutcome.2.2.checkpoints.checkpoints := by
    intro factor
    cases factor
    exact ⟨rfl,(owner_recorded enc family dummy extraction positive accumulator output firstSmall roundSmall extractionNodes extractionInitial extractionOutcome extractionSupported).2⟩
  have checked := DecodedPaddedExtraction.extraction_of_not_risk extraction enc family shape positive accumulator output
    firstSmall roundSmall extractionNodes dummy extractionCapacity extractionRadius extractionOutcome (HeterogeneousBatchOpening.snapshots heights (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes).tag extractionOutcome.1)
    recorded extractionPassed risk
  rcases increment_eq_world_or_bad base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes extraction positive accumulator output firstSmall roundSmall extractionNodes extractionCapacity extractionRadius extractionInitial extractionOutcome extractionSupported state nttRetained extractionRetained audited associated with equal | bad
  · rw [equal] at checked
    exact Or.inl checked
  · exact Or.inr (Or.inr bad)

include supported extractionSupported extractionRetained audited associated in
/-- Compose canonical increment correctness at the earlier comparison state
with actual accepted extraction. Retained history supplies the value transfer;
only the extraction's existing risk and the one final collision event remain. -/
theorem output_of_earlier_increment_or_risks (bits : ℕ)
    (original : NativeKeySwitch.Key q (2^(c+lanes)) d)
    (earlier : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (nttEarlier : CheckpointHistoryChain.Retains outcome.2 earlier)
    (later : CheckpointHistoryChain.Retains earlier state)
    (correct : PackedCipherSource.familyCipher (c := c) (RecordedSourceWorld.family earlier) enc dummy
      (RecordedSourceWorld.slot (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) earlier (CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 earlier nttEarlier (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)) (Fin.last d,false)) =
      CanonicalKeySwitch.increment bits original ((accumulator extractionOutcome.1.1) false))
    (shape : dimension ≤ 2^(c+lanes))
    (extractionPassed : PaddedPublicZeroCheck.accepted (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes) extractionOutcome.2.1 = true) :
    output extractionOutcome.1.1 = NativeKeySwitch.extract shape
      (CanonicalKeySwitch.switch bits original (NativePBS.bias (accumulator extractionOutcome.1.1))) ∨
    PaddedPublicZeroCheck.OriginalRisk (KeySwitchPaddedExtraction.stage extraction enc family positive accumulator output firstSmall roundSmall extractionNodes) dummy extractionCapacity extractionRadius extractionOutcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  rcases extraction_world_or_risks base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes extraction positive accumulator output firstSmall roundSmall extractionNodes extractionCapacity extractionRadius extractionInitial extractionOutcome extractionSupported state (CheckpointHistoryChain.trans nttEarlier later) extractionRetained audited associated shape extractionPassed with extracted | risk | bad
  · have transferred := RecordedSourceWorldTransport.equality_persistent (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) enc dummy earlier state
      (CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 earlier nttEarlier (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)) later audited (Fin.last d,false)
      (CanonicalKeySwitch.increment bits original ((accumulator extractionOutcome.1.1) false)) correct
    rcases transferred with incrementCorrect | bad
    · rw [incrementCorrect] at extracted
      exact Or.inl (CanonicalKeySwitch.extract_of_constraints shape (NativePBS.bias (accumulator extractionOutcome.1.1))
        (CanonicalKeySwitch.increment bits original ((accumulator extractionOutcome.1.1) false))
        (output extractionOutcome.1.1) extracted)
    · exact Or.inr (Or.inr bad)
  · exact Or.inr (Or.inl risk)
  · exact Or.inr (Or.inr bad)

end
end FormalProof4FHE.HasteBoots.ExecutedExtractionNTTLink
