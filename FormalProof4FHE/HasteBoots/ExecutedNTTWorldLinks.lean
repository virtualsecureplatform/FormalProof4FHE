module
public import FormalProof4FHE.HasteBoots.AcceptedKeySwitchNTT
public import FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
public import FormalProof4FHE.HasteBoots.RecordedSourceWorld
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchProduct
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchReconstruction
@[expose] public section

/-! Canonical slots identify actual executed NTT sources with the original
reconstruction and product sources. Caller-root identities are derived from
support; only public decoder routing remains as an explicit condition. -/
namespace FormalProof4FHE.HasteBoots.ExecutedNTTWorldLinks
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

/-- The selected child's actual scheduled index is the requested index. -/
theorem selected_index (passes : outcome.1.accepted = true) (index : Fin (d+1)) :
    (AcceptedKeySwitchNTT.selected base enc family nodesEnough psi primitive dummy memory initial outcome supported passes index).1.1 = index :=
  (Classical.choose_spec (AcceptedKeySwitchNTT.accepted_child base enc family nodesEnough psi primitive dummy memory initial outcome supported passes index)).2

variable
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ) (passes : outcome.1.accepted = true)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (nttRetained : CheckpointHistoryChain.Retains outcome.2 state)

section Reconstruction
variable {ReconstructionResponse ReconstructionCommitMemory : Type}
    (reconstruction : PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory heights (2*d+2) (2^lanes) (1+c))
    (input : NativeGoldParameterStore.Reference) (radix : ZMod q)
    (reconstructionCapacity : ∀ factor, 2^(reconstruction.code factor).suffix ≤ (reconstruction.code factor).m*(2^lanes))
    (reconstructionRadius : Fin (2*d+2) → ℕ)
    [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(reconstruction.code factor).front) (2^lanes))]
    [∀ factor, SampleableType (Fin (reconstruction.code factor).queries → Fin (2^heights (reconstruction.tag factor)))]
    (reconstructionInitial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (reconstructionOutcome : PaddedLinear.Prefix (count := 2*d+2) (Input := Input) (Digest := Digest) (CommitMemory := ReconstructionCommitMemory) heights ×
      PaddedLinear.RunResult (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough radix))
    (reconstructionSupported : reconstructionOutcome ∈ support (PaddedLinear.witness
      (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough radix) dummy reconstructionInitial))
    (reconstructionRetained : CheckpointHistoryChain.Retains reconstructionOutcome.2.2 state)

include supported reconstructionSupported in
/-- Exact public decoder routing and the actual caller-root theorems identify
these canonical slots without a source-value, root-alias or safety premise. -/
theorem coefficient_slot
    (routing : ∀ (level : Fin d) memory, PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive (Fin.castSucc level) memory)
      (capacity (Fin.castSucc level) memory) (radius (Fin.castSucc level) memory) false =
      PaddedStageSourceInterpretation.linearParameters (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough radix) reconstructionCapacity reconstructionRadius (DecompositionLinear.digit level))
    (level : Fin d) :
    let nttRecorded := CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 state nttRetained
      (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)
    let otherRecorded := CheckpointHistoryChain.family_recorded (ExecutedKeySwitchReconstruction.sourceFamily reconstruction enc input family nodesEnough radix reconstructionCapacity reconstructionRadius reconstructionOutcome.1) reconstructionOutcome.2.2 state reconstructionRetained
      (ExecutedKeySwitchReconstruction.sourceFamily_recorded reconstruction enc input family nodesEnough radix reconstructionCapacity reconstructionRadius dummy reconstructionInitial reconstructionOutcome reconstructionSupported)
    RecordedSourceWorld.slot (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) state nttRecorded (Fin.castSucc level,false) =
      RecordedSourceWorld.slot (ExecutedKeySwitchReconstruction.sourceFamily reconstruction enc input family nodesEnough radix reconstructionCapacity reconstructionRadius reconstructionOutcome.1) state otherRecorded (DecompositionLinear.digit level) := by
  dsimp only
  apply RecordedSourceWorld.slot_eq
  · let child := AcceptedKeySwitchNTT.selected base enc family nodesEnough psi primitive dummy memory initial outcome supported passes (Fin.castSucc level)
    change PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive child.1.1 child.1.2)
      (capacity child.1.1 child.1.2) (radius child.1.1 child.1.2) false = _
    have same : child.1.1 = Fin.castSucc level := selected_index base enc family nodesEnough psi primitive dummy memory initial outcome supported passes (Fin.castSucc level)
    rw [same]
    exact routing level child.1.2
  · have expected := ExecutedKeySwitchReconstruction.sourceFamily_expected_roots reconstruction enc input family nodesEnough radix reconstructionCapacity reconstructionRadius dummy reconstructionInitial reconstructionOutcome reconstructionSupported
    exact (expected.2 level).symm

end Reconstruction
section Product
variable {ProductResponse ProductCommitMemory : Type}
    (product : KeySwitchPaddedProduct.Scheme (q := q) (d := d) (b := 2^lanes) (n := c)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := heights))
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (productNodes : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (productCapacity : ∀ factor, 2^(product.code factor).suffix ≤ (product.code factor).m*(2^lanes))
    (productRadius : PBSHadamard.Factor d → ℕ)
    [SampleableType (PackedZeroReduction.Points (ZMod q) c (2^lanes))]
    [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
    [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(product.code factor).front) (2^lanes))]
    [∀ factor, SampleableType (Fin (product.code factor).queries → Fin (2^heights (product.tag factor)))]
    (productInitial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (productOutcome : PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := ProductCommitMemory) heights ×
      PaddedZeroCheck.RunResult (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes))
    (productSupported : productOutcome ∈ support (PaddedZeroCheck.witness
      (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes) dummy productInitial))
    (productRetained : CheckpointHistoryChain.Retains productOutcome.2.2 state)

include supported productSupported in
/-- Exact public decoder routing and the actual caller-root theorems identify
these canonical slots without a source-value, root-alias or safety premise. -/
theorem evaluation_slot
    (routing : ∀ index memory, PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive index memory)
      (capacity index memory) (radius index memory) true =
      PaddedStageSourceInterpretation.zeroParameters (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes) productCapacity productRadius (PackedPBSOriginalReferences.evaluationFactor index))
    (index : Fin (d+1)) :
    let nttRecorded := CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 state nttRetained
      (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)
    let otherRecorded := CheckpointHistoryChain.family_recorded (ExecutedKeySwitchProduct.sourceFamily product enc family firstSmall roundSmall productNodes productCapacity productRadius productOutcome.1) productOutcome.2.2 state productRetained
      (ExecutedKeySwitchProduct.sourceFamily_recorded product enc family firstSmall roundSmall productNodes productCapacity productRadius dummy productInitial productOutcome productSupported)
    RecordedSourceWorld.slot (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) state nttRecorded (index,true) =
      RecordedSourceWorld.slot (ExecutedKeySwitchProduct.sourceFamily product enc family firstSmall roundSmall productNodes productCapacity productRadius productOutcome.1) state otherRecorded (PackedPBSOriginalReferences.evaluationFactor index) := by
  dsimp only
  apply RecordedSourceWorld.slot_eq
  · let child := AcceptedKeySwitchNTT.selected base enc family nodesEnough psi primitive dummy memory initial outcome supported passes (index)
    change PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive child.1.1 child.1.2)
      (capacity child.1.1 child.1.2) (radius child.1.1 child.1.2) true = _
    have same : child.1.1 = index := selected_index base enc family nodesEnough psi primitive dummy memory initial outcome supported passes (index)
    rw [same]
    exact routing index child.1.2
  · have expected := ExecutedKeySwitchProduct.sourceFamily_roots product enc family firstSmall roundSmall productNodes productCapacity productRadius dummy productInitial productOutcome productSupported
    rw [expected]
    change family.evaluations index = (PackedPBSOriginalReferences.roleReference family (PackedPBSOriginalReferences.evaluationFactor index)).root
    rw [PackedPBSOriginalReferences.evaluation_reference]

end Product

end
end FormalProof4FHE.HasteBoots.ExecutedNTTWorldLinks
