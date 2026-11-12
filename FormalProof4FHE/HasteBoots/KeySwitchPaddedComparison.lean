module
public import FormalProof4FHE.HasteBoots.KeySwitchPaddedReconstruction
public import FormalProof4FHE.HasteBoots.PaddedReconstructionComparison
public import FormalProof4FHE.HasteBoots.KeySwitchPaddedComparisonConfig
@[expose] public section

/-! The reached final comparison borrows the actual canonical reconstruction
registry: caller-owned digit coefficients followed by its emitted borrow roots.
No independent comparison source roots or opening memory are supplied. Physical
source interpretation coherence and full-prefix composition remain separate. -/
namespace FormalProof4FHE.HasteBoots.KeySwitchPaddedComparison
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {q d b n : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory Helper Result : Type}
  [DecidableEq Input] [DecidableEq Digest] {H : Cfg → ℕ}
variable (s : PaddedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
variable [SampleableType (Fin b → ZMod q)] [SampleableType Digest]
  [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(s.code factor).front) b)]
  [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^H (s.tag factor)))]

/-- Both execution supports derive the comparison's original digit roots,
actual emitted borrow roots, opening memory and incoming history. This holds
for every reached comparison, including one that subsequently rejects. -/
theorem registry
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (input : NativeGoldParameterStore.Reference) (family : PackedPBSOriginalReferences.Family d)
    (nodesEnough : 2*b ≤ q) (radix : ZMod q) (dummy : Digest)
    (comparison : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (before : PaddedReconstructionComparison.Before (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix))
    (linearSupported : before ∈ support
      (PaddedLinear.witness (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) dummy initial))
    (outcome : PackedPBSComparisonStage.Outcome
      (PaddedReconstructionComparison.stage (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) comparison))
    (comparisonSupported : some outcome ∈ support (PaddedReconstructionComparison.continuation
      (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) comparison dummy before)) :
    (∀ i : Fin d, outcome.1.1.1 (PackedPBSComparisonReferences.digitSlot i) = family.coefficients (Fin.castSucc i)) ∧
    (∀ i : Fin (d+1), outcome.1.1.1 (PackedPBSComparisonReferences.borrowSlot i) =
      before.1.1.1 (DecompositionLinear.borrow i)) ∧
    outcome.1.1.2 = before.2.1.2.memory ∧ outcome.1.2 = before.2.2 := by
  have same := PaddedReconstructionComparison.sources
    (KeySwitchPaddedReconstruction.stage s enc input family nodesEnough radix) comparison dummy before outcome comparisonSupported
  have originals := KeySwitchPaddedReconstruction.witness_expected_roots s enc input family nodesEnough radix dummy initial before linearSupported
  refine ⟨?_,?_,?_,same.2⟩
  · intro i
    rw [same.1]
    change before.1.1.1 (PackedPBSComparisonReferences.linearSlot (PackedPBSComparisonReferences.digitSlot i)) = _
    rw [PackedPBSComparisonReferences.linear_digit]
    exact originals.2 i
  · intro i
    rw [same.1]
    change before.1.1.1 (PackedPBSComparisonReferences.linearSlot (PackedPBSComparisonReferences.borrowSlot i)) = _
    rw [PackedPBSComparisonReferences.linear_borrow]
  · exact congrArg Prod.snd same.1

end
end FormalProof4FHE.HasteBoots.KeySwitchPaddedComparison
