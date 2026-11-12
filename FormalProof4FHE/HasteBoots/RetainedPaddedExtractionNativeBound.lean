module
public import FormalProof4FHE.HasteBoots.RetainedPaddedExtractionProbability
public import FormalProof4FHE.HasteBoots.KeySwitchPaddedExtraction
@[expose] public section

/-! Average the executed native extraction bound over its actual supported
predecessors. Typed messages supply the degree laws; only public code facts,
source-dependent rates and the inherited audit remain explicit. -/
namespace FormalProof4FHE.HasteBoots.RetainedPaddedExtractionNativeBound
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
open RetainedPaddedExtraction
noncomputable section
variable {q d c lanes dimension : ℕ} [Fact q.Prime]
  {K Before Cfg Input Response Memory CommitMemory : Type}
  [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K]
  [DecidableEq Input] [DecidableEq Digest] {H : Cfg → ℕ}
  [SampleableType Digest] [SampleableType (ZMod q)]
  [SampleableType (Fin (2^lanes) → ZMod q)] [SampleableType (Fin c → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) c (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]

/-- Only reached extraction children contribute risk. The component rate is
derived from the actual native stage, not supplied as a child-security law. -/
theorem safe_bound
    (base : Before → Memory → KeySwitchPaddedExtraction.Scheme (q := q) (c := c) (lanes := lanes)
      (Input := Input) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (heights := H))
    [∀ before memory factor, NeZero ((base before memory).code factor).m]
    [∀ before memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((base before memory).code factor).front) (2^lanes))]
    [∀ before memory factor, SampleableType (Fin ((base before memory).code factor).queries → Fin (2^H ((base before memory).tag factor)))]
    [∀ before memory factor, SampleableType ((Fin (2^((base before memory).code factor).front) × Fin (2^lanes)) → K)]
    (get : Before → Option (Bool × Memory))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
    (positive : 0 < dimension)
    (acc : Before → Memory → ((Unit → Digest) × CommitMemory) → NativeBlindRotation.Cipher q (2^(c+lanes)))
    (output : Before → Memory → ((Unit → Digest) × CommitMemory) → NativePublic.Ciphertext q dimension)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (nodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (basis : Module.Basis (Fin (2^lanes)) (ZMod q) K) (dummy : Digest)
    (enough : ∀ before memory factor, ((base before memory).code factor).m ≤ Fintype.card (Fin (2^H ((base before memory).tag factor))))
    (capacity : ∀ before memory factor, 2^((base before memory).code factor).suffix ≤ ((base before memory).code factor).m*(2^lanes))
    (radius : Before → Memory → Unit → ℕ)
    (small : ∀ before memory factor, (radius before memory factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := K) ((base before memory).domain factor)) ((base before memory).code factor).m :
        Set (Fin (2^H ((base before memory).tag factor)) → K)) : ℚ≥0)/3)
    (epsilon : ENNReal)
    (calibrated : ∀ before memory,
      (((c : ENNReal)/Fintype.card (ZMod q))^(2^lanes) +
        ((((((2*(2^lanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes))) +
        (c : ENNReal)*((((((2*(2^lanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (([()]).map (fun factor => JointMatrixOpening.error (K := K) (m := ((base before memory).code factor).m) (b := 2^lanes)
        (queries := ((base before memory).code factor).queries) ((base before memory).domain factor) (radius before memory factor))).sum ≤ epsilon)
    (prior : ProbComp Before)
    (audited : ∀ before ∈ support prior, CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) (state before)) :
    let native := fun before memory => KeySwitchPaddedExtraction.stage (base before memory) enc family positive
      (acc before memory) (output before memory) firstSmall roundSmall nodesEnough
    Pr{let outcome ← (prior >>= finish native get state dummy)}[
      ∃ result, outcome.2 = some result ∧
        PaddedPublicZeroCheck.OriginalRisk (native result.1.1 result.1.2) dummy (capacity result.1.1 result.1.2)
          (radius result.1.1 result.1.2) result.2 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (finalState native state outcome)] ≤ epsilon := by
  dsimp only
  apply RetainedPaddedExtractionProbability.selected_safe_bound
    (fun before memory => KeySwitchPaddedExtraction.stage (base before memory) enc family positive
      (acc before memory) (output before memory) firstSmall roundSmall nodesEnough)
    get state dummy prior
    (fun result => PaddedPublicZeroCheck.OriginalRisk
      (KeySwitchPaddedExtraction.stage (base result.1.1 result.1.2) enc family positive
        (acc result.1.1 result.1.2) (output result.1.1 result.1.2) firstSmall roundSmall nodesEnough)
      dummy (capacity result.1.1 result.1.2) (radius result.1.1 result.1.2) result.2) epsilon
  intro before supported selected selectedByVerifier
  exact (KeySwitchPaddedExtraction.original_safe_bound (base selected.1 selected.2) enc family positive
    (acc selected.1 selected.2) (output selected.1 selected.2) firstSmall roundSmall nodesEnough basis dummy
    (enough selected.1 selected.2) (capacity selected.1 selected.2) (radius selected.1 selected.2)
    (small selected.1 selected.2) (state before) (audited before supported)).trans (calibrated selected.1 selected.2)

end
end FormalProof4FHE.HasteBoots.RetainedPaddedExtractionNativeBound
