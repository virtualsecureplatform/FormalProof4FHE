module
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction
public import FormalProof4FHE.HasteBoots.PublicAccumulatorEndpoint
@[expose] public section

/-! The actual final extraction reads the caller's bound accumulator endpoint
whenever its actual comparison return selects the extraction continuation. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSPublicExtractionEndpoint
open OracleSpec OracleComp
open NativeRootMessage (Digest)
noncomputable section
variable {q log d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData : Type}
  {AccResponse MonoResponse MonoCommitMemory ZeroResponse ZeroCommitMemory InputResponse InputCommitMemory : Type}
  {FinalResponse FinalCommitMemory ProductResponse ProductCommitMemory ReconstructionResponse ReconstructionCommitMemory : Type}
  {accFront accQueries accHeight lanes cells rows monoK monoFront monoQueries monoHeight zeroFront zeroQueries zeroHeight : ℕ}
  {inputB inputC inputFront inputQueries inputHeight finalD finalB finalC : ℕ}
  {FinalHelper FinalSelection FinalRoot FinalData : Memory → Type}
local notation "Complete" => PackedPBSKeySwitchExtraction.BeforeExtraction (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := 2^lanes) (accC := cells) (accR := rows) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)
  (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := inputB) (inputC := inputC)
  (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight)

  (FinalResponse := FinalResponse) (FinalCommitMemory := FinalCommitMemory) (finalD := finalD) (finalB := finalB) (finalC := finalC)

  (ProductResponse := ProductResponse) (ProductCommitMemory := ProductCommitMemory)

  (ReconstructionResponse := ReconstructionResponse) (ReconstructionCommitMemory := ReconstructionCommitMemory)


/-- The actual selected endpoint is the public claim, with no fallback or supplied
endpoint-value equality. Selection comes from the retained comparison return. -/
theorem endpoint_eq_claim (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper (Selection × ShortCircuitSequence.Outcome Root Data Memory) d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper (SecondSelection × ShortCircuitSequence.Outcome SecondRoot SecondData Memory) d)
    (finalBase : Fin (finalD+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg FinalResponse Memory FinalCommitMemory first.heights finalB finalC 1 finalB)
    (productBase : Memory → KeySwitchPaddedProduct.Scheme (q := q) (d := finalD) (b := finalB) (n := finalC)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := first.heights))
    (reconstructionBase : Memory → PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory first.heights (2*finalD+2) finalB (1+finalC))
    (comparisonBase : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory (FinalHelper memory) (FinalSelection memory × ShortCircuitSequence.Outcome (FinalRoot memory) (FinalData memory) Memory) finalD)
    (traceRounds : PackedAccumulatorTrace.Rounds rows)
    (publicInitial claimed : NativeBlindRotation.Cipher q (2^(cells+lanes)))
    {accSuffix accM : ℕ}
    (behavior : Memory → AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg AccResponse Memory Memory
      (2^lanes) cells rows accFront accSuffix accM accQueries accHeight)
    (before : Complete first second finalBase productBase reconstructionBase comparisonBase)
    (memory : Memory)
    (selected : PackedPBSKeySwitchExtraction.get first second finalBase productBase reconstructionBase comparisonBase before = some (true,memory)) :
    PackedPBSKeySwitchExtraction.endpoint first second finalBase productBase reconstructionBase comparisonBase
      (PublicAccumulatorContext.factory traceRounds publicInitial claimed behavior)
      (Nat.pow_add 2 cells lanes).symm rfl before = claimed := by
  have present := (PackedPBSKeySwitchExtraction.get_spec first second finalBase productBase reconstructionBase comparisonBase before memory selected).1
  cases saved : before.1.1.1.1.1.1.1.2 with
  | none => rw [saved] at present; cases present
  | some accumulator =>
    simpa only [PackedPBSKeySwitchExtraction.endpoint,saved,Fin.cast_refl,id_eq] using
      PublicAccumulatorEndpoint.factory_value (Nat.pow_add 2 cells lanes).symm
        traceRounds publicInitial claimed behavior accumulator.1.1.2

end
end FormalProof4FHE.HasteBoots.PackedPBSPublicExtractionEndpoint
