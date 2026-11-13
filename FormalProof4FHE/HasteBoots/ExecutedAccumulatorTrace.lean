module
public import FormalProof4FHE.HasteBoots.DecodedAccumulatorTrace
public import FormalProof4FHE.HasteBoots.ExecutedAccumulatorInputs
public import FormalProof4FHE.HasteBoots.DecodedAccumulatorConstraints
public import FormalProof4FHE.HasteBoots.OwnedAmbientAccumulator
public import FormalProof4FHE.HasteBoots.AmbientSourceDescriptor
public import FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
public import FormalProof4FHE.HasteBoots.PackedPBSAccumulatorReferences
public import FormalProof4FHE.HasteBoots.PackedHadamardRows
public import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! Associate recorded reconstruction inputs with the original duplicated
sources of an actual accumulator run, then enforce difference-row semantics. -/
namespace FormalProof4FHE.HasteBoots.ExecutedAccumulatorTrace
open OracleSpec OracleComp
noncomputable section
attribute [local irreducible] MonadAttach.support
variable {q cells lanes rows front suffix m queries height d : ℕ} [Fact q.Prime]
  {Input Digest Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) (2^lanes))]
  [SampleableType (Fin queries → Fin (2^height))]
  (heights : Cfg → ℕ)
  (s : AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2^lanes) cells rows front suffix m queries height)
  (dummy : Digest)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : AmbientAccumulator.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
    AmbientAccumulator.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response)
      (Memory := Memory) (b := 2^lanes) (c := cells) (r := rows) (front := front) (queries := queries) (height := height))
  (supported : outcome ∈ support (AmbientAccumulator.witness heights s dummy initial))

include supported in
/-- The actual accepted accumulator checks yield arithmetic, initial/final
endpoint identities and cyclic linkage of the constructed original trace, or
the existing accumulator OriginalRisk occurs. No packed-trace witness is supplied. -/
theorem arithmetic_linkage_or_risk
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (rounds : PackedAccumulatorTrace.Rounds rows)
    (start : s.context.start = (FlatMatrixFold.index rows).symm (AccumulatorTrace.wrap rounds.shape))
    (finish : s.context.finish = (FlatMatrixFold.index rows).symm (AccumulatorTrace.last rounds.shape))
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true) :
    (AccumulatorTrace.Arithmetic (DecodedAccumulatorRows.tables (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius)) ∧
      AccumulatorTrace.Linkage rounds.shape (DecodedAccumulatorRows.tables (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius)) (DecodedAccumulatorTrace.endpoint s.context.initial) (DecodedAccumulatorTrace.endpoint s.context.final)) ∨ OwnedAmbientAccumulator.OriginalRisk heights s dummy capacity radius outcome := by
  rcases ExecutedAccumulatorInputs.full_holds_or_risk heights s dummy initial outcome supported capacity radius arithmetic opened with holds | risk
  · exact Or.inl ⟨DecodedAccumulatorConstraints.arithmetic_of_holds (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius) holds.1,
      DecodedAccumulatorTrace.linkage_of_holds (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius) rounds start finish holds⟩
  · exact Or.inr risk

variable {levels : ℕ}
include supported in
/-- Actual original-source arithmetic plus multiplication-stage identities
executes the complete active native blind-rotation trace, or existing risk. -/
theorem valid_trace_or_risk
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (rounds : PackedAccumulatorTrace.Rounds rows)
    (start : s.context.start = (FlatMatrixFold.index rows).symm (AccumulatorTrace.wrap rounds.shape))
    (finish : s.context.finish = (FlatMatrixFold.index rows).symm (AccumulatorTrace.last rounds.shape))
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true)
    (bits : ℕ) (controls : Fin rounds.count → NativeBlindRotation.Control q (2^(cells+lanes)) levels × ℕ)
    (rotation : ∀ round, DecodedAccumulatorRows.decode (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius).product (AccumulatorTrace.active rounds.shape round) =
      fun half => NativeBlindRotation.rotate (controls round).2
        (DecodedAccumulatorRows.decode (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius).input (AccumulatorTrace.active rounds.shape round) half))
    (external : ∀ round, DecodedAccumulatorRows.decode (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius).external (AccumulatorTrace.active rounds.shape round) =
      NativeBlindRotation.externalProduct bits (controls round).1
        (DecodedAccumulatorRows.decode (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius).difference (AccumulatorTrace.active rounds.shape round))) :
    NativeBlindRotation.ValidTrace bits (List.ofFn controls) (DecodedAccumulatorTrace.endpoint s.context.initial)
      (List.ofFn (AccumulatorTrace.traceAt rounds.shape (DecodedAccumulatorRows.tables (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius)))) (DecodedAccumulatorTrace.endpoint s.context.final) ∨ OwnedAmbientAccumulator.OriginalRisk heights s dummy capacity radius outcome := by
  rcases ExecutedAccumulatorInputs.full_holds_or_risk heights s dummy initial outcome supported capacity radius arithmetic opened with holds | risk
  · exact Or.inl (DecodedAccumulatorTrace.valid_trace_of_holds (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius) rounds start finish holds bits controls rotation external)
  · exact Or.inr risk

include supported in
/-- The actual context's decoded final endpoint equals the complete native run
from its decoded initial endpoint, or the existing accumulator risk occurs.
Matching these context endpoints to the public PBS statement remains separate. -/
theorem output_eq_run_or_risk
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (rounds : PackedAccumulatorTrace.Rounds rows)
    (start : s.context.start = (FlatMatrixFold.index rows).symm (AccumulatorTrace.wrap rounds.shape))
    (finish : s.context.finish = (FlatMatrixFold.index rows).symm (AccumulatorTrace.last rounds.shape))
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true)
    (bits : ℕ) (controls : Fin rounds.count → NativeBlindRotation.Control q (2^(cells+lanes)) levels × ℕ)
    (rotation : ∀ round, DecodedAccumulatorRows.decode (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius).product (AccumulatorTrace.active rounds.shape round) =
      fun half => NativeBlindRotation.rotate (controls round).2
        (DecodedAccumulatorRows.decode (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius).input (AccumulatorTrace.active rounds.shape round) half))
    (external : ∀ round, DecodedAccumulatorRows.decode (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius).external (AccumulatorTrace.active rounds.shape round) =
      NativeBlindRotation.externalProduct bits (controls round).1
        (DecodedAccumulatorRows.decode (ExecutedAccumulatorInputs.sources heights s dummy outcome capacity radius).difference (AccumulatorTrace.active rounds.shape round))) :
    (DecodedAccumulatorTrace.endpoint s.context.final) = NativeBlindRotation.run bits (List.ofFn controls) (DecodedAccumulatorTrace.endpoint s.context.initial) ∨ OwnedAmbientAccumulator.OriginalRisk heights s dummy capacity radius outcome := by
  rcases valid_trace_or_risk heights s dummy initial outcome supported capacity radius rounds start finish arithmetic opened bits controls rotation external
    with trace | risk
  · exact Or.inl (NativeBlindRotation.validTrace_output bits _ _ _ _ trace)
  · exact Or.inr risk

end
end FormalProof4FHE.HasteBoots.ExecutedAccumulatorTrace
