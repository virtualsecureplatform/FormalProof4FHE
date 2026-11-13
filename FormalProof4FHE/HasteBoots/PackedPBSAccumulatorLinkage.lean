module
public import FormalProof4FHE.HasteBoots.ExecutedAccumulatorTrace
public import FormalProof4FHE.HasteBoots.PackedPBSDifferenceDigitNTT
public import FormalProof4FHE.HasteBoots.PackedPBSHonestControlKeys
public import FormalProof4FHE.HasteBoots.PackedPBSOriginalTransformCoverage
public import FormalProof4FHE.HasteBoots.TransportedOriginalNTTBinding
public import FormalProof4FHE.HasteBoots.PackedPBSResultAccumulatorSource
public import FormalProof4FHE.HasteBoots.PackedPBSDecompositionAccumulatorInputs
public import FormalProof4FHE.HasteBoots.PackedPBSFirstDigitNTTAssociation
public import FormalProof4FHE.HasteBoots.PackedPBSSecondDigitNTTAssociation
public import FormalProof4FHE.HasteBoots.PackedPBSFirstCanonicalDigits
public import FormalProof4FHE.HasteBoots.ExecutedAccumulatorInputs
public import FormalProof4FHE.HasteBoots.OwnedAmbientAccumulator
public import FormalProof4FHE.HasteBoots.AmbientSourceDescriptor
public import FormalProof4FHE.HasteBoots.DecodedAccumulatorRows
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! Original Hadamard and NTT arithmetic relations in the actual
supported PBS prefix. All predecessor support, selected factory memory and
original owners are recovered from this same retained execution. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSAccumulatorLinkage
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open scoped BigOperators
noncomputable section
attribute [local irreducible] MonadAttach.support
variable {q cells lanes rows d c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) (2^lanes))]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n (2^lanes))] [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]

variable (length : 2^c*(2^lanes) = 2^(cells+lanes)) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^((cells+lanes)+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2^lanes) c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory (2^lanes) n front suffix m queries height)
  (nodesEnough : 2*(2^lanes) ≤ q) (radix : ℕ)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) (2^lanes) front suffix m queries height)

variable {FirstRetained Selection FirstRoot Data : Type} {firstRepetitions : Fin d → ℕ}

variable {SecondRetained SecondSelection SecondRoot SecondData : Type} {secondRepetitions : Fin d → ℕ}

variable {AccResponse : Type} {accFront accSuffix accM accQueries accHeight : ℕ}

  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^accFront) (2^lanes))]
  [SampleableType (Fin accQueries → Fin (2^accHeight))]

variable (dummy : Digest)
  (first : PackedPBSComparisonStage.Scheme Cfg Input Memory ((Fin (∑ i, firstRepetitions i) → Digest) × FirstRetained)
    (Selection × ShortCircuitSequence.Outcome FirstRoot Data Memory) d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory ((Fin (∑ i, secondRepetitions i) → Digest) × SecondRetained)
    (SecondSelection × ShortCircuitSequence.Outcome SecondRoot SecondData Memory) d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) (2^lanes) front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference)
  (factory : Memory → AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg AccResponse Memory Memory
    (2^lanes) cells rows accFront accSuffix accM accQueries accHeight)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (before : PackedPBSAccumulator.BeforeAccumulator (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := 2^lanes) (c := c) (r := r) (k := k) (n := n)
    (front := front) (suffix := suffix) (queries := queries) (height := height) first second)
  (outcome : PackedPBSAccumulator.AccumulatorOutcome (q := q) (Input := Input) (Cfg := Cfg)
    (Memory := Memory) (AccResponse := AccResponse) (accB := 2^lanes) (accC := cells) (accR := rows)
    (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight) first.heights)
  (supported : (before,some outcome) ∈ support (PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase
    dummy first second secondBase accumulators factory initial))

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The accumulator actually reached by PBS enforces arithmetic, both decoded
context endpoints and complete cyclic continuity on its original sources, or
its existing OriginalRisk occurs. The trace is constructed, not supplied. -/
theorem arithmetic_linkage_or_risk
    (capacity : 2^accSuffix ≤ accM*(2^lanes)) (radius : ℕ)
    (rounds : PackedAccumulatorTrace.Rounds rows)
    (start : (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).context.start = (FlatMatrixFold.index rows).symm (AccumulatorTrace.wrap rounds.shape))
    (finish : (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).context.finish = (FlatMatrixFold.index rows).symm (AccumulatorTrace.last rounds.shape))
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true) :
    (AccumulatorTrace.Arithmetic (DecodedAccumulatorRows.tables (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius)) ∧
      AccumulatorTrace.Linkage rounds.shape (DecodedAccumulatorRows.tables (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius)) (DecodedAccumulatorTrace.endpoint (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).context.initial) (DecodedAccumulatorTrace.endpoint (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).context.final)) ∨ OwnedAmbientAccumulator.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy capacity radius outcome :=
  ExecutedAccumulatorTrace.arithmetic_linkage_or_risk first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy
    (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.2.2 outcome (PackedPBSDecompositionAccumulatorInputs.accumulatorExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) capacity radius rounds start finish arithmetic opened

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Combining original endpoint/linkage checks with multiplication-stage
identities gives the full native run between the actual context endpoints.
The remaining public-context association and stage-risk composition are explicit. -/
theorem output_eq_run_or_risk
    (capacity : 2^accSuffix ≤ accM*(2^lanes)) (radius : ℕ)
    (rounds : PackedAccumulatorTrace.Rounds rows)
    (start : (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).context.start = (FlatMatrixFold.index rows).symm (AccumulatorTrace.wrap rounds.shape))
    (finish : (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).context.finish = (FlatMatrixFold.index rows).symm (AccumulatorTrace.last rounds.shape))
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true)
    (bits : ℕ) (controls : Fin rounds.count → NativeBlindRotation.Control q (2^(cells+lanes)) d × ℕ)
    (rotation : ∀ round, DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius).product (AccumulatorTrace.active rounds.shape round) =
      fun half => NativeBlindRotation.rotate (controls round).2
        (DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius).input (AccumulatorTrace.active rounds.shape round) half))
    (external : ∀ round, DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius).external (AccumulatorTrace.active rounds.shape round) =
      NativeBlindRotation.externalProduct bits (controls round).1
        (DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius).difference (AccumulatorTrace.active rounds.shape round))) :
    (DecodedAccumulatorTrace.endpoint (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).context.final) = NativeBlindRotation.run bits (List.ofFn controls) (DecodedAccumulatorTrace.endpoint (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).context.initial) ∨ OwnedAmbientAccumulator.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy capacity radius outcome :=
  ExecutedAccumulatorTrace.output_eq_run_or_risk first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy
    (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.2.2 outcome (PackedPBSDecompositionAccumulatorInputs.accumulatorExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) capacity radius rounds start finish arithmetic opened bits controls rotation external

end
end FormalProof4FHE.HasteBoots.PackedPBSAccumulatorLinkage
