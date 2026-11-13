module
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
namespace FormalProof4FHE.HasteBoots.PackedPBSNativeExternalProduct
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

/-- Actual retained coefficient rows for every digit source/limb and native
round/half. This predicate is established by original-source coverage. -/
def DigitRows (rounds : r = rows+1) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : Fin (2*d+1) → ℕ)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius bits : ℕ) : Prop :=
  ∀ source level position half, PackedNTTBinding.row length
    (AuthenticatedNTT.sources (base (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level).1 (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level).2.1) dummy capacity (radius (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level).1) (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level).2.2.1 false)
    (rounds.symm ▸ PackedMonomialRotation.rowIndex position half) =
    NativeBlindRotation.digit bits level (DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).difference position source)

/-- The actual retained final NTT coefficient is the decoded external row. -/
def ResultRows (rounds : r = rows+1) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : Fin (2*d+1) → ℕ)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ) : Prop :=
  ∀ position half, PackedNTTBinding.row length
    (AuthenticatedNTT.sources (base (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1 (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.1) dummy capacity (radius (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1) (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.2.1 false)
    (rounds.symm ▸ PackedMonomialRotation.rowIndex position half) =
    DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).external position half

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Deterministic composition of actual retained source rows, original native
relations and control-key evaluations. Subsequent coverage derives every
semantic premise from native risks and honest setup. -/
theorem external_product_of_relations
    (coefficients : c = cells) (rounds : r = rows+1) (dimensions : (rows+1)+cells = n+1)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : Fin (2*d+1) → ℕ) (hadamardRadius : ℕ)
    (hadamardGeometry : ∀ factor, first.heights (hs.tag factor) = height)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius bits : ℕ)
    (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := d))
    (native : PBSHadamard.Relation (RecordedPaddedSourceFamily.logical (PackedPBSOriginalTransformCoverage.hadamardSources hs first second before capacity hadamardRadius hadamardGeometry) hs.encoding dummy (n+1)) ∧ PackedPBSOriginalTransformCoverage.Transforms length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius hadamardRadius hadamardGeometry)
    (digits : DigitRows length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported rounds capacity radius accCapacity accRadius bits)
    (result : ResultRows length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported rounds capacity radius accCapacity accRadius)
    (keys : ∀ position half source level, PBSHadamardBlindRotation.project
      (RecordedPaddedSourceFamily.logical (PackedPBSOriginalTransformCoverage.hadamardSources hs first second before capacity hadamardRadius hadamardGeometry) hs.encoding dummy (n+1))
      (PackedHadamardRows.address (Nat.pow_add 2 cells lanes).symm dimensions (PackedMonomialRotation.rowIndex position half))
      (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true)) =
      BlindRotationNTT.transform (cells+lanes) psi (controls position source level half)) :
    ∀ position, DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).external position =
      NativeBlindRotation.externalProduct bits (controls position) (DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).difference position) := by
  subst c
  subst r
  intro position
  apply PBSHadamardBlindRotation.externalProduct_of_relations psi primitive bits (controls position)
    (DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).difference position) (DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).external position)
    (RecordedPaddedSourceFamily.logical (PackedPBSOriginalTransformCoverage.hadamardSources hs first second before capacity hadamardRadius hadamardGeometry) hs.encoding dummy (n+1))
    (fun half => PackedHadamardRows.address (Nat.pow_add 2 cells lanes).symm dimensions (PackedMonomialRotation.rowIndex position half)) native.1
  · intro half source level
    have same := native.2 (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level) (PackedPBSDifferenceDigitNTT.digitEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level)
      (PackedMonomialRotation.rowIndex position half)
    rw [digits source level position half] at same
    simpa only [PackedPBSDifferenceDigitNTT.digitEntry_slot,PackedPBSDecompositionReferences.digitSlot,
      PackedHadamardRows.evaluation_digit] using same
  · intro half source level
    exact (keys position half source level).symm
  · intro half
    have same := native.2 (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.resultEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)
      (PackedMonomialRotation.rowIndex position half)
    rw [result position half] at same
    simpa only [PackedPBSResultAccumulatorSource.resultEntry_slot,PackedHadamardRows.evaluation_result] using same

end
end FormalProof4FHE.HasteBoots.PackedPBSNativeExternalProduct
