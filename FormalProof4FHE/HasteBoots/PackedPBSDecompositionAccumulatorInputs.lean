module
public import FormalProof4FHE.HasteBoots.PackedPBSAccumulator
public import FormalProof4FHE.HasteBoots.PackedPBSSecondDigitNTTAssociation
public import FormalProof4FHE.HasteBoots.PackedPBSFirstCanonicalDigits
public import FormalProof4FHE.HasteBoots.ExecutedAccumulatorInputs
public import FormalProof4FHE.HasteBoots.OwnedAmbientAccumulator
public import FormalProof4FHE.HasteBoots.AmbientSourceDescriptor
public import FormalProof4FHE.HasteBoots.DecodedAccumulatorRows
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! Both original decomposition inputs and accumulator differences in the actual
supported PBS prefix. All predecessor support, selected factory memory and
original owners are recovered from this same retained execution. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSDecompositionAccumulatorInputs
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

/-- The actual accepted second comparison that gates this accumulator. -/
def secondComparison := Classical.choose (PackedPBSAccumulator.reached_accumulator length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase accumulators factory initial before outcome supported)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Recover the exact second-comparison prefix, without replay. -/
theorem secondSupported : (before.1,some (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∈ support
    (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase initial) := by
  have facts := Classical.choose_spec (PackedPBSAccumulator.reached_accumulator length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase accumulators factory initial before outcome supported)
  dsimp only [secondComparison]
  rw [← facts.1]
  exact facts.2.2.1

/-- Configure the actual borrowed-root accumulator at that returned memory. -/
def accumulatorScheme := PackedPBSAccumulator.accumulator family inputs hs accumulators factory
  (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.2.1.2.memory

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Its actual inherited execution, with the same shared state. -/
theorem accumulatorExecuted : outcome ∈ support (AmbientAccumulator.witness first.heights
    (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.2.2) :=
  (Classical.choose_spec (PackedPBSAccumulator.reached_accumulator length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase accumulators factory initial before outcome supported)).2.2.2

/-- Original arithmetic sources decoded from the actual accumulator owners. -/
def accumulatorSources (capacity : 2^accSuffix ≤ accM*(2^lanes)) (radius : ℕ) :=
  ExecutedAccumulatorInputs.sources first.heights (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy outcome capacity radius

/-- The first comparison actually reached on that same second prefix. -/
def firstComparison := PackedPBSSecondCanonicalDigits.predecessor (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Its support follows from the same retained execution. -/
theorem firstSupported : (before.1.1.1,some (firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∈ support
    (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first initial) :=
  PackedPBSSecondDigitNTTAssociation.firstPrefixSupported (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)

/-- Original first reconstruction factory, without replacing its encoding. -/
def firstLinearScheme := PackedPBSFirstCanonicalDigits.linearScheme (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)

/-- Executed second reconstruction with its runtime-selected encoding. -/
def secondLinearScheme := PackedPBSSecondCanonicalDigits.linearScheme (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)

/-- Original first reconstruction source family. Only its total width is used. -/
def firstFamily (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height) :=
  PackedPBSFirstCanonicalDigits.sourceFamily (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) capacity radius geometry

/-- Original second reconstruction source family. Only its total width is used. -/
def secondFamily (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height) :=
  PackedPBSSecondCanonicalDigits.sourceFamily (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) capacity radius geometry

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The actual accumulator preserves the full second-comparison history. -/
theorem secondRetained
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state) :
    CheckpointHistoryChain.Retains (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.2.2 state := by
  intro tag saved recorded
  exact retained _ _ (AmbientAccumulator.retains first.heights (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy
    (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.2.2 outcome (accumulatorExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) tag saved recorded)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Carry first-comparison history through the real second linear/comparison
and accumulator stages; all checkpoint owners and logs remain recorded. -/
theorem firstRetained
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state) :
    CheckpointHistoryChain.Retains (firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.2.2 state := by
  intro tag saved recorded
  have afterLinear := AmbientLinear.retains first.heights (PackedPBSSecondCanonicalDigits.linearScheme (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) dummy
    (firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.2.2 (PackedPBSSecondCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported))
    (PackedPBSSecondCanonicalDigits.linearExecuted (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) tag saved recorded
  have afterComparison := PackedPBSComparisonStage.retains hs.encoding dummy (PackedPBSSecondComparisons.sharedScheme first.heights second)
    (PackedPBSSecondCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)).1.1.1
    (PackedPBSSecondCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)).2.1.2.memory
    (PackedPBSSecondCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)).2.2 tag saved afterLinear
    (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSSecondCanonicalDigits.comparisonExecuted (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported))
  exact secondRetained length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported state retained tag saved afterComparison

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The actual first family remains recorded after this accumulator. -/
theorem firstRecorded (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (encoding : (firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state) :
    RecordedPaddedSourceFamily.Recorded (firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) state :=
  PackedPBSFirstCanonicalDigits.source_recorded (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) capacity radius geometry encoding
    state (firstRetained length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported state retained)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Literal borrowed input roots agree with the executed first reconstruction. -/
theorem firstInputRoot (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height) :
    outcome.1.1.1 (PackedPBSAccumulatorReferences.inputSlot false) =
      (firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry).roots DecompositionLinear.input := by
  rw [PackedPBSAccumulator.roots length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase
    dummy first second secondBase accumulators factory initial before outcome supported]
  change inputs.roots false = _
  exact (PackedPBSFirstCanonicalDigits.source_roots (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) capacity radius geometry).1.symm

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The actual first reconstruction input is the corresponding accumulator
difference half at every original NTT row, or the existing risk/final Bad. -/
theorem first_input_rows_or_risks
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (encoding : (firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (accGeometry : ∀ factor, first.heights ((accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = accHeight)
    (associated : ExecutedAccumulatorInputs.parameters first.heights (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) accCapacity accRadius accGeometry
      (PackedPBSAccumulatorReferences.inputSlot false) =
      (firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry).parameters DecompositionLinear.input)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true) :
    (∀ position outputHalf, DecompositionBlindRotation.project
      (RecordedPaddedSourceFamily.logical (firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (accFront+accSuffix))
      (PackedHadamardRows.address (Nat.pow_add 2 cells lanes).symm
        (show (rows+1)+cells = accFront+accSuffix by have := (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).layout; omega)
        (PackedMonomialRotation.rowIndex position outputHalf)) DecompositionLinear.input =
      DecodedAccumulatorRows.decode (accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).difference position false) ∨
      OwnedAmbientAccumulator.OriginalRisk first.heights (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy accCapacity accRadius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state :=
  ExecutedAccumulatorInputs.input_ntt_rows_or_risks first.heights (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy
    (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.2.2 outcome (accumulatorExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) accCapacity accRadius accGeometry
    (firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) false associated
    (firstInputRoot length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) state retained audited
    (firstRecorded length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry encoding state retained) arithmetic opened

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The actual second family remains recorded after this accumulator. -/
theorem secondRecorded (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state) :
    RecordedPaddedSourceFamily.Recorded (secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) state :=
  PackedPBSSecondCanonicalDigits.source_recorded (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) capacity radius geometry
    state (secondRetained length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported state retained)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Literal borrowed input roots agree with the executed second reconstruction. -/
theorem secondInputRoot (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height) :
    outcome.1.1.1 (PackedPBSAccumulatorReferences.inputSlot true) =
      (secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry).roots DecompositionLinear.input := by
  rw [PackedPBSAccumulator.roots length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase
    dummy first second secondBase accumulators factory initial before outcome supported]
  change inputs.roots true = _
  exact (PackedPBSSecondCanonicalDigits.source_roots (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) capacity radius geometry).1.symm

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The actual second reconstruction input is the corresponding accumulator
difference half at every original NTT row, or the existing risk/final Bad. -/
theorem second_input_rows_or_risks
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (accGeometry : ∀ factor, first.heights ((accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = accHeight)
    (associated : ExecutedAccumulatorInputs.parameters first.heights (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) accCapacity accRadius accGeometry
      (PackedPBSAccumulatorReferences.inputSlot true) =
      (secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry).parameters DecompositionLinear.input)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true) :
    (∀ position outputHalf, DecompositionBlindRotation.project
      (RecordedPaddedSourceFamily.logical (secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (accFront+accSuffix))
      (PackedHadamardRows.address (Nat.pow_add 2 cells lanes).symm
        (show (rows+1)+cells = accFront+accSuffix by have := (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).layout; omega)
        (PackedMonomialRotation.rowIndex position outputHalf)) DecompositionLinear.input =
      DecodedAccumulatorRows.decode (accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).difference position true) ∨
      OwnedAmbientAccumulator.OriginalRisk first.heights (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy accCapacity accRadius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state :=
  ExecutedAccumulatorInputs.input_ntt_rows_or_risks first.heights (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy
    (secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.2.2 outcome (accumulatorExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) accCapacity accRadius accGeometry
    (secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) true associated
    (secondInputRoot length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) state retained audited
    (secondRecorded length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry state retained) arithmetic opened

end
end FormalProof4FHE.HasteBoots.PackedPBSDecompositionAccumulatorInputs
