module
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
namespace FormalProof4FHE.HasteBoots.PackedPBSOriginalTransformCoverage
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

/-- Actual copied original Hadamard digit/key/result sources from this PBS run. -/
def hadamardSources (capacity : 2^suffix ≤ m*(2^lanes)) (hadamardRadius : ℕ)
    (hadamardGeometry : ∀ factor, first.heights (hs.tag factor) = height) :=
  TransportedOriginalHadamardSource.sources hs before.1.1.1.1.1 first.heights capacity hadamardRadius hadamardGeometry

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- All Hadamard owners survive the complete actually reached PBS prefix. -/
theorem hadamard_recorded
    (linearEncoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (capacity : 2^suffix ≤ m*(2^lanes)) (hadamardRadius : ℕ)
    (hadamardGeometry : ∀ factor, first.heights (hs.tag factor) = height)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state) :
    RecordedPaddedSourceFamily.Recorded (hadamardSources hs first second before capacity hadamardRadius hadamardGeometry) state :=
  TransportedOriginalHadamardSource.recorded length psi primitive family base hs dummy initial before.1.1.1.1.1 (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) first.heights capacity hadamardRadius hadamardGeometry state
    (PackedPBSResultAccumulatorSource.originalRetained length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported linearEncoding state retained)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The actual original Hadamard identity holds on those recorded factors,
or its existing original-risk event occurs. No relation certificate is supplied. -/
theorem hadamard_relation_or_risk (capacity : 2^suffix ≤ m*(2^lanes)) (hadamardRadius : ℕ)
    (hadamardGeometry : ∀ factor, first.heights (hs.tag factor) = height) :
    PBSHadamard.Relation (RecordedPaddedSourceFamily.logical (hadamardSources hs first second before capacity hadamardRadius hadamardGeometry) hs.encoding dummy (n+1)) ∨ OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs) dummy capacity hadamardRadius before.1.1.1.1.1 :=
  TransportedOriginalHadamardSource.relation_or_risk length psi primitive family base hs dummy initial before.1.1.1.1.1 (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) first.heights capacity hadamardRadius hadamardGeometry

/-- One set of coefficient-to-original-Hadamard bindings for every retained
NTT call and row, without selecting a fresh experiment for any child. -/
def Transforms (capacity : 2^suffix ≤ m*(2^lanes)) (radius : Fin (2*d+1) → ℕ) (hadamardRadius : ℕ)
    (hadamardGeometry : ∀ factor, first.heights (hs.tag factor) = height) : Prop :=
  ∀ entry ∈ (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results, ∀ row, BlindRotationNTT.transform (cells+lanes) psi
    (PackedNTTBinding.row length (AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy capacity (radius entry.1) entry.2.2.1 false) row) =
    PBSHadamardBlindRotation.project
      (RecordedPaddedSourceFamily.logical (hadamardSources hs first second before capacity hadamardRadius hadamardGeometry) hs.encoding dummy (n+1))
      (PackedHadamardRows.address length ((base entry.1 entry.2.1).dimensions.trans hs.dimensions.symm) row)
      (PackedPBSOriginalReferences.evaluationFactor entry.1)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- All original native transforms hold together, or the same loop OriginalRisk
or same later Bad occurs. One risk covers all retained calls and rows. -/
theorem all_transforms_or_risks
    (linearEncoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : Fin (2*d+1) → ℕ) (hadamardRadius : ℕ)
    (hadamardGeometry : ∀ factor, first.heights (hs.tag factor) = height)
    (nttGeometry : ∀ (entry : Fin (2*d+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
    (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
    (b := 2^lanes) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)), entry ∈ (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results →
      ∀ side, first.heights ((base entry.1 entry.2.1).tag side) = height)
    (encoding : ∀ entry, entry ∈ (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results → (base entry.1 entry.2.1).encoding = hs.encoding)
    (associated : ∀ entry member,
      TransportedOriginalNTTSource.parameters base entry first.heights capacity (radius entry.1) (nttGeometry entry member) true =
        TransportedOriginalHadamardSource.parameters hs first.heights capacity hadamardRadius hadamardGeometry
          (PackedPBSOriginalReferences.evaluationFactor entry.1))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state) :
    (Transforms length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius hadamardRadius hadamardGeometry) ∨ NTTLoopProbability.AnyRisk (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1 ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  classical
  by_cases risky : NTTLoopProbability.AnyRisk (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1
  · exact Or.inr (Or.inl risky)
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state
  · exact Or.inr (Or.inr bad)
  left
  intro entry member row
  rcases TransportedOriginalNTTBinding.transforms_or_risks length psi primitive family base hs dummy initial before.1.1.1.1.1 (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) entry member first.heights
      capacity radius hadamardRadius (nttGeometry entry member) hadamardGeometry (encoding entry member) (associated entry member)
      state (PackedPBSResultAccumulatorSource.originalRetained length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported linearEncoding state retained) audited (PackedPBSResultAccumulatorSource.originalAccepted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)
      with rows | failed | failure
  · exact rows row
  · exact False.elim (risky failed)
  · exact False.elim (bad failure)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The actual native Hadamard and every original NTT relation hold in one
source world, or existing Hadamard/NTT risks or the same final Bad occur. -/
theorem native_relations_or_risks
    (linearEncoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : Fin (2*d+1) → ℕ) (hadamardRadius : ℕ)
    (hadamardGeometry : ∀ factor, first.heights (hs.tag factor) = height)
    (nttGeometry : ∀ (entry : Fin (2*d+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
    (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
    (b := 2^lanes) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)), entry ∈ (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results →
      ∀ side, first.heights ((base entry.1 entry.2.1).tag side) = height)
    (encoding : ∀ entry, entry ∈ (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results → (base entry.1 entry.2.1).encoding = hs.encoding)
    (associated : ∀ entry member,
      TransportedOriginalNTTSource.parameters base entry first.heights capacity (radius entry.1) (nttGeometry entry member) true =
        TransportedOriginalHadamardSource.parameters hs first.heights capacity hadamardRadius hadamardGeometry
          (PackedPBSOriginalReferences.evaluationFactor entry.1))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state) :
    (PBSHadamard.Relation (RecordedPaddedSourceFamily.logical (hadamardSources hs first second before capacity hadamardRadius hadamardGeometry) hs.encoding dummy (n+1)) ∧ Transforms length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius hadamardRadius hadamardGeometry) ∨
      OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs) dummy capacity hadamardRadius before.1.1.1.1.1 ∨ NTTLoopProbability.AnyRisk (PackedPBSNTTLoop.factory length psi primitive family base) dummy capacity radius (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1 ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  rcases hadamard_relation_or_risk length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity hadamardRadius hadamardGeometry with hadamard | failedHadamard
  · rcases all_transforms_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported linearEncoding capacity radius hadamardRadius hadamardGeometry nttGeometry encoding associated
      state retained audited with transforms | failedNTT | bad
    · exact Or.inl ⟨hadamard,transforms⟩
    · exact Or.inr (Or.inr (Or.inl failedNTT))
    · exact Or.inr (Or.inr (Or.inr bad))
  · exact Or.inr (Or.inl failedHadamard)

end
end FormalProof4FHE.HasteBoots.PackedPBSOriginalTransformCoverage
