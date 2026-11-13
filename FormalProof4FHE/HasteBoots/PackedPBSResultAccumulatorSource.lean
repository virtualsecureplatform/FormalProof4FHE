module
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

/-! Original external-product result coefficients and accumulator external sources in the actual
supported PBS prefix. All predecessor support, selected factory memory and
original owners are recovered from this same retained execution. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSResultAccumulatorSource
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

/-- The original NTT loop that enabled the actual first reconstruction. -/
def originalLoop := PackedPBSFirstCanonicalDigits.predecessor (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Recover its support in the same actual Hadamard-plus-NTT prefix. -/
theorem originalSupported : (before.1.1.1.1.1,some (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∈ support
    (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial) :=
  PackedPBSFirstDigitNTTAssociation.originalSupported (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Carry all copied original NTT checkpoints through both reconstructions,
comparisons and the actual accumulator; no per-source recording is assumed. -/
theorem originalRetained
    (encoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state) :
    CheckpointHistoryChain.Retains (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2) state :=
  PackedPBSFirstDigitNTTAssociation.originalRetained (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) encoding state
    (PackedPBSDecompositionAccumulatorInputs.firstRetained length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported state retained)

/-- The actual accumulator external-product source owner, at native slot four. -/
def externalOwner := ExecutedAccumulatorInputs.owners first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) outcome 4

/-- Complete public decoder metadata of that same external-product source. -/
def externalParameters (capacity : 2^accSuffix ≤ accM*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = accHeight) :=
  ExecutedAccumulatorInputs.parameters first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) capacity radius geometry 4

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The external slot borrows the actual final original NTT coefficient root. -/
theorem external_root : (externalOwner length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).root = family.coefficients (Fin.last (2*d)) := by
  change outcome.1.1.1 4 = _
  rw [PackedPBSAccumulator.roots length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase
    dummy first second secondBase accumulators factory initial before outcome supported]
  rfl

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Reaching the first reconstruction already derives original-loop acceptance. -/
theorem originalAccepted : (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.accepted = true :=
  (Classical.choose_spec (PackedPBSFirstReconstruction.reached_reconstruction length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy initial before.1.1.1.1
    (PackedPBSFirstCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) (PackedPBSFirstCanonicalDigits.reconstructionSupported (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)))).2.1

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The result slot was actually executed in the accepted original loop. -/
theorem resultEntry_exists : ∃ entry ∈ (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results,
    entry.1 = Fin.last (2*d) := by
  have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial
    before.1.1.1.1.1 (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)
  obtain ⟨incoming,child,member,_,_⟩ := PackedPBSNTTLoop.all_slots_bound length psi primitive family base hs.encoding dummy
    before.1.1.1.1.1.2.1.2.memory before.1.1.1.1.1.2.2 (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) reached.2.2
    (originalAccepted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (Fin.last (2*d))
  exact ⟨(Fin.last (2*d),(incoming,child)),member,rfl⟩

/-- Select the retained result entry; this never launches a new NTT call. -/
def resultEntry := Classical.choose (resultEntry_exists length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The selected result belongs to the original execution's retained list. -/
theorem resultEntry_member : (resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∈ (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results :=
  (Classical.choose_spec (resultEntry_exists length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)).1

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Its slot is the literal final result slot of the trusted caller. -/
theorem resultEntry_slot : (resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1 = Fin.last (2*d) :=
  (Classical.choose_spec (resultEntry_exists length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)).2

variable
  (entry : Fin (2*d+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
    (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
    (b := 2^lanes) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
  (member : entry ∈ (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results)
  (slot : entry.1 = Fin.last (2*d))

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported member slot in
/-- The original result coefficient source and the actual accumulator external
source have one decoded interpretation, outside the same later Bad event.
Source equality is derived from recorded roots and complete public metadata. -/
theorem result_source_eq_or_bad
    (linearEncoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ side, first.heights ((base entry.1 entry.2.1).tag side) = height)
    (encoding : (base entry.1 entry.2.1).encoding = hs.encoding)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (accGeometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = accHeight)
    (associated : TransportedOriginalNTTSource.parameters base entry first.heights capacity radius geometry false =
      externalParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius accGeometry)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state) :
    AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy capacity radius entry.2.2.1 false =
      RecordedPaddedSource.logical (externalParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius accGeometry)
        hs.encoding dummy (r+c) (externalOwner length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  rw [TransportedOriginalNTTSource.original_logical base hs dummy entry first.heights capacity radius geometry encoding false]
  have recordedOriginal := TransportedOriginalNTTSource.owner_recorded length psi primitive family base hs dummy initial
    before.1.1.1.1.1 (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) entry member first.heights state
    (originalRetained length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported linearEncoding state retained) false
  have recordedAccumulator := AmbientAccumulator.fresh_recorded first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy
    (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.2.2 outcome (PackedPBSDecompositionAccumulatorInputs.accumulatorExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) 4
  have rootOriginal := TransportedOriginalNTTSource.owner_root length psi primitive family base hs dummy initial
    before.1.1.1.1.1 (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) entry member first.heights false
  have roots : (TransportedOriginalNTTSource.owner base entry first.heights false).root = (externalOwner length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).root := by
    rw [rootOriginal,slot,external_root length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported]
    rfl
  exact AmbientSourceDescriptor.associated_logical_eq_or_bad
    (TransportedOriginalNTTSource.parameters base entry first.heights capacity radius geometry false)
    (externalParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius accGeometry) associated hs.encoding dummy (r+c)
    state audited (TransportedOriginalNTTSource.owner base entry first.heights false) (externalOwner length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)
    recordedOriginal (retained _ _ recordedAccumulator) roots

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported member slot in
/-- With the public coefficient/round layout identified, every original result
row is the actual decoded accumulator external-product row. No result polynomial
value or transform-truth certificate is supplied. -/
theorem result_rows_eq_or_bad
    (coefficients : c = cells) (rounds : r = rows+1)
    (linearEncoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ side, first.heights ((base entry.1 entry.2.1).tag side) = height)
    (encoding : (base entry.1 entry.2.1).encoding = hs.encoding)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (accGeometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = accHeight)
    (associated : TransportedOriginalNTTSource.parameters base entry first.heights capacity radius geometry false =
      externalParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius accGeometry)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state) :
    (∀ position half, PackedNTTBinding.row length
      (AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy capacity radius entry.2.2.1 false)
      (rounds.symm ▸ PackedMonomialRotation.rowIndex position half) =
      DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).external position half) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  subst c
  subst r
  rcases result_source_eq_or_bad length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported entry member slot linearEncoding capacity radius geometry encoding
    accCapacity accRadius accGeometry associated state retained audited with equal | bad
  · left
    have normalized := AmbientSourceDescriptor.original hs.encoding dummy first.heights
      ((PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag 4) (accGeometry 4) (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).domain accCapacity accRadius (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).layout.symm (externalOwner length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)
    have same : AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy capacity radius entry.2.2.1 false =
        DecodedAccumulatorRows.nttView (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).external := by
      have nativeView := DecodedAccumulatorRows.nttView_logical (cells := cells) (rows := rows)
        (externalParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius accGeometry) hs.encoding dummy (externalOwner length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)
      have original : (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).external =
          RecordedPaddedSource.logical (externalParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius accGeometry)
            hs.encoding dummy ((1+rows)+cells) (externalOwner length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) := normalized
      rw [original,nativeView]
      exact equal
    intro position half
    change PackedMonomialRotation.polynomial
      (AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy capacity radius entry.2.2.1 false) position half = _
    rw [same]
    exact DecodedAccumulatorRows.polynomial_nttView _ position half
  · exact Or.inr bad

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The actually selected original result row equals the accumulator external
row outside final Bad, with no caller-supplied retained-child witness. -/
theorem retained_result_rows_eq_or_bad
    (coefficients : c = cells) (rounds : r = rows+1)
    (linearEncoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ side, first.heights ((base (resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1 (resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.1).tag side) = height)
    (encoding : (base (resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1 (resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.1).encoding = hs.encoding)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (accGeometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = accHeight)
    (associated : TransportedOriginalNTTSource.parameters base (resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) first.heights capacity radius geometry false =
      externalParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius accGeometry)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state) :
    (∀ position half, PackedNTTBinding.row length
      (AuthenticatedNTT.sources (base (resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1 (resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.1) dummy capacity radius (resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).2.2.1 false)
      (rounds.symm ▸ PackedMonomialRotation.rowIndex position half) =
      DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).external position half) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  exact result_rows_eq_or_bad length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported (resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)
    (resultEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (resultEntry_slot length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) coefficients rounds linearEncoding capacity radius geometry encoding
    accCapacity accRadius accGeometry associated state retained audited

end
end FormalProof4FHE.HasteBoots.PackedPBSResultAccumulatorSource
