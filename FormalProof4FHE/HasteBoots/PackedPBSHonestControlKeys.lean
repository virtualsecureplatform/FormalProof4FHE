module
public import FormalProof4FHE.HasteBoots.HonestControlKeySetup
public import FormalProof4FHE.HasteBoots.HonestControlKeyTranscript
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

/-! Honest control-key semantics for the original Hadamard sources in the actual
supported PBS prefix. All predecessor support, selected factory memory and
original owners are recovered from this same retained execution. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSHonestControlKeys
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

/-- Public descriptors of the original Hadamard key slots, fixed by their
actual source geometry rather than supplied as decoded key values. -/
def parameters (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights (hs.tag factor) = height) (slot : Fin (2*d)) :=
  TransportedOriginalHadamardSource.parameters hs first.heights capacity radius geometry (.inl (slot,true))

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Every original Hadamard owner freezes a log containing all incoming setup
queries, including the original callback's actual commitment hash calls. -/
theorem prefix_log : initial.hash.log <+: before.1.1.1.1.1.1.2.hash.log := by
  have present := (PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial
    before.1.1.1.1.1 (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)).2.1
  simp only [MultiCommitmentPrefix.witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at present
  obtain ⟨committed,committedSupported,last,_,same⟩ := present
  have logs := congrArg (fun result => result.1.2.hash.log) same
  rw [logs]
  exact SharedHashLog.run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (PackedPBSHadamardNTT.hadamard family hs).commit initial committed committedSupported

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Actual Hadamard key snapshots have the caller's installed setup roots. -/
theorem key_root (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights (hs.tag factor) = height) (slot : Fin (2*d)) :
    ((PackedPBSOriginalTransformCoverage.hadamardSources hs first second before capacity radius geometry).owners (.inl (slot,true))).root = family.keys slot := by
  change before.1.1.1.1.1.1.1.1 (.inl (slot,true)) = _
  rw [PackedPBSHadamardNTT.hadamard_roots length psi primitive family base hs dummy initial before.1.1.1.1.1 (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)]
  rfl

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Every actual Hadamard key polynomial equals the honestly initialized native
control-row transform, or the same final Bad occurs. Setup query inclusion and
root identity are derived from execution; no transform equality is supplied. -/
theorem keys_or_bad
    (linearEncoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights (hs.tag factor) = height)
    (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := d))
    (receipt : HonestControlKeySetup.Receipt (parameters hs first capacity radius geometry) hs.encoding psi controls family.keys initial.hash.log)
    (dimensions : (rows+1)+cells = n+1)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (sound : RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape first.heights) state)
    (enough : ∀ slot, (parameters hs first capacity radius geometry slot).degree ≤ 2^first.heights (parameters hs first capacity radius geometry slot).tag)
    (margin : ∀ slot, 2*(parameters hs first capacity radius geometry slot).radius <
      Code.minDist (BlockCode.code (parameters hs first capacity radius geometry slot).domain
        (parameters hs first capacity radius geometry slot).degree (2^lanes) :
          Set (Fin (2^first.heights (parameters hs first capacity radius geometry slot).tag) → Fin (2^lanes) → ZMod q)))
    (fits : ∀ slot, (rows+1)+cells ≤ (parameters hs first capacity radius geometry slot).front+(parameters hs first capacity radius geometry slot).suffix) :
    (∀ position half source level, PBSHadamardBlindRotation.project
      (RecordedPaddedSourceFamily.logical (PackedPBSOriginalTransformCoverage.hadamardSources hs first second before capacity radius geometry) hs.encoding dummy (n+1))
      (PackedHadamardRows.address (Nat.pow_add 2 cells lanes).symm dimensions (PackedMonomialRotation.rowIndex position half))
      (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true)) =
      BlindRotationNTT.transform (cells+lanes) psi (controls position source level half)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  obtain ⟨labels,roots,logged⟩ := receipt
  have logPrefix := prefix_log length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported
  have recorded := PackedPBSOriginalTransformCoverage.hadamard_recorded length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported linearEncoding capacity radius geometry state retained
  have honest := HonestControlKeyTranscript.polynomials_or_bad (PackedPBSOriginalTransformCoverage.hadamardSources hs first second before capacity radius geometry) (fun slot => .inl (slot,true))
    hs.encoding dummy psi controls labels (fun slot => (key_root length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry slot).trans (roots slot))
    (fun slot entry member => logPrefix.sublist.subset (logged slot entry member)) state sound recorded enough margin fits
  rcases honest with values | bad
  · left
    intro position half source level
    have regroup : QueryReindex.source dimensions
        (RecordedPaddedSourceFamily.logical (PackedPBSOriginalTransformCoverage.hadamardSources hs first second before capacity radius geometry) hs.encoding dummy (n+1)
          (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true))) =
        RecordedPaddedSourceFamily.logical (PackedPBSOriginalTransformCoverage.hadamardSources hs first second before capacity radius geometry) hs.encoding dummy ((rows+1)+cells)
          (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true)) :=
      PaddedSourceAddress.logical_reindex dimensions _
    rw [PackedHadamardRows.project_eq_row]
    rw [regroup]
    exact values position half source level
  · exact Or.inr bad

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Actual shared hash-only setup returns exactly this caller's control roots
and native initial state. The factual receipt is derived, not assumed. -/
theorem keys_from_setup_or_bad {SetupIndex : Type} {setupBase : OracleSpec SetupIndex}
    (setupImpl : QueryImpl setupBase ProbComp)
    (linearEncoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights (hs.tag factor) = height)
    (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := d))
    (setupSupported : (family.keys,initial) ∈ support ((simulateQ
      (CheckpointExecution.handler setupImpl hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height))
      (HonestControlKeySetup.program (parameters hs first capacity radius geometry) hs.encoding psi controls)).run
        (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height))))
    (dimensions : (rows+1)+cells = n+1)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (sound : RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape first.heights) state)
    (enough : ∀ slot, (parameters hs first capacity radius geometry slot).degree ≤ 2^first.heights (parameters hs first capacity radius geometry slot).tag)
    (margin : ∀ slot, 2*(parameters hs first capacity radius geometry slot).radius <
      Code.minDist (BlockCode.code (parameters hs first capacity radius geometry slot).domain
        (parameters hs first capacity radius geometry slot).degree (2^lanes) :
          Set (Fin (2^first.heights (parameters hs first capacity radius geometry slot).tag) → Fin (2^lanes) → ZMod q)))
    (fits : ∀ slot, (rows+1)+cells ≤ (parameters hs first capacity radius geometry slot).front+(parameters hs first capacity radius geometry slot).suffix) :
    (∀ position half source level, PBSHadamardBlindRotation.project
      (RecordedPaddedSourceFamily.logical (PackedPBSOriginalTransformCoverage.hadamardSources hs first second before capacity radius geometry) hs.encoding dummy (n+1))
      (PackedHadamardRows.address (Nat.pow_add 2 cells lanes).symm dimensions (PackedMonomialRotation.rowIndex position half))
      (.inl (PBSHadamardBlindRotation.digitIndex (source,level),true)) =
      BlindRotationNTT.transform (cells+lanes) psi (controls position source level half)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  have initialized := HonestControlKeySetup.initialized setupImpl (parameters hs first capacity radius geometry)
    hs.encoding dummy psi controls (RecordedSourceCoherence.Shape Cfg height) (family.keys,initial) setupSupported
  exact keys_or_bad length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported linearEncoding capacity radius geometry controls initialized.1 dimensions
    state retained sound enough margin fits

end
end FormalProof4FHE.HasteBoots.PackedPBSHonestControlKeys
