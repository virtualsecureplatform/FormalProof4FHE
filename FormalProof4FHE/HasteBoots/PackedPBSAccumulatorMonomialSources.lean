module
public import FormalProof4FHE.HasteBoots.PackedPBSMonomialNTT
public import FormalProof4FHE.HasteBoots.AcceptedMonomialNTT
public import FormalProof4FHE.HasteBoots.OwnedAmbientAccumulator
public import FormalProof4FHE.HasteBoots.AmbientSourceDescriptor
public import FormalProof4FHE.HasteBoots.DecodedAccumulatorRows
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! Original accumulator sources and monomial coefficients in the actual
supported PBS prefix. All predecessor support, selected factory memory and
original owners are recovered from this same retained execution. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSAccumulatorMonomialSources
open OracleSpec OracleComp
open NativeRootMessage (Digest)
noncomputable section
attribute [local irreducible] MonadAttach.support
variable {q cells lanes rows d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]

variable (length : 2^c*b = 2^(cells+lanes)) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^((cells+lanes)+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

variable {Helper Selection Root Data : Type}

variable {SecondHelper SecondSelection SecondRoot SecondData : Type}

variable {AccResponse : Type} {accFront accSuffix accM accQueries accHeight : ℕ}

  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^accFront) (2^lanes))]
  [SampleableType (Fin accQueries → Fin (2^accHeight))]

variable {MonoResponse MonoCommitMemory : Type} {monoK monoFront monoSuffix monoM monoQueries monoHeight : ℕ}
  [SampleableType (Fin monoK → Fin (rows+1) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^monoFront) (2^lanes))]
  [SampleableType (Fin monoQueries → Fin (2^monoHeight))]

variable [SampleableType (Fin (2^lanes) → ZMod q)]

variable (dummy : Digest)
  (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper
    (Selection × ShortCircuitSequence.Outcome Root Data Memory) d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper
    (SecondSelection × ShortCircuitSequence.Outcome SecondRoot SecondData Memory) d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference)
  (factory : Memory → AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg AccResponse Memory Memory
    (2^lanes) cells rows accFront accSuffix accM accQueries accHeight)
  (evaluations : PackedPBSMonomialReferences.Evaluations)
  (monoBase : Bool → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg MonoResponse Memory MonoCommitMemory
    (2^lanes) cells (rows+1) monoK monoFront monoSuffix monoM monoQueries monoHeight)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (before : PackedPBSMonomialNTT.AfterAccumulator (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
    (front := front) (suffix := suffix) (queries := queries) (height := height) (AccResponse := AccResponse)
    (accB := 2^lanes) (accC := cells) (accR := rows) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
    first second)
  (ntts : PackedPBSMonomialNTT.MonomialOutcome (q := q) (Input := Input) (Cfg := Cfg)
    (Memory := Memory) (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (monoB := 2^lanes)
    (monoC := cells) (monoR := rows+1) (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries)
    (monoHeight := monoHeight) first.heights)
  (supported : (before,some ntts) ∈ support (PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase initial))

/-- Select the accumulator return that this same PBS prefix actually reached. -/
def accumulatorChild := Classical.choose (PackedPBSMonomialNTT.reached_ntt length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase initial before ntts supported)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported in
/-- Recover its actual prefix support, rather than assuming a new child run. -/
theorem accumulatorSupported : (before.1,some (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported)) ∈ support (PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial) := by
  have facts := Classical.choose_spec (PackedPBSMonomialNTT.reached_ntt length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase initial before ntts supported)
  dsimp only [accumulatorChild]
  rw [← facts.1]
  exact facts.2.2.1

/-- The second-comparison predecessor and its actual opening memory. -/
def predecessor := Classical.choose (PackedPBSAccumulator.reached_accumulator length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before.1 (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported) (accumulatorSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported))

/-- Configure the original accumulator at the predecessor's actual memory. -/
def accumulatorScheme := PackedPBSAccumulator.accumulator family inputs hs accumulators factory
  (predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.2.1.2.memory

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported in
/-- This accumulator was executed from the actual predecessor state. -/
theorem accumulatorExecuted : (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported) ∈ support (AmbientAccumulator.witness first.heights
    (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported) dummy (predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.2.2) :=
  (Classical.choose_spec (PackedPBSAccumulator.reached_accumulator length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before.1 (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported) (accumulatorSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported))).2.2.2

/-- Original accumulator owners, taken from its actual retained prefix. -/
def accumulatorOwners :=
  AmbientDependentBatchOpening.snapshots first.heights (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).tag (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).1

/-- The complete original accumulator tables supplied to the arithmetic proof. -/
def accumulatorTables (capacity : 2^accSuffix ≤ accM*(2^lanes)) (radius : ℕ) :=
  OwnedAmbientAccumulator.originalTables first.heights (accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported) dummy capacity radius
    (accumulatorOwners length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported in
/-- The two-call NTT starts at the actual accumulator return and state. -/
theorem nttExecuted : ntts ∈ support (AmbientMonomialNTT.witness hs.encoding (Nat.pow_add 2 cells lanes).symm psi primitive
    (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase first.heights dummy
    (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.1.2.memory (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.2) :=
  (Classical.choose_spec (PackedPBSMonomialNTT.reached_ntt length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase initial before ntts supported)).2.2.2

variable (passed : ntts.1.accepted = true)

/-- A retained native NTT selected from the actual accepted two-call loop. -/
def selectedNTT (side : Bool) := AcceptedMonomialNTT.selected hs.encoding psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase first.heights dummy (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.1.2.memory (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.2 ntts (nttExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported) passed side

/-- Its actual original coefficient/evaluation checkpoint owners. -/
def nttOwners (side : Bool) := AcceptedMonomialNTT.owners hs.encoding psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase first.heights dummy (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.1.2.memory (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.2 ntts (nttExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported) passed side

/-- Its complete original coefficient/evaluation sources. -/
def nttSources (capacity : 2^monoSuffix ≤ monoM*(2^lanes)) (radius : Bool → ℕ) (side source : Bool) :=
  AcceptedMonomialNTT.sources hs.encoding psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase first.heights dummy (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.1.2.memory (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.2 ntts (nttExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported) passed capacity radius side source

/-- Native accumulator slots borrowed by the two monomial coefficient calls. -/
def accumulatorSlot (side : Bool) : Fin 7 := if side then 1 else 0

/-- Complete metadata of the actual selected NTT coefficient decoder. -/
def nttParameters (capacity : 2^monoSuffix ≤ monoM*(2^lanes)) (radius : Bool → ℕ)
    (geometry : ∀ side incoming, first.heights ((monoBase side incoming).tag false) = monoHeight) (side : Bool) :=
  let child := selectedNTT length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported passed side
  AmbientSourceDescriptor.parameters (front := monoFront) first.heights ((monoBase side child.1).tag false)
    (geometry side child.1) (monoBase side child.1).domain capacity (radius side)

/-- Actual accumulator decoder metadata at the reached predecessor memory. -/
def accumulatorParameters (capacity : 2^accSuffix ≤ accM*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).tag factor) = accHeight) (side : Bool) :=
  let scheme := accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported
  AmbientSourceDescriptor.parameters (front := accFront) first.heights (scheme.tag (accumulatorSlot side))
    (geometry (accumulatorSlot side)) scheme.domain capacity radius

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported passed in
/-- The original monomial coefficient sources are the actual accumulator
input/product tables, outside one later shared-history exception. Only public
decoder association is assumed; owners, roots and execution support are derived. -/
theorem sources_eq_or_bad (monoCapacity : 2^monoSuffix ≤ monoM*(2^lanes)) (monoRadius : Bool → ℕ)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (monoGeometry : ∀ side incoming, first.heights ((monoBase side incoming).tag false) = monoHeight)
    (accGeometry : ∀ factor, first.heights ((accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).tag factor) = accHeight)
    (associated : ∀ side, nttParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported passed monoCapacity monoRadius monoGeometry side = accumulatorParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported accCapacity accRadius accGeometry side)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains ntts.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state) :
    (∀ side, nttSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported passed monoCapacity monoRadius side false = DecodedAccumulatorRows.nttView (accumulatorTables length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported accCapacity accRadius (accumulatorSlot side))) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state
  · exact Or.inr bad
  · left
    intro side
    let child := accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported
    let selected := selectedNTT length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported passed side
    let scheme := accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported
    have accSupported := accumulatorExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported
    have recordedAcc := AmbientAccumulator.fresh_recorded first.heights scheme dummy
      (predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.2.2 child accSupported (accumulatorSlot side)
    have accAtLoop := AmbientNTTSequenceSoundness.retains
      (AmbientMonomialNTT.factory hs.encoding (Nat.pow_add 2 cells lanes).symm psi primitive
        (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase)
      first.heights hs.encoding dummy [false,true] child.2.1.2.memory child.2.2 ntts (nttExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported)
      (scheme.tag (accumulatorSlot side)) (accumulatorOwners length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported (accumulatorSlot side)) recordedAcc
    have accAtState := retained _ _ accAtLoop
    have member := AcceptedMonomialNTT.selected_member hs.encoding psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase first.heights dummy (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.1.2.memory (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.2 ntts (nttExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported) passed side
    have nttAtLoop := PackedPBSMonomialNTT.retained_source_recorded length psi primitive family inputs base hs nodesEnough radix linearBase
      dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase initial before ntts supported
      (side,selected) member false
    have nttAtState := retained _ _ nttAtLoop
    have rootNtt := AcceptedMonomialNTT.owners_recorded hs.encoding psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase first.heights dummy (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.1.2.memory (accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).2.2 ntts (nttExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported) passed side false
    have roots := PackedPBSAccumulator.roots length psi primitive family inputs base hs nodesEnough radix linearBase
      dummy first second secondBase accumulators factory initial before.1 child (accumulatorSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported)
    have rootAccumulator : (accumulatorOwners length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported (accumulatorSlot side)).root =
        PackedPBSMonomialReferences.coefficients accumulators side := by
      change child.1.1.1 (accumulatorSlot side) = _
      rw [roots]
      cases side <;> rfl
    have comparison := AmbientSourceDescriptor.associated_logical_eq_or_bad
      (nttParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported passed monoCapacity monoRadius monoGeometry side) (accumulatorParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported accCapacity accRadius accGeometry side) (associated side)
      hs.encoding dummy ((rows+1)+cells) state audited (nttOwners length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported passed side false) (accumulatorOwners length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported (accumulatorSlot side))
      nttAtState accAtState (rootNtt.1.trans rootAccumulator.symm)
    have equal := comparison.resolve_right bad
    have normalizedNtt := AmbientSourceDescriptor.original hs.encoding dummy first.heights ((monoBase side selected.1).tag false)
      (monoGeometry side selected.1) (monoBase side selected.1).domain monoCapacity (monoRadius side)
      (monoBase side selected.1).dimensions (nttOwners length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported passed side false)
    have normalizedAccumulator := AmbientSourceDescriptor.original hs.encoding dummy first.heights (scheme.tag (accumulatorSlot side))
      (accGeometry (accumulatorSlot side)) scheme.domain accCapacity accRadius scheme.layout.symm (accumulatorOwners length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported (accumulatorSlot side))
    change QueryReindex.source (monoBase side selected.1).dimensions
      (AmbientMatrixSource.source (front := monoFront) hs.encoding dummy first.heights (monoBase side selected.1).domain monoCapacity (monoRadius side)
        ((monoBase side selected.1).tag false) (nttOwners length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported passed side false)) =
      DecodedAccumulatorRows.nttView (QueryReindex.source scheme.layout.symm
        (AmbientMatrixSource.source (front := accFront) hs.encoding dummy first.heights scheme.domain accCapacity accRadius
          (scheme.tag (accumulatorSlot side)) (accumulatorOwners length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported (accumulatorSlot side))))
    rw [normalizedNtt,normalizedAccumulator]
    exact equal.trans (DecodedAccumulatorRows.nttView_logical (cells := cells) (rows := rows)
      (accumulatorParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported accCapacity accRadius accGeometry side) hs.encoding dummy (accumulatorOwners length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported (accumulatorSlot side))).symm

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported passed in
/-- Every decoded monomial coefficient row is the same polynomial from the
original accumulator input/product table, including inactive padded rows. -/
theorem coefficient_rows_eq_or_bad (monoCapacity : 2^monoSuffix ≤ monoM*(2^lanes)) (monoRadius : Bool → ℕ)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (monoGeometry : ∀ side incoming, first.heights ((monoBase side incoming).tag false) = monoHeight)
    (accGeometry : ∀ factor, first.heights ((accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported).tag factor) = accHeight)
    (associated : ∀ side, nttParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported passed monoCapacity monoRadius monoGeometry side = accumulatorParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported accCapacity accRadius accGeometry side)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains ntts.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state) :
    (∀ side position half, PackedMonomialRotation.polynomial (nttSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported passed monoCapacity monoRadius side false) position half =
      DecodedAccumulatorRows.decode (accumulatorTables length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported accCapacity accRadius (accumulatorSlot side)) position half) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  rcases sources_eq_or_bad length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported passed monoCapacity monoRadius accCapacity accRadius monoGeometry accGeometry associated
      state retained audited with same | bad
  · left
    intro side position half
    have equal := congrArg (fun source => PackedMonomialRotation.polynomial source position half) (same side)
    exact equal.trans (DecodedAccumulatorRows.polynomial_nttView (accumulatorTables length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts supported accCapacity accRadius (accumulatorSlot side)) position half)
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.PackedPBSAccumulatorMonomialSources
