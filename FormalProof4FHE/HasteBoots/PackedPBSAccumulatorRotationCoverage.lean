module
public import FormalProof4FHE.HasteBoots.PackedPBSAccumulatorMonomialSources
public import FormalProof4FHE.HasteBoots.PackedPBSMonomialProduct
public import FormalProof4FHE.HasteBoots.MonomialSourceAssociation
@[expose] public section

/-! Actual accumulator rotations follow from the native monomial continuation
in the same full PBS prefix, retaining its original source owners and history. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSAccumulatorRotationCoverage
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
variable {rounds : ℕ} {ZeroResponse ZeroCommitMemory : Type} {zeroFront zeroSuffix zeroM zeroQueries zeroHeight : ℕ}
  [SampleableType (PackedZeroReduction.Points (ZMod q) (cells+rows) (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^zeroFront) (2^lanes))]
  [SampleableType (Fin zeroQueries → Fin (2^zeroHeight))]
variable (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
  (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
  (rotations : Fin rounds → Fin (2*(2^(cells+lanes))))
  (zeroBase : Memory → AuthenticatedPublicZeroCheck.Scheme (ZMod q) Bool Unit Bool
    (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q) (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
    Input Digest Cfg ZeroResponse Memory ZeroCommitMemory (2^lanes) (cells+rows) zeroFront zeroSuffix zeroM zeroQueries zeroHeight)
  (product : PackedPBSMonomialProduct.ProductOutcome (q := q) (Input := Input) (Cfg := Cfg) (Memory := Memory)
    (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
    (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight) first.heights)
  (supported : ((before,some ntts),some product) ∈ support (PackedPBSMonomialProduct.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial))

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported in
/-- Reaching the product recovers this exact supported monomial NTT prefix. -/
theorem prefixSupported : (before,some ntts) ∈ support (PackedPBSMonomialNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase initial) :=
  (Classical.choose_spec (PackedPBSMonomialProduct.reached_product length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial (before,some ntts) product supported)).2.2.1

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported in
/-- The actual NTT acceptance gate enabled this continuation. -/
theorem nttAccepted : ntts.1.accepted = true := by
  have reached := Classical.choose_spec (PackedPBSMonomialProduct.reached_product length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial (before,some ntts) product supported)
  have same : ntts = Classical.choose (PackedPBSMonomialProduct.reached_product length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial (before,some ntts) product supported) := Option.some.inj reached.1
  exact same ▸ reached.2.1

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported in
/-- The product runs at the retained NTT's actual memory and entire state. -/
theorem productExecuted : product ∈ support (AmbientPublicZeroCheck.witness first.heights (MonomialPublicZeroCheck.stage firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy ntts.2) := by
  have reached := Classical.choose_spec (PackedPBSMonomialProduct.reached_product length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial (before,some ntts) product supported)
  have same : ntts = Classical.choose (PackedPBSMonomialProduct.reached_product length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial (before,some ntts) product supported) := Option.some.inj reached.1
  exact same ▸ reached.2.2.2

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported in
/-- Factor the same supported execution into its complete native monomial
component at the actual accumulator return; no component is replayed. -/
theorem componentExecuted : (ntts,some product) ∈ support (AmbientMonomialProduct.witness firstSmall roundSmall zeroNodesEnough hs.encoding (Nat.pow_add 2 cells lanes).symm psi primitive rotations (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase zeroBase first.heights dummy (PackedPBSAccumulatorMonomialSources.accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)).2.1.2.memory (PackedPBSAccumulatorMonomialSources.accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)).2.2) := by
  have head := PackedPBSAccumulatorMonomialSources.nttExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)
  have tail := productExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported
  change (ntts,some product) ∈ support (do
    let actual ← AmbientMonomialNTT.witness hs.encoding (Nat.pow_add 2 cells lanes).symm psi primitive
      (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase first.heights dummy
      (PackedPBSAccumulatorMonomialSources.accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)).2.1.2.memory (PackedPBSAccumulatorMonomialSources.accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)).2.2
    AmbientMonomialProduct.finish firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots zeroBase first.heights dummy actual)
  rw [support_bind]
  refine Set.mem_iUnion.mpr ⟨ntts,Set.mem_iUnion.mpr ⟨head,?_⟩⟩
  simp only [AmbientMonomialProduct.finish,nttAccepted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff]
  exact ⟨product,tail,rfl⟩

/-- The original accumulator tables, constructed from this reached prefix. -/
def accumulatorTables (capacity : 2^accSuffix ≤ accM*(2^lanes)) (radius : ℕ) :=
  PackedPBSAccumulatorMonomialSources.accumulatorTables length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) capacity radius

/-- Metadata of the selected original coefficient decoder. -/
def coefficientParameters (capacity : 2^monoSuffix ≤ monoM*(2^lanes)) (radius : Bool → ℕ)
    (geometry : ∀ side incoming, first.heights ((monoBase side incoming).tag false) = monoHeight) (side : Bool) :=
  PackedPBSAccumulatorMonomialSources.nttParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) (nttAccepted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) capacity radius geometry side

/-- Metadata of the corresponding actual original accumulator input/product. -/
def accumulatorParameters (capacity : 2^accSuffix ≤ accM*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((PackedPBSAccumulatorMonomialSources.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)).tag factor) = accHeight)
    (side : Bool) :=
  PackedPBSAccumulatorMonomialSources.accumulatorParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) capacity radius geometry side

/-- Metadata of the selected original evaluation decoder. -/
def evaluationParameters (capacity : 2^monoSuffix ≤ monoM*(2^lanes)) (radius : Bool → ℕ)
    (geometry : ∀ side incoming, first.heights ((monoBase side incoming).tag true) = monoHeight) (side : Bool) :=
  MonomialSourceAssociation.nttParameters firstSmall roundSmall zeroNodesEnough hs.encoding psi primitive rotations (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase zeroBase first.heights dummy (PackedPBSAccumulatorMonomialSources.accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)).2.1.2.memory (PackedPBSAccumulatorMonomialSources.accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)).2.2 ntts product (componentExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) capacity radius geometry side

/-- Metadata of the product's actual private evaluation decoder. -/
def productParameters (capacity : 2^zeroSuffix ≤ zeroM*(2^lanes)) (radius : ℕ)
    (geometry : ∀ incoming factor, first.heights ((zeroBase incoming).tag factor) = zeroHeight) (side : Bool) :=
  MonomialSourceAssociation.productParameters (zeroBase := zeroBase) (heights := first.heights) (before := ntts)
    capacity radius geometry side

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported in
/-- Every actual accumulator input/product row satisfies its rotation outside
the already bounded native monomial risk families and the same final exception.
Both sets of source associations concern public physical-decoder metadata. -/
theorem all_rotations_or_risks
    (monoCapacity : 2^monoSuffix ≤ monoM*(2^lanes)) (monoRadius : Bool → ℕ)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (zeroCapacity : 2^zeroSuffix ≤ zeroM*(2^lanes)) (zeroRadius : ℕ)
    (monoGeometry : ∀ side incoming source, first.heights ((monoBase side incoming).tag source) = monoHeight)
    (accGeometry : ∀ factor, first.heights ((PackedPBSAccumulatorMonomialSources.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)).tag factor) = accHeight)
    (zeroGeometry : ∀ incoming factor, first.heights ((zeroBase incoming).tag factor) = zeroHeight)
    (coefficientAssociated : ∀ side,
      coefficientParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported monoCapacity monoRadius (fun side incoming => monoGeometry side incoming false) side =
      accumulatorParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported accCapacity accRadius accGeometry side)
    (evaluationAssociated : ∀ side,
      evaluationParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported monoCapacity monoRadius (fun side incoming => monoGeometry side incoming true) side =
      productParameters (zeroBase := zeroBase) (first := first) (ntts := ntts) zeroCapacity zeroRadius zeroGeometry side)
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (productPassed : AmbientPublicZeroCheck.accepted product.2.1 = true) :
    (∀ (position : Fin (2^rows)) (active : position.val < rounds) (half : Bool),
      DecodedAccumulatorRows.decode (accumulatorTables length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported accCapacity accRadius 1) position half =
        NativeBlindRotation.rotate (rotations ⟨position.val,active⟩).val
          (DecodedAccumulatorRows.decode (accumulatorTables length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported accCapacity accRadius 0) position half)) ∨
    AmbientNTTSequenceSoundness.AnyOriginalRisk
      (AmbientMonomialNTT.factory hs.encoding (Nat.pow_add 2 cells lanes).symm psi primitive
        (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase)
      first.heights dummy monoCapacity monoRadius ntts.1 ∨
    AmbientPublicZeroCheck.OriginalRisk first.heights (MonomialPublicZeroCheck.stage firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy zeroCapacity zeroRadius product ∨
    CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) product.2.2 := by
  have finalAudited := PackedPBSMonomialProduct.audited_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory (Nat.pow_add 2 cells lanes).symm evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase initial compatible restricted audited
    ((before,some ntts),some product) supported
  change CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) product.2.2 at finalAudited
  have retained : CheckpointHistoryChain.Retains ntts.2 product.2.2 := by
    intro tag owner recorded
    exact AmbientPublicZeroCheck.retains first.heights (MonomialPublicZeroCheck.stage firstSmall roundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy ntts.2 product (productExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) tag owner recorded
  have coefficientRows := PackedPBSAccumulatorMonomialSources.coefficient_rows_eq_or_bad length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) (nttAccepted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)
    monoCapacity monoRadius accCapacity accRadius (fun side incoming => monoGeometry side incoming false) accGeometry coefficientAssociated
    product.2.2 retained finalAudited
  rcases coefficientRows with sameRows | failed
  · have incoming := PackedPBSAccumulator.audited_witness length psi primitive family inputs base hs nodesEnough radix linearBase
      dummy first second secondBase accumulators factory initial compatible restricted audited (before.1,some (PackedPBSAccumulatorMonomialSources.accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)))
      (PackedPBSAccumulatorMonomialSources.accumulatorSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported))
    change CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) (PackedPBSAccumulatorMonomialSources.accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)).2.2 at incoming
    have covered := MonomialSourceAssociation.all_rotations_or_risks firstSmall roundSmall zeroNodesEnough hs.encoding psi primitive rotations (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase zeroBase first.heights dummy (PackedPBSAccumulatorMonomialSources.accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)).2.1.2.memory (PackedPBSAccumulatorMonomialSources.accumulatorChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)).2.2 ntts product (componentExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported)
      monoCapacity monoRadius zeroCapacity zeroRadius (fun side incoming => monoGeometry side incoming true) zeroGeometry
      evaluationAssociated incoming productPassed
    rcases covered with rotated | nttRisk | productRisk | failed
    · left
      intro position active half
      have output := sameRows true position half
      have input := sameRows false position half
      change PackedMonomialRotation.polynomial
        (PackedPBSAccumulatorMonomialSources.nttSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) (nttAccepted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) monoCapacity monoRadius true false) position half =
        DecodedAccumulatorRows.decode (accumulatorTables length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported accCapacity accRadius 1) position half at output
      change PackedMonomialRotation.polynomial
        (PackedPBSAccumulatorMonomialSources.nttSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts (prefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) (nttAccepted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported) monoCapacity monoRadius false false) position half =
        DecodedAccumulatorRows.decode (accumulatorTables length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory evaluations monoBase initial before ntts firstSmall roundSmall zeroNodesEnough rotations zeroBase product supported accCapacity accRadius 0) position half at input
      rw [← output,← input]
      exact rotated position active half
    · exact Or.inr (Or.inl nttRisk)
    · exact Or.inr (Or.inr (Or.inl productRisk))
    · exact Or.inr (Or.inr (Or.inr failed))
  · exact Or.inr (Or.inr (Or.inr failed))

end
end FormalProof4FHE.HasteBoots.PackedPBSAccumulatorRotationCoverage
